;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "In-memory semantic model populated by the compiler's analysis sink.

  Captures var/local/keyword/class usages and definitions, macro compile-time
  dependency edges, and (from live namespace state) unused require/import/refer
  - across namespaces, with precise source spans.

  Provenance is per top-level form: every fact is filed under the form that
  produced it, so re-analysing one form (or one namespace) retracts exactly its
  prior facts and installs the new ones, without disturbing the rest of the
  model (design §7). Drivers: run-analysis / load-ns! (cold or single-ns) and
  eval-form! (single-form). Query with find-usages, definition, unused-*, etc.

  See doc/analysis-and-reload.md for the full design."
      :author "replique-clj"}
    clojure.analysis
  (:require [clojure.java.io :as io])
  (:import [clojure.lang IAnalysisSink Compiler Var LineNumberingPushbackReader]
           [java.io StringReader]))

;; model keys:
;;   :usages          {var   #{span}}       span = {:source :line :column :end-line :end-column :from-ns}
;;   :defs            {var   span}
;;   :locals          {binding {:ns :name ...span :uses #{span}}}
;;   :keyword-usages  {kw    #{span}}
;;   :class-usages    {class #{span}}
;;   :macro-deps      {ns-sym {macro-var #{fid}}}   compile-time edges (§9)
;; provenance:
;;   :forms           {fid {:ns :source :line :column :defines #{var} :facts [instr]}}
;;   :entity->form    {var fid}     the form that currently defines each var
;;   :ns->forms       {ns-sym #{fid}}
;;   :next-fid        long          global unique-id source for forms (shared)
(def ^:private empty-model
  {:usages {} :defs {} :locals {} :keyword-usages {} :class-usages {} :macro-deps {}
   :forms {} :entity->form {} :ns->forms {} :next-fid 0
   :ns-mtime {}})  ; ns-sym -> source file last-modified time, for staleness (§9)

(defonce ^:private model (atom empty-model))

;; The stack of active (nested) top-level forms is per-thread, not part of the
;; shared model: with-sink binds it to a fresh atom for each analysis. This keeps
;; "which form am I inside" thread-local (matching the thread-local sink binding),
;; so concurrent analyses on different threads cannot stamp facts with each other's
;; form ids. Only the recorded facts - and :next-fid, the global id source - live
;; in the shared model. nil when no analysis is in flight; current-fid then yields
;; nil and facts are simply recorded without provenance.
(def ^:private ^:dynamic *form-stack* nil)

(defn- span [source line column end-line end-column]
  (cond-> {:source source :line line :column column}
    (nat-int? end-line)   (assoc :end-line end-line)
    (nat-int? end-column) (assoc :end-column end-column)))

(defn- current-fid [] (when-let [s *form-stack*] (peek @s)))

(defn- add-fact [m fid instr]
  (if fid (update-in m [:forms fid :facts] conj instr) m))

(defn- record-usage [m idx target sp fid]
  (-> m
      (update-in [idx target] (fnil conj #{}) sp)
      (add-fact fid [idx target sp])))

;; --- retraction ------------------------------------------------------------

(defn- drop-empty [m idx k]
  (if (empty? (get-in m [idx k])) (update m idx dissoc k) m))

(defn- retract-instr [m [op a b c]]
  (case op
    :usages         (-> m (update-in [:usages a] disj b) (drop-empty :usages a))
    :keyword-usages (-> m (update-in [:keyword-usages a] disj b) (drop-empty :keyword-usages a))
    :class-usages   (-> m (update-in [:class-usages a] disj b) (drop-empty :class-usages a))
    :defs           (update m :defs dissoc a)
    :locals         (update m :locals dissoc a)
    :local-use      (cond-> m (get-in m [:locals a]) (update-in [:locals a :uses] disj b))
    :macro-dep      (let [m (update-in m [:macro-deps a b] disj c)]
                      (if (empty? (get-in m [:macro-deps a b]))
                        (let [m (update-in m [:macro-deps a] dissoc b)]
                          (if (empty? (get-in m [:macro-deps a])) (update m :macro-deps dissoc a) m))
                        m))
    m))

(defn- retract-form [m fid]
  (if-let [fe (get-in m [:forms fid])]
    (let [m (reduce retract-instr m (:facts fe))
          m (update m :forms dissoc fid)
          m (update m :entity->form
                    (fn [e] (reduce (fn [e v] (if (= (get e v) fid) (dissoc e v) e)) e (:defines fe))))]
      (if-let [owner (:ns fe)]
        (-> m (update-in [:ns->forms owner] disj fid) (drop-empty :ns->forms owner))
        m))
    m))

;; --- model mutators (called by the sink and by drivers) --------------------

(defn- begin-form! [source line column]
  ;; Allocate a globally-unique fid from the shared model, then push it on this
  ;; thread's form stack. The fid used is (dec :next-fid) after the atomic bump.
  (let [m'  (swap! model
                   (fn [m]
                     (let [fid (:next-fid m)]
                       (-> m
                           (update :next-fid inc)
                           (assoc-in [:forms fid] {:source source :line line :column column
                                                   :defines #{} :facts []})))))
        fid (dec (:next-fid m'))]
    (when *form-stack* (swap! *form-stack* conj fid)))
  nil)

(defn- end-form! []
  (let [fid (current-fid)]
    (when *form-stack* (swap! *form-stack* pop))
    (when fid
      (swap! model
             (fn [m]
               (let [fe (get-in m [:forms fid])]
                 (if (and (empty? (:facts fe)) (empty? (:defines fe)))
                   (update m :forms dissoc fid)          ; drop empty forms (e.g. outer do, EOF)
                   (let [owner (some-> *ns* ns-name)]
                     (-> m
                         (assoc-in [:forms fid :ns] owner)
                         (update-in [:ns->forms owner] (fnil conj #{}) fid)))))))))
  nil)

;; Invariant: a fact is recorded ONLY when a form is open (current-fid non-nil).
;; Without a form there is nowhere to file the fact's undo-record, so it could
;; never be retracted (a ghost in the index) - and for defs it would even write a
;; bogus [:forms nil] entry. So every sink method is a no-op when no form is open.
;; This never drops anything real: load / require / eval-form! always open a form;
;; only a bare eval outside a form window (an unsupported use of run-analysis)
;; would land here, and that was never retractable anyway.
(deftype AnalysisSink []
  IAnalysisSink
  (beginForm [_ source line column] (begin-form! source line column))
  (endForm [_] (end-form!))
  (varUsage [_ target from-ns source line column el ec]
    (when-let [fid (current-fid)]
      (swap! model (fn [m]
                     (record-usage m :usages target
                                   (assoc (span source line column el ec) :from-ns from-ns)
                                   fid))))
    nil)
  (varDef [_ v source line column el ec]
    (when-let [fid (current-fid)]
      (swap! model (fn [m]
                     (let [old (get-in m [:entity->form v])
                           m   (if (and old (not= old fid)) (retract-form m old) m)]
                       (-> m
                           (assoc-in [:defs v] (span source line column el ec))
                           (assoc-in [:entity->form v] fid)
                           (update-in [:forms fid :defines] (fnil conj #{}) v)
                           (add-fact fid [:defs v]))))))
    nil)
  (localDef [_ binding name ns source line column el ec]
    (when-let [fid (current-fid)]
      (swap! model (fn [m]
                     (-> m
                         (update-in [:locals binding]
                                    (fn [cur] (merge (span source line column el ec)
                                                     {:ns ns :name name :uses (get cur :uses #{})})))
                         (add-fact fid [:locals binding])))))
    nil)
  (localUsage [_ binding ns source line column el ec]
    (when-let [fid (current-fid)]
      (let [sp (assoc (span source line column el ec) :ns ns)]
        (swap! model (fn [m]
                       (-> m
                           (update-in [:locals binding :uses] (fnil conj #{}) sp)
                           (add-fact fid [:local-use binding sp]))))))
    nil)
  (keywordUsage [_ kw from-ns source line column el ec]
    (when-let [fid (current-fid)]
      (swap! model (fn [m]
                     (record-usage m :keyword-usages kw
                                   (assoc (span source line column el ec) :from-ns from-ns)
                                   fid))))
    nil)
  (classUsage [_ c from-ns source line column el ec]
    (when-let [fid (current-fid)]
      (swap! model (fn [m]
                     (record-usage m :class-usages c
                                   (assoc (span source line column el ec) :from-ns from-ns)
                                   fid))))
    nil)
  (macroExpansion [_ macro from-ns source line column el ec record-usage?]
    (when-let [fid (current-fid)]
     (swap! model (fn [m]
                   (let [ns-sym (ns-name from-ns)
                         ;; Always record the compile-time edge (stale reload needs
                         ;; it even for expansion-introduced calls); record the
                         ;; macro *usage* only for a source-written call.
                         m      (-> m
                                    (update-in [:macro-deps ns-sym macro] (fnil conj #{}) fid)
                                    (add-fact fid [:macro-dep ns-sym macro fid]))]
                     (if record-usage?
                       (record-usage m :usages macro
                                     (assoc (span source line column el ec) :from-ns from-ns :macro true)
                                     fid)
                       m))))
    nil)))

;; --- drivers ---------------------------------------------------------------

(defn reset-model!
  "Clear the whole model (cold-load driver: start from empty, design §8)."
  []
  (reset! model empty-model))

(defn- with-sink [thunk]
  ;; Bind the sink and a fresh per-thread form stack together, for the same
  ;; dynamic extent: every form begin/end and fact recorded on this thread
  ;; during the analysis uses this thread's own stack.
  (push-thread-bindings {Compiler/ANALYSIS_SINK (->AnalysisSink)
                         #'*form-stack*         (atom [])})
  (try (thunk) (finally (pop-thread-bindings))))

(declare record-ns-mtime!)

(defn run-analysis
  "Invoke thunk with the analysis sink installed on this thread, so any
  compilation it triggers (load / require / eval) populates the model,
  form by form. Returns the thunk's value.

  Also records the source mtime of every namespace this run (re)compiled, so the
  run establishes its own staleness baseline. Without it a cold analysis leaves
  every namespace with a nil baseline, and the next `changed-namespaces` would
  report them all as changed (nil baseline != current mtime), making the first
  `stale-reload!` re-evaluate the whole codebase. Only namespaces actually
  touched this run are snapshotted (their :ns->forms changed); baselines for
  untouched namespaces - e.g. ones edited but not yet reloaded - are left intact,
  so a pending staleness flag elsewhere is not silently cleared."
  [thunk]
  (let [before (:ns->forms @model)
        result (with-sink thunk)]
    (doseq [ns-sym (keys (:ns->forms @model))
            :when (not= (get before ns-sym) (get-in @model [:ns->forms ns-sym]))]
      (record-ns-mtime! ns-sym))
    result))

(defn retract-ns!
  "Remove every fact produced by ns-sym's forms from the model, preserving all
  other namespaces' references to its vars (design §8, single-ns replace)."
  [ns-sym]
  (swap! model (fn [m] (reduce retract-form m (get-in m [:ns->forms ns-sym]))))
  nil)

(defn- ns->source-path [ns-sym]
  (str (.. (name ns-sym) (replace \- \_) (replace \. \/)) ".clj"))

(defn- resource->file
  "The File a file: resource URL points at. Prefer URL.toURI (which decodes %20
  and friends), but classloaders sometimes hand back URLs with un-encoded
  characters - most commonly a literal space in a path like /Users/x/My
  Project/... - which toURI rejects with URISyntaxException. Fall back to the raw
  path in that case (where the space is already literal, so File is correct)
  instead of letting the exception abort the whole reload."
  [^java.net.URL u]
  (try
    (java.io.File. (.toURI u))
    (catch java.net.URISyntaxException _
      (java.io.File. (.getPath u)))))

(defn- ns-source-mtime [ns-sym]
  (when-let [u (io/resource (ns->source-path ns-sym))]
    (when (= "file" (.getProtocol u))
      (.lastModified (resource->file u)))))

(defn- record-ns-mtime! [ns-sym]
  (swap! model assoc-in [:ns-mtime ns-sym] (ns-source-mtime ns-sym))
  nil)

(defn snapshot-mtimes!
  "Record the current source-file modification time of every analysed namespace,
  so later staleness checks have a reference point. `run-analysis` already
  baselines the namespaces it compiles, so this is not needed after a plain cold
  analysis; use it to force-rebaseline the entire model (e.g. to deliberately
  clear all pending staleness flags at once)."
  []
  (doseq [ns-sym (keys (:ns->forms @model))] (record-ns-mtime! ns-sym))
  nil)

(defn load-ns!
  "Single-namespace analysis (design §8): retract ns-sym's prior forms, then
  reload the namespace under the sink so the model is replaced cleanly. Removes
  defs deleted from source and stale non-def forms that retract-on-redefine
  alone would miss. Refreshes the stored source mtime."
  [ns-sym]
  (retract-ns! ns-sym)
  (run-analysis #(require ns-sym :reload))
  (record-ns-mtime! ns-sym))

(defn- retract-forms-at
  "Retract any previously-analysed top-level form recorded at exactly this source
  position. Re-evaluating an edited form thus replaces its facts instead of
  leaving the old version's behind. The varDef retract-on-redefine tap only
  covers forms that (re)define a var - a non-def form (defmethod, a registry
  swap!, a bare call) has no var identity to key on, so without this its old
  usages/keyword/class facts would accumulate as phantoms. Matching is by
  (source, line, column); a form whose start position shifted is not caught here
  (its var defs are still handled by entity->form; for non-defs, prefer load-ns!
  when positions move)."
  [m source line column]
  (reduce retract-form m
          (vec (for [[fid fe] (:forms m)
                     :when (and (= source (:source fe))
                                (= line (:line fe))
                                (= column (:column fe)))]
                 fid))))

(defn eval-form!
  "Single-form analysis (design §8, finest scope). Reads one top-level form from
  form-str positioned at file/line/column, evaluates it in ns-sym under the sink,
  and updates the model for just that form. Any prior form recorded at the same
  file/line/column is retracted first, so re-evaluating an edited form replaces
  its facts - both for defs (also covered by retract-on-redefine) and for non-def
  forms (which have no var to key retraction on). Returns the eval result.

  Caveat: the retraction unit is the whole form. Top-level (do ...) is NOT split
  here (unlike Compiler.load), so re-evaluating one def previously loaded inside a
  multi-def form (e.g. (do (def a) (def b))) retracts that form's siblings from
  the model - they stay interned at runtime but drop out of the index until
  re-analysed."
  [ns-sym file line column form-str]
  (let [rdr (doto (LineNumberingPushbackReader. (StringReader. form-str))
              (.setLineNumber (int line))
              (.setColumnNumber (int column)))]
    (with-sink
      (fn []
        (push-thread-bindings {Compiler/SOURCE_PATH file
                               Compiler/SOURCE      file
                               (var *ns*)           (the-ns ns-sym)})
        (try
          (swap! model retract-forms-at file line column)
          (begin-form! file line column)
          (try
            (let [form (read {:eof ::eof} rdr)]
              (when-not (= form ::eof)
                (clojure.core/eval form)))
            (finally (end-form!)))
          (finally (pop-thread-bindings)))))))

;; --- queries ---------------------------------------------------------------

(defn find-usages
  "Usage sites recorded for var v: a set of spans
  {:from-ns :source :line :column :end-line :end-column [:macro]}."
  [^Var v]
  (get-in @model [:usages v]))

(defn definition
  "Definition site recorded for var v: a span, or nil."
  [^Var v]
  (get-in @model [:defs v]))

(defn find-keyword-usages
  "Occurrence sites recorded for keyword kw. Auto-resolved keywords are indexed
  fully-qualified, so pass e.g. (keyword \"my.ns\" \"x\")."
  [kw]
  (get-in @model [:keyword-usages kw]))

(defn find-class-usages
  "Occurrence sites recorded for class c (a java.lang.Class)."
  [c]
  (get-in @model [:class-usages c]))

(defn macro-deps
  "Compile-time macro dependency edges. No arg: {ns-sym #{macro-var}}. With a
  namespace symbol: the set of macro vars it expanded (design §9)."
  ([] (reduce-kv (fn [acc ns mm] (assoc acc ns (set (keys mm)))) {} (:macro-deps @model)))
  ([ns-sym] (set (keys (get-in @model [:macro-deps ns-sym])))))

(defn unused-locals
  "Source-written local bindings with no recorded reference. Optionally restrict
  to a namespace. Each result is the binding's def site plus :name and :ns."
  ([] (unused-locals nil))
  ([ns-sym]
   (for [[_ info] (:locals @model)
         :when (empty? (:uses info))
         :when (or (nil? ns-sym) (= ns-sym (ns-name (:ns info))))]
     (dissoc info :uses))))

;; --- requires / imports (read from live namespace state, design §4) --------

;; The default java.lang.* auto-imports every namespace gets for free. A fresh
;; empty namespace has exactly these, so we read them off one - but only ONCE
;; (cached in a delay) and with the throwaway namespace removed afterwards, so
;; repeated unused-imports calls do not grow the global namespace registry.
(def ^:private default-imports
  (delay
    (let [n (gensym "clojure.analysis._blank")]
      (try (set (vals (ns-imports (create-ns n))))
           (finally (remove-ns n))))))

(defn ns-referenced-namespaces
  "Namespace-name symbols whose vars or namespaced keywords are referenced from
  ns-sym, per the model."
  [ns-sym]
  (let [m @model
        from? (fn [uses] (some #(= ns-sym (some-> (:from-ns %) ns-name)) uses))]
    (into #{}
          (concat
           (for [[^Var v uses] (:usages m) :when (from? uses)] (ns-name (.ns v)))
           (for [[kw uses] (:keyword-usages m)
                 :when (and (namespace kw) (from? uses))]
             (symbol (namespace kw)))))))

(defn unused-aliases
  "Aliases in ns-sym whose target namespace has no var or namespaced-keyword
  reference from ns-sym. Returns {alias ns-sym}."
  [ns-sym]
  (let [used (ns-referenced-namespaces ns-sym)]
    (into {} (for [[a ns] (ns-aliases ns-sym)
                   :when (not (contains? used (ns-name ns)))]
               [a (ns-name ns)]))))

(defn unused-refers
  "Non-core vars referred into ns-sym that are never used from it.
  Returns {referred-sym var}. clojure.core auto-refers are excluded."
  [ns-sym]
  (let [uses (:usages @model)
        core (the-ns 'clojure.core)
        used? (fn [v] (some #(= ns-sym (some-> (:from-ns %) ns-name)) (get uses v)))]
    (into {} (for [[sym ^Var v] (ns-refers ns-sym)
                   :when (and (not (identical? core (.ns v))) (not (used? v)))]
               [sym v]))))

(defn unused-imports
  "User-imported classes in ns-sym that are never referenced from it.
  Returns {imported-sym class}. java.lang.* auto-imports are excluded."
  [ns-sym]
  (let [defaults @default-imports
        used? (fn [c] (some #(= ns-sym (some-> (:from-ns %) ns-name)) (find-class-usages c)))]
    (into {} (for [[sym c] (ns-imports ns-sym)
                   :when (and (not (contains? defaults c)) (not (used? c)))]
               [sym c]))))

(defn ns-forms
  "The fids currently attributed to ns-sym (for inspection/tests)."
  [ns-sym]
  (get-in @model [:ns->forms ns-sym] #{}))

;; --- stale reload + prune (design §9) --------------------------------------

(defn changed-namespaces
  "Analysed namespaces whose source-file modification time differs from the
  recorded baseline (edited since last analysis/reload). Namespaces whose source
  can no longer be resolved to a file (mtime nil - moved, deleted, or now behind
  a jar) are skipped: reloading them would only fail, so they are not flagged."
  []
  (let [m @model]
    (set (for [ns-sym (keys (:ns->forms m))
               :let [now (ns-source-mtime ns-sym)]
               :when (and (some? now)
                          (not= now (get-in m [:ns-mtime ns-sym])))]
           ns-sym))))

(defn- macro-owner [^Var mv] (ns-name (.ns mv)))

(defn- reverse-macro-graph
  "macro-defining-ns -> #{namespaces that expand a macro from it}."
  [m]
  (reduce (fn [acc [n mm]]
            (reduce (fn [acc mv] (update acc (macro-owner mv) (fnil conj #{}) n))
                    acc (keys mm)))
          {} (:macro-deps m)))

(defn stale-namespaces
  "The set of namespaces to reload: every namespace whose source was edited since
  last loaded (the seed), plus every namespace that transitively compile-time-
  depends on the seed through the macro graph (design §9). Runtime-only
  (function-call) dependents are excluded - a plain var re-resolves at runtime and
  needs no recompile; only macro dependents do. This is a conservative macro-aware
  closure: any edit to a macro-defining file marks its macro-dependents stale
  (it does not distinguish which specific form in the file changed)."
  ([] (stale-namespaces (changed-namespaces)))
  ([seed]
   (let [rev (reverse-macro-graph @model)]
     (loop [dirty (set seed), queue (vec seed)]
       (if-let [x (peek queue)]
         (let [fresh (remove dirty (get rev x))]
           (recur (into dirty fresh) (into (pop queue) fresh)))
         dirty)))))

(defn- macro-dep-nses
  "Namespaces defining macros that ns-sym expands (its compile-time deps)."
  [m ns-sym]
  (set (map macro-owner (keys (get-in m [:macro-deps ns-sym])))))

(defn- topo-order
  "Order nses so each namespace's macro-dependency namespaces come first.
  Cycles are broken arbitrarily (remaining nodes appended)."
  [nses dep-fn]
  (let [nodes (set nses)]
    (loop [order [], placed #{}, remaining nodes]
      (if (empty? remaining)
        order
        (let [ready (filter (fn [n] (every? #(or (placed %) (not (nodes %))) (dep-fn n)))
                            remaining)]
          (if (empty? ready)
            (into order remaining)
            (recur (into order ready) (into placed ready) (reduce disj remaining ready))))))))

(defn ns-def-vars
  "The vars the model currently records a `def` form for in ns-sym. This is the
  set `:defs` restricts to one namespace, and it is exactly the population
  prune-ns! is allowed to consider: only vars the compiler saw defined by a
  top-level def can be judged 'deleted from source' by their disappearance."
  [m ns-sym]
  (let [the-ns* (the-ns ns-sym)]
    (set (for [^Var v (keys (:defs m)) :when (identical? the-ns* (.ns v))] v))))

(defn prune-ns!
  "Remove vars whose defining `def` form vanished from source. `prior-defs` is
  the set of def-vars the model recorded for ns-sym *before* the reload that
  just ran (capture it with `ns-def-vars` immediately before `load-ns!`); a var
  is pruned when it was in `prior-defs`, is no longer in the freshly reloaded
  :defs, and is still interned under the same identity. Warns - but still unmaps
  - if a pruned var has recorded usages (design §9.3: reflective uses can't be
  seen, so warn-and-prune, don't block). Returns the pruned symbols.

  Gating on `prior-defs` (not `ns-interns` minus :defs) is deliberate: vars that
  were never recorded as a `def` are never candidates, so intern-created vars
  are left alone. In particular a `defprotocol`'s method vars (created by
  `intern`, never a DefExpr - see core_deftype.clj) are never in :defs and so
  are never pruned; the cost is that a genuinely *deleted* protocol method (or a
  deleted `defonce`, which :reload also does not re-def) leaks a stale interned
  var until a cold reanalysis. That is the safe direction: never unmap a live
  protocol method and break its dispatch.

  PRECONDITION: only valid immediately after `load-ns!` of ns-sym (which
  `stale-reload!` does), so :defs has just been fully repopulated. Refuses to run
  on a namespace the model has never analysed (no forms in :ns->forms), turning
  misuse into a loud error instead of silent data loss."
  [ns-sym prior-defs]
  (when-not (seq (get-in @model [:ns->forms ns-sym]))
    (throw (ex-info (str "prune-ns! refused: " ns-sym " has no analysed forms in the model. "
                         "Run (load-ns! '" ns-sym ") first - prune is only valid right after "
                         "a full analysis, else it would unmap vars it simply never recorded.")
                    {:ns ns-sym})))
  (let [live (ns-def-vars @model ns-sym)
        interned (set (vals (ns-interns ns-sym)))
        gone (filter (fn [^Var v] (and (contains? interned v) (not (contains? live v))))
                     prior-defs)]
    (doseq [^Var v gone]
      (when-let [us (seq (find-usages v))]
        (binding [*out* *err*]
          (println "WARN: pruning" (str v) "still referenced at"
                   (vec (for [s us] [(some-> (:from-ns s) ns-name) (:line s) (:column s)])))))
      (ns-unmap ns-sym (.sym v))
      (swap! model (fn [m] (-> m (update :usages dissoc v)
                               (update :defs dissoc v)
                               (update :entity->form dissoc v)))))
    (mapv #(.sym ^Var %) gone)))

(defn- topo-respected?
  "True when `order` already loads every namespace after all its macro-deps
  (per dep-fn). Deps outside `order` are ignored - they were not reloaded, so
  they are already current."
  [order dep-fn]
  (let [idx (zipmap order (range))]
    (every? (fn [x] (every? (fn [y] (or (nil? (idx y)) (< (idx y) (idx x))))
                            (dep-fn x)))
            order)))

(defn stale-reload!
  "Macro-aware stale reload (design §9.2). Computes the stale set (changed
  namespaces + their transitive macro-dependents), reloads each via load-ns! in
  macro-dependency order (macro definers before their users, which then re-expand
  the new macros), and optionally prunes vanished vars (:prune true). Returns the
  final reload order.

  Two-pass, to handle a macro dependency introduced by the very edit being
  reloaded (design §9.2). The first-pass order comes from the pre-reload macro
  graph, which cannot yet know an edge that only this edit adds (e.g. ns A newly
  requires and expands ns B's macro): A could be ordered before B and expand B's
  stale macro. Pass 1 reloads in that best-guess order, which recompiles every
  edited file and so completes the macro graph. We then recompute the order from
  the now-complete graph; if pass 1 already respected it (the common case - no
  new cross-ns macro edge) we are done at no extra cost, otherwise a namespace
  expanded a stale macro and we reload once more in the corrected order. Two
  passes always suffice: after pass 1 the on-disk source is fixed and every
  edited file has been analysed, so the recomputed graph - and its order - is
  stable.

  Limitation: this repairs *stale* expansion (the macro exists but is the old
  version). An edit that calls a macro which did not exist in the dependency's
  old version can still make pass 1 error if misordered; ordering by the new
  requires would be needed for that, which this does not do."
  [& {:keys [prune]}]
  (let [reload! (fn [order]
                  (doseq [ns-sym order]
                    ;; Snapshot the ns's def-vars BEFORE load-ns! retracts them,
                    ;; so prune can tell which def forms vanished (see prune-ns!).
                    (let [prior (when prune (ns-def-vars @model ns-sym))]
                      (load-ns! ns-sym)
                      (when prune (prune-ns! ns-sym prior)))))
        stale  (stale-namespaces)
        order1 (topo-order stale #(macro-dep-nses @model %))]
    (reload! order1)
    ;; Pass 1 completed the macro graph; re-derive the order from it.
    (let [dep-fn  #(macro-dep-nses @model %)]
      (if (topo-respected? order1 dep-fn)
        order1
        (let [order2 (topo-order stale dep-fn)]
          (reload! order2)
          order2)))))

(defn snapshot
  "The whole model, for inspection/tests."
  []
  @model)
