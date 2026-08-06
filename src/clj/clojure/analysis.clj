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

;; Vars are keyed by their fully-qualified name symbol (my.ns/foo), not by Var
;; object identity: a var deleted and later redefined mints a NEW Var object, so
;; identity keys would strand a deleted var's references under a dead key and pin
;; the dead Var (and its root value) in memory. A name key is stable across that
;; churn, keeps a deleted-but-referenced var findable as a tombstone (:defs entry
;; with :removed true), and matches Clojure's late binding (callers re-resolve the
;; name). The sink receives resolved Var objects and converts them via var-key.
;; model keys:
;;   :usages          {qsym  #{span}}       qsym = fully-qualified var name (my.ns/foo)
;;                                          span = {:source :line :column :end-line :end-column :from-ns}
;;   :defs            {qsym  {:span span :removed bool}}
;;                                          :removed = def deleted from source but still
;;                                          referenced (a tombstone; dropped once its last
;;                                          usage disappears - see retract-instr)
;;   :locals          {binding {:ns :name ...span :uses #{span}}}
;;   :keyword-usages  {kw    #{span}}
;;   :class-usages    {class #{span}}
;;   :macro-deps      {ns-sym {macro-qsym #{fid}}}   compile-time edges (§9)
;; provenance:
;;   :forms           {fid {:ns :source :line :column :defines #{qsym} :facts [instr]}}
;;   :entity->form    {qsym fid}    the form that currently defines each var
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

;; When bound to an atom, begin-form! logs every fid it allocates here. load-ns!
;; uses this to roll back a failed reload precisely - retracting exactly the forms
;; that reload created (wherever endForm filed them) - instead of resetting the
;; whole shared model, which would clobber facts other threads committed meanwhile.
;; nil outside load-ns!, so ordinary analyses pay nothing for it.
(def ^:private ^:dynamic *created-fids* nil)

;; When bound to an atom (holding a set), retract-instr logs here every var whose
;; usage set it just emptied - the candidates for tombstone GC. A driver sweeps
;; ONLY these keys when its operation finishes (sweep-tombstones), instead of
;; scanning the whole :defs map. Being per-operation and thread-local, thread A
;; only ever sweeps tombstones A itself emptied, so it cannot GC a tombstone that
;; thread B's concurrent reload has transiently emptied mid-retract (design §7.3).
;; nil when no driver established it, so bare retract-form calls pay nothing.
(def ^:private ^:dynamic *emptied-tombstones* nil)

(defn- span [source line column end-line end-column]
  (cond-> {:source source :line line :column column}
    (nat-int? end-line)   (assoc :end-line end-line)
    (nat-int? end-column) (assoc :end-column end-column)))

(defn- var-key
  "Canonical model key for a var: its fully-qualified name symbol (my.ns/foo).
  Stable across ns-unmap+redef churn (a redefinition mints a new Var object under
  the same name), so a deleted var's references stay findable and no dead Var is
  pinned in the model. The sink only ever hands it resolved (interned) vars, but
  the public query API (find-usages / definition) may be passed an arbitrary var,
  including an uninterned one whose namespace is nil - return nil for those so a
  lookup simply misses (as it did pre-refactor) rather than throwing."
  [^Var v]
  (when-let [ns (.ns v)]
    (symbol (str (ns-name ns)) (str (.sym v)))))

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
    ;; When this drop empties a's usage set, note a as a tombstone-GC candidate for
    ;; the driver to sweep after re-analysis (see *emptied-tombstones* / sweep-
    ;; tombstones). The conj is a side effect inside a swap! fn, but idempotent - a
    ;; retried swap re-adds the same key to a set, and sweep re-checks emptiness
    ;; before dropping, so an extra candidate from a discarded attempt is harmless.
    :usages         (let [m (-> m (update-in [:usages a] disj b) (drop-empty :usages a))]
                      (when (and *emptied-tombstones* (nil? (get-in m [:usages a])))
                        (swap! *emptied-tombstones* conj a))
                      m)
    :keyword-usages (-> m (update-in [:keyword-usages a] disj b) (drop-empty :keyword-usages a))
    :class-usages   (-> m (update-in [:class-usages a] disj b) (drop-empty :class-usages a))
    ;; A def whose form is retracted (deleted from source) but that other forms
    ;; still reference becomes a tombstone, not a deletion, so tooling can flag the
    ;; now-dangling references; with no references left it is dropped outright. A
    ;; normal reload re-runs varDef right after, clearing :removed either way. The
    ;; tombstone is later GC'd by sweep-tombstones (NOT here, and NOT in the :usages
    ;; branch) - see that fn for why the collection must wait for a reload boundary.
    :defs           (if (seq (get-in m [:usages a]))
                      (assoc-in m [:defs a :removed] true)
                      (update m :defs dissoc a))
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

(defn- sweep-tombstones
  "GC the tombstones among `candidates` (var keys whose usage set was emptied this
  operation, collected in *emptied-tombstones*) whose last reference is now truly
  gone: drop each :defs entry that is still :removed and still has no usages.

  Runs at a reload boundary (after load-ns! / eval-form! / retract-ns! finishes),
  NOT inside retract-instr: a reload first retracts the namespace's old forms and
  only then re-analyses, so a var the reloaded namespace still references has its
  usage set transiently emptied mid-reload and re-filled moments later. GC-ing
  eagerly on that empty window would delete a cross-namespace tombstone that in
  fact survives the reload (the reference comes right back) - and, on a plain
  successful reload of the referencing namespace, strand the re-added usage under
  no :defs entry. Deferring to the stable end state, and re-checking emptiness
  here, avoids both. Sweeping only this operation's own candidates (not the whole
  :defs map) keeps it O(touched) and confines it to tombstones this thread emptied."
  [m candidates]
  (reduce (fn [m k]
            (if (and (get-in m [:defs k :removed]) (empty? (get-in m [:usages k])))
              (update m :defs dissoc k)
              m))
          m candidates))

;; The precise inverse of retract-instr/retract-form, used only by load-ns! to
;; roll back a failed reload: it re-adds one previously-retracted form (and its
;; facts) into the live model, without disturbing any other form. `snap` is the
;; pre-reload model the form is restored from; the two lossy instrs (:defs carries
;; only the qsym, :locals only the binding) recover their index value from it. For
;; :defs that value is the WHOLE entry {:span :removed}, so a def's tombstone state
;; round-trips with its span - restoring only the span could leave a var falsely
;; tombstoned (or falsely healthy) after rollback. Must mirror retract-instr
;; op-for-op - if you add a fact op there, add it here.
(defn- reinstate-instr [snap m [op a b c]]
  (case op
    :usages         (update-in m [:usages a] (fnil conj #{}) b)
    :keyword-usages (update-in m [:keyword-usages a] (fnil conj #{}) b)
    :class-usages   (update-in m [:class-usages a] (fnil conj #{}) b)
    :defs           (assoc-in m [:defs a] (get-in snap [:defs a]))
    :locals         (assoc-in m [:locals a] (get-in snap [:locals a]))
    :local-use      (cond-> m (get-in m [:locals a]) (update-in [:locals a :uses] (fnil conj #{}) b))
    :macro-dep      (update-in m [:macro-deps a b] (fnil conj #{}) c)
    m))

(defn- reinstate-form [m snap fid]
  (if-let [fe (get-in snap [:forms fid])]
    (let [m (assoc-in m [:forms fid] fe)
          m (reduce (partial reinstate-instr snap) m (:facts fe))
          m (reduce (fn [m v] (assoc-in m [:entity->form v] fid)) m (:defines fe))]
      (if-let [owner (:ns fe)]
        (update-in m [:ns->forms owner] (fnil conj #{}) fid)
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
    (when *form-stack* (swap! *form-stack* conj fid))
    (when *created-fids* (swap! *created-fids* conj fid)))
  nil)

(defn- form-start! [line column]
  ;; The reader reports the top-level form's true start once it commits to the
  ;; datum - past any leading whitespace, ; comment, #_ discard or non-selected
  ;; reader-conditional branch that beginForm's pre-scan could not skip. Correct
  ;; the open form's position so retract-forms-at / eval-form! key on the form
  ;; itself, not the junk before it.
  ;; The reader fires formStart once per skipped leading no-op (each ; line, each
  ;; #_), then once for the datum - "last wins" gives the right position, so the
  ;; earlier calls are redundant swaps. Accepted: this is the analysis path, not a
  ;; hot loop, and the waste is bounded by a form's leading-comment count; avoiding
  ;; it would mean restructuring the reader's read() loop for no correctness gain.
  (when-let [fid (current-fid)]
    (swap! model update-in [:forms fid] #(assoc % :line line :column column)))
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
  (formStart [_ line column] (form-start! line column))
  (endForm [_] (end-form!))
  (varUsage [_ target from-ns source line column el ec]
    ;; when-let on the key, not let: var-key is nil only for a nil-ns var, which the
    ;; compiler should never resolve to here - but if one slips through, skip it
    ;; rather than write a nil key that would later NPE (namespace nil) in queries.
    (when-let [fid (current-fid)]
      (when-let [k (var-key target)]
        (swap! model (fn [m]
                       (record-usage m :usages k
                                     (assoc (span source line column el ec) :from-ns from-ns)
                                     fid)))))
    nil)
  (varDef [_ v source line column el ec]
    (when-let [fid (current-fid)]
      (when-let [k (var-key v)]
        (swap! model (fn [m]
                       (let [old (get-in m [:entity->form k])
                             m   (if (and old (not= old fid)) (retract-form m old) m)]
                         (-> m
                             ;; Fresh entry (no :removed): a (re)definition un-tombstones.
                             (assoc-in [:defs k] {:span (span source line column el ec)})
                             (assoc-in [:entity->form k] fid)
                             (update-in [:forms fid :defines] (fnil conj #{}) k)
                             (add-fact fid [:defs k])))))))
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
     (when-let [mk (var-key macro)]      ; skip a nil-ns macro var (see varUsage)
      (let [ns-sym (ns-name from-ns)]
       (swap! model (fn [m]
                     ;; Always record the compile-time edge (stale reload needs it
                     ;; even for expansion-introduced calls); record the macro
                     ;; *usage* only for a source-written call.
                     (let [m (-> m
                                 (update-in [:macro-deps ns-sym mk] (fnil conj #{}) fid)
                                 (add-fact fid [:macro-dep ns-sym mk fid]))]
                       (if record-usage?
                         (record-usage m :usages mk
                                       (assoc (span source line column el ec) :from-ns from-ns :macro true)
                                       fid)
                         m)))))
    nil))))

;; --- drivers ---------------------------------------------------------------

(defn reset-model!
  "Clear the whole model (cold-load driver: start from empty, design §8)."
  []
  (reset! model empty-model))

(defn- with-sink [thunk]
  ;; Bind the sink and a fresh per-thread form stack together, for the same
  ;; dynamic extent: every form begin/end and fact recorded on this thread during
  ;; the analysis uses this thread's own stack. *created-fids* is deliberately NOT
  ;; bound here: begin-form! nil-guards it, so an ordinary analysis leaves it nil
  ;; and pays nothing; when a caller (load-ns!) has established it, this inherits
  ;; that binding so the caller sees every fid this analysis allocates, for rollback.
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
  ;; Own a tombstone-candidate set unless a driver (load-ns!) already established
  ;; one, in which case inherit it so that driver does the single post-op sweep.
  (let [own?   (nil? *emptied-tombstones*)
        before (:ns->forms @model)]
    (binding [*emptied-tombstones* (or *emptied-tombstones* (atom #{}))]
      (let [result (with-sink thunk)]
        (doseq [ns-sym (keys (:ns->forms @model))
                :when (not= (get before ns-sym) (get-in @model [:ns->forms ns-sym]))]
          (record-ns-mtime! ns-sym))
        (when own? (swap! model sweep-tombstones @*emptied-tombstones*))
        result))))

(defn- retract-ns*
  "Remove every fact produced by ns-sym's forms from the model, preserving all
  other namespaces' references to its vars (design §8, single-ns replace). Records
  emptied tombstone candidates but does NOT sweep - the caller does, after any
  re-analysis (load-ns!), or immediately (retract-ns!)."
  [ns-sym]
  (swap! model (fn [m] (reduce retract-form m (get-in m [:ns->forms ns-sym]))))
  nil)

(defn retract-ns!
  "Remove every fact produced by ns-sym's forms from the model, preserving all
  other namespaces' references to its vars (design §8, single-ns replace). GCs any
  tombstone whose last reference this retract removed (e.g. retracting the one
  namespace that still referenced a deleted-but-referenced var)."
  [ns-sym]
  (binding [*emptied-tombstones* (atom #{})]
    (retract-ns* ns-sym)
    (swap! model sweep-tombstones @*emptied-tombstones*))
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
  alone would miss. Refreshes the stored source mtime.

  Atomic: retract + reload + mtime update either all take effect or, if the
  reload throws (typically an edited source with a compile/syntax error), none
  do - ns-sym is reverted to its prior state and the error re-thrown. Without the
  rollback a failed reload leaves ns-sym's facts retracted but never replaced, so
  every var in the namespace (even ones that still compile) drops out of the index.

  The rollback reverts ONLY ns-sym, via swap!: it retracts this reload's created
  forms that belong to ns-sym and reinstates ns-sym's prior forms from a pre-retract
  snapshot. It never reset!s the whole model, so facts other threads committed by
  concurrent analyses between the snapshot and the failure are preserved (design
  §7.3). It also leaves alone any *other* namespace this reload happened to load
  fresh (an edit adding `(require some-not-yet-loaded-ns)`): that namespace compiled
  successfully and its facts reflect the runtime, so retracting them would strand a
  loaded namespace with no model entry. Created fids are filtered by owning ns
  (endForm files every form under its namespace, even the one that threw).

  Limitation: assumes one namespace per source file (the Clojure norm). A file that
  defines a second `(ns other ...)` is only partially tracked - retract and rollback
  key on ns-sym, so `other`'s forms from the same file are neither replaced nor
  rolled back cleanly. Reload such a file with a cold reanalysis instead."
  [ns-sym]
  (let [snapshot @model
        old-fids (get-in snapshot [:ns->forms ns-sym])]
    ;; One candidate set spans the retract and the re-analysis (run-analysis
    ;; inherits it), so the single success-path sweep sees every var emptied by
    ;; either phase - and the failure path discards it, never GC-ing on rollback.
    (binding [*created-fids*       (atom [])
              *emptied-tombstones* (atom #{})]
      (try
        (retract-ns* ns-sym)
        (run-analysis #(require ns-sym :reload))
        (swap! model sweep-tombstones @*emptied-tombstones*)
        (record-ns-mtime! ns-sym)
        (catch Throwable t
          (swap! model
                 (fn [m]
                   (let [mine (filter #(= ns-sym (get-in m [:forms % :ns])) @*created-fids*)
                         m    (reduce retract-form m mine)]
                     (reduce (fn [m fid] (reinstate-form m snapshot fid)) m old-fids))))
          (throw t))))))

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
    (binding [*emptied-tombstones* (atom #{})]
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
            ;; only on success; GC tombstones this form's retraction emptied
            (swap! model sweep-tombstones @*emptied-tombstones*)
            (finally (pop-thread-bindings))))))))

;; --- queries ---------------------------------------------------------------

(defn find-usages
  "Usage sites recorded for var v: a set of spans
  {:from-ns :source :line :column :end-line :end-column [:macro]}."
  [^Var v]
  (get-in @model [:usages (var-key v)]))

(defn definition
  "Definition site recorded for var v: a span, or nil. A tombstoned var (its def
  deleted from source but still referenced) is treated as undefined - returns nil,
  not the span the def used to occupy."
  [^Var v]
  (let [e (get-in @model [:defs (var-key v)])]
    (when-not (:removed e) (:span e))))

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
  "Compile-time macro dependency edges. No arg: {ns-sym #{macro-qsym}}. With a
  namespace symbol: the set of macro var names (qualified symbols) it expanded
  (design §9)."
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
           (for [[qsym uses] (:usages m)
                 :when (and (namespace qsym) (from? uses))]
             (symbol (namespace qsym)))
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
        used? (fn [^Var v] (some #(= ns-sym (some-> (:from-ns %) ns-name)) (get uses (var-key v))))]
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

(defn- macro-owner
  "The macro-defining namespace symbol for a macro key (a qualified symbol)."
  [macro-key] (symbol (namespace macro-key)))

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
  "The fully-qualified name symbols the model currently records a healthy `def`
  form for in ns-sym (tombstones - :removed defs - excluded). This is exactly the
  population prune-ns! is allowed to consider: only vars the compiler saw defined
  by a top-level def can be judged 'deleted from source' by their disappearance."
  [m ns-sym]
  (let [nsname (str (ns-name (the-ns ns-sym)))]
    (set (for [[k entry] (:defs m)
               :when (and (= nsname (namespace k)) (not (:removed entry)))]
           k))))

(defn ns-def-var-snapshot
  "Capture {qsym -> the currently-interned Var object} for ns-sym's healthy
  recorded defs. This is prune-ns!'s `prior`; take it *before* load-ns! so that,
  once vars are keyed by name (not identity), prune can still tell a lingering
  deleted-def var (the SAME Var object is still interned after :reload) from one
  the reloaded source deleted and re-created under a fresh identity via intern /
  unmap-then-reintern (which must be preserved, not unmapped)."
  [m ns-sym]
  (let [interned (ns-interns ns-sym)]
    (into {} (for [k (ns-def-vars m ns-sym)]
               [k (get interned (symbol (name k)))]))))

(defn prune-ns!
  "Unmap the *runtime* vars whose defining `def` form vanished from source.
  `prior` is the {qsym -> Var} snapshot the model recorded for ns-sym *before* the
  reload that just ran (capture it with `ns-def-var-snapshot` immediately before
  `load-ns!`); a var is pruned when it was in `prior`, no longer has a healthy def
  in the freshly reloaded model, and the SAME Var object is still interned. The
  identity check matters because vars are keyed by name, not object: a def deleted
  from source but re-created under a fresh Var (an explicit intern, or
  unmap-then-reintern in the new source) is a different object than the snapshot's,
  so it is left alone rather than destroyed. Warns - but still unmaps - if a pruned
  var has recorded usages (design §9.3: reflective uses can't be seen, so
  warn-and-prune, don't block). Returns the pruned symbols.

  Model-side, nothing to do here: load-ns!'s retract already handled the vanished
  def - a deleted def still referenced by other forms became a tombstone in :defs
  (:removed true, its usages preserved so the now-dangling references stay
  findable), one with no references left was dropped outright, and either way
  :entity->form was cleared by retract-form. This function only reconciles the
  live namespace: `require :reload` re-defs existing vars but never *removes* a var
  whose def was deleted, so the interned var would linger and shadow the source.

  Gating on `prior` (not `ns-interns` minus :defs) is deliberate: vars that
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
  [ns-sym prior]
  (when-not (seq (get-in @model [:ns->forms ns-sym]))
    (throw (ex-info (str "prune-ns! refused: " ns-sym " has no analysed forms in the model. "
                         "Run (load-ns! '" ns-sym ") first - prune is only valid right after "
                         "a full analysis, else it would unmap vars it simply never recorded.")
                    {:ns ns-sym})))
  (let [live     (ns-def-vars @model ns-sym)   ; healthy def qsyms after reload
        interned (ns-interns ns-sym)           ; {simple-sym var}
        gone (for [[k old-var] prior
                   :when (and old-var
                              (identical? (get interned (symbol (name k))) old-var)
                              (not (contains? live k)))]
               k)]
    (doseq [k gone]
      (when-let [us (seq (get-in @model [:usages k]))]
        (binding [*out* *err*]
          (println "WARN: pruning" (str k) "still referenced at"
                   (vec (for [s us] [(some-> (:from-ns s) ns-name) (:line s) (:column s)])))))
      (ns-unmap ns-sym (symbol (name k))))
    (mapv #(symbol (name %)) gone)))

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

  Fail-fast, like require: if a namespace fails to compile, load-ns! re-throws and
  the reload stops there (namespaces later in the order, and the second pass, do
  not run). This is intentional - it surfaces the error immediately rather than
  pressing on. No staleness is lost: load-ns! advances a namespace's mtime baseline
  only on a successful load, so the failed namespace and any not yet reached stay
  stale (see changed-namespaces) and are retried on the next stale-reload! call.

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
                    ;; Snapshot the ns's def-vars (with their Var identities) BEFORE
                    ;; load-ns! retracts them, so prune can tell which def forms
                    ;; vanished - and preserve any re-created afresh (see prune-ns!).
                    (let [prior (when prune (ns-def-var-snapshot @model ns-sym))]
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
