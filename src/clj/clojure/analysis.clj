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
  - across files, with precise source spans.

  Provenance is per top-level form: every fact is filed under the form that
  produced it, so re-analysing one file drops exactly its prior forms and installs
  the new ones, without disturbing the rest of the model (design §7). The stored
  model is just this form log; the by-entity query indexes are derived from it on
  demand and cached (build-index / derived), so the sink does no index maintenance.

  The reload/staleness unit is the FILE, keyed by the classpath-relative source
  path the compiler records (e.g. \"app/util.clj\"). This is deliberate:
    - a file is what an editor actually edits and saves;
    - one file can define several namespaces (a second `(ns ...)`, or `in-ns`);
      a file reload re-analyses all of them together, which a require-by-namespace
      cannot (it can't even name a file's second namespace);
    - `require`, which loads transitive deps and which the editor does NOT drive,
      already records this same classpath-relative key - so keying by it keeps the
      model consistent no matter how a file first entered it.
  Each form also keeps its owning namespace (:ns) as metadata, for the lints that
  read live namespace state (unused-aliases/refers/imports).

  Analysis is always populated FROM DISK - run-analysis (cold) and load-file!
  (single-file reload) both read the file - so the model stays in sync with what is
  written on disk and never reflects an un-saved REPL eval.

  Drivers: run-analysis (cold), load-file! (single file, atomic), stale-reload!
  (macro-aware cascade, §9), reload-files! (a given set, in macro order),
  retract-file!. Query with find-usages, definition,
  unused-*, file-namespaces, etc. - find-usages/definition take a Var or its
  fully-qualified name symbol.

  See doc/analysis-and-reload.md for the full design."
      :author "replique-clj"}
    clojure.analysis
  (:require [clojure.java.io :as io])
  (:import [clojure.lang IAnalysisSink Compiler RT Var]))

;; Vars are keyed by their fully-qualified name symbol (my.ns/foo), not by Var
;; object identity: a var deleted and later redefined mints a NEW Var object, so
;; identity keys would strand a deleted var's references under a dead key and pin
;; the dead Var (and its root value) in memory. A name key is stable across that
;; churn, keeps a deleted-but-referenced var findable (see below) and matches
;; Clojure's late binding (callers re-resolve the name). The sink receives resolved
;; Var objects and converts them via var-key.
;;
;; The model has two layers. The STORED layer is the compiler's write side - an
;; append log of top-level forms, each carrying the facts it produced; it is all the
;; sink ever mutates. The DERIVED layer is the query side - the by-entity indexes,
;; rebuilt from the forms by build-index and cached (see derived). The sink does no
;; index maintenance and no retract-on-redefine: a redefinition is just a later form,
;; and build-index resolves "which form defines each var" by replaying forms in fid
;; (definition) order, so the highest-fid def wins. A var referenced but not defined
;; by any live form simply has no :defs entry - definition returns nil for it, which
;; is what the old incremental tombstone yielded.
;;
;; stored (write model - mutated only by the sink / drivers):
;;   :forms           {fid {:ns :source :line :column + one key per non-empty fact
;;                          category: :usages :defs :keyword-usages :class-usages
;;                          :locals :local-uses :macro-deps, each a vector of facts}}
;;                                          Facts are stored BY CATEGORY rather than as
;;                                          tagged [op a b] tuples, so each fact is a
;;                                          single self-describing object (a Span /
;;                                          LocalSpan / MacroDep carrying its own entity
;;                                          key) - no wrapper allocated per fact, and
;;                                          none retained. Still self-contained, so the
;;                                          derived indexes rebuild from forms alone.
;;   :source->forms   {source #{fid}}   the file each form belongs to (the reload unit)
;;   :next-fid        long          global unique-id source for forms (shared)
;;   :file-mtime      {source long}   per-file on-disk mtime baseline (§9); a live file
;;                                    whose mtime differs is "changed"
;;   :non-files       #{source}     the sources a jar answers to, so changed-files can
;;                                  skip resolving them (§9); dropped by
;;                                  classpath-changed!, refilled as they are resolved
;; derived (built by build-index from :forms, cached keyed by :forms identity):
;;   :usages          {qsym  #{span}}       qsym = fully-qualified var name (my.ns/foo)
;;                                          span = a Span record (compact, primitive
;;                                          int coords); the public queries normalise
;;                                          it to {:source :line :column :end-line
;;                                          :end-column :from-ns [:macro]} via span->map
;;   :defs            {qsym  {:span span}}   only vars a live form defines
;;   :locals          {binding {:ns :name ...span :uses #{span}}}
;;   :keyword-usages  {kw    #{span}}
;;   :class-usages    {class-name-string #{span}}  (keyed by name, not Class - see class-key)
;;   :macro-deps      {ns-sym {macro-qsym #{fid}}}   compile-time edges (§9); each fid
;;                                          carries the expanding form's file (:source)
(def ^:private empty-model
  {:forms {} :source->forms {} :next-fid 0 :file-mtime {} :non-files #{}})

(defonce ^:private model (atom empty-model))

;; Two thread-local stacks, bound together by with-sink for the analysis extent
;; (matching the thread-local sink binding, so concurrent analyses on different
;; threads never mix). Neither is part of the shared model; the model is touched
;; only when a whole FILE commits.
;;
;; *file-stack*: the file load stack. beginFile pushes a FileFrame, endFile pops and
;; commits it. Compiler.load is re-entrant, so a require nested in a form pushes a
;; child frame that fully commits (or, on a compile error, is discarded) before the
;; parent form continues - which is exactly what makes a failed reload keep the files
;; that fully loaded and drop only the one that threw. Each frame buffers its own
;; file's completed forms off the shared atom until it commits, in one swap!.
;;
;; *form-stack*: the active (nested) top-level forms within the current file. Each
;; entry is an OpenForm buffer accumulating that form's facts; end-form! hands the
;; finished form to its file frame. nil when no analysis is in flight; current-form
;; then yields nil and facts are simply dropped (no form to attribute them to).
(def ^:private ^:dynamic *file-stack* nil)
(def ^:private ^:dynamic *form-stack* nil)

;; A usage/def span. The sink files one per var/keyword/class occurrence - by far
;; the most numerous fact - so its shape drives allocation during an analysed load.
;; A record with primitive int coordinates costs ~1/7th the bytes of the equivalent
;; array-map (measured), chiefly by not boxing the four coordinates into Integers.
;; The four coordinates are always ints at the sink boundary (IAnalysisSink passes
;; them as int); an absent end-line/end-column arrives non-nat and is stored as -1.
;; from-ns is the referencing namespace (nil for a def); macro is true for a
;; macro-call usage, else nil. Locals use their own record (LocalSpan) below.
;;
;; `entity` is the thing this span is ABOUT - the var key for a usage/def, the Keyword
;; for a keyword usage, the class-name string for a class usage. Carrying it on the
;; span makes a fact a SINGLE object: the form's per-category lists hold bare spans, so
;; there is no [op a b] tuple wrapper per fact (one fewer allocation each, and one
;; fewer object retained in the :forms log for the life of the code). span->map never
;; exposes it, so the public span shape is unchanged.
(defrecord Span [entity source ^int line ^int column ^int end-line ^int end-column from-ns macro])

(defn- norm-end [x] (if (nat-int? x) (int x) -1))

(defn- span
  ([entity source line column el ec] (span entity source line column el ec nil nil))
  ([entity source line column el ec from-ns macro]
   (->Span entity source (int line) (int column) (norm-end el) (norm-end ec)
           from-ns (when macro true))))

;; A local binding's def/use site. Locals are numerous too (every fn-arg and
;; let-binding), so they get the same lightweight-record treatment as Span rather
;; than a map built via merge: one allocation per local, primitive int coordinates,
;; no boxing. `binding` is the opaque identity token linking a def to its uses (the
;; entity key, carried on the span for the same one-object-per-fact reason as Span).
;; `lns` is the owning namespace; `lname` the binding's source name (present for a def,
;; nil for a use). Fields are named to avoid shadowing clojure.core/ns and /name;
;; build-index (local->map) projects them to the public :ns/:name keys, so the query
;; surface stays plain maps.
(defrecord LocalSpan [binding source ^int line ^int column ^int end-line ^int end-column lns lname])

(defn- local-span
  ([binding source line column el ec lns] (local-span binding source line column el ec lns nil))
  ([binding source line column el ec lns lname]
   (->LocalSpan binding source (int line) (int column) (norm-end el) (norm-end ec) lns lname)))

;; A compile-time macro-dependency edge: namespace `mns` expanded a call to macro var
;; `mvar`. The only fact with no span, so it gets its own two-field holder rather than a
;; tuple - a deftype (not a record) since nothing needs map access to it.
(deftype MacroDep [mns mvar])

(defn- span->map
  "Normalise a Span record to the documented plain-map span shape, for the public
  query API - so results carry no record type and compare = to map literals. Omits
  an absent end-line/end-column (stored as -1) and a nil from-ns/macro, exactly
  reproducing the map the sink used to build."
  [s]
  (cond-> {:source (:source s) :line (:line s) :column (:column s)}
    (nat-int? (:end-line s))   (assoc :end-line (:end-line s))
    (nat-int? (:end-column s)) (assoc :end-column (:end-column s))
    (:from-ns s)               (assoc :from-ns (:from-ns s))
    (:macro s)                 (assoc :macro true)))

(defn- spans->maps [spans]
  (when spans (into #{} (map span->map) spans)))

(defn- local->map
  "Normalise a LocalSpan record to the plain-map local shape build-index files in the
  :locals index - {:source :line :column :ns [:name] [:end-line :end-column]} - so the
  public locals surface (unused-locals, snapshot) carries no record type. :name is
  omitted for a use (lname nil), matching the map the sink used to build."
  [l]
  (cond-> {:source (:source l) :line (:line l) :column (:column l) :ns (:lns l)}
    (nat-int? (:end-line l))   (assoc :end-line (:end-line l))
    (nat-int? (:end-column l)) (assoc :end-column (:end-column l))
    (:lname l)                 (assoc :name (:lname l))))

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

(defn- class-key
  "Canonical model key for a class: its fully-qualified name string (Class.getName -
  e.g. \"java.lang.String\", \"my.ns.Foo\", \"[Ljava.lang.Object;\"). Keying by name,
  not the Class object, keeps a class redefined at the REPL - a reloaded deftype /
  defrecord mints a NEW Class under a fresh DynamicClassLoader - from pinning its old
  Class, and that loader, live as a stale map key until every referencing form is
  itself re-analysed. Occurrences of the old and new class thus unify under one key,
  exactly as var-key unifies a redefined var (design §5)."
  [^Class c]
  (.getName c))

;; A file being loaded. `buffer` collects its completed forms (plain maps, each with a
;; per-file :seq = begin-order rank); `counter` is a one-long mutable holding the next
;; rank (= count of forms begun in this file). Both are thread-local and touched only
;; by the loading thread, so no synchronisation. The frame commits its buffer to the
;; model in one swap! at endFile (commit-frame!): fids = base + :seq off the model's
;; current :next-fid.
(deftype FileFrame [source ^java.util.ArrayList buffer ^longs counter])

;; Fact categories. Facts are stored in one list PER CATEGORY rather than in a single
;; list of [op a b] tuples, so the category is implied by which list a fact is in and
;; each fact is a single self-describing object (the span, carrying its own entity).
;; These are array slots on the open form, so they are plain int constants.
(def ^:private ^:const CAT-USAGES   0)
(def ^:private ^:const CAT-DEFS     1)
(def ^:private ^:const CAT-KEYWORDS 2)
(def ^:private ^:const CAT-CLASSES  3)
(def ^:private ^:const CAT-LOCALS   4)
(def ^:private ^:const CAT-LOCALUSE 5)
(def ^:private ^:const CAT-MACRODEP 6)
(def ^:private ^:const N-CATS       7)

;; The model key each category is stored under on a committed form entry, indexed by
;; the constants above.
(def ^:private cat-keys
  [:usages :defs :keyword-usages :class-usages :locals :local-uses :macro-deps])

;; An open form is buffered in a thread-local mutable holder, NOT written to the shared
;; model fact-by-fact. Facts accumulate in per-category ArrayLists (`cats`, allocated
;; lazily - most forms touch only one or two categories) and the form's position is
;; corrected in place (form-start! fires repeatedly, last wins); at end-form! the
;; finished form is handed to its file `frame`'s buffer. So the sink never touches the
;; shared atom - not per fact, not per form. `pos` is [line column]; `seq` is the form's
;; begin-order rank within its file, used to assign a fid = base + seq at commit, so
;; build-index still replays a file's forms in begin order.
(deftype OpenForm [^long seq ^FileFrame frame ^longs pos ^objects cats])

(defn- current-frame ^FileFrame [] (when-let [s *file-stack*] (peek @s)))
(defn- current-form  ^OpenForm  [] (when-let [s *form-stack*] (peek @s)))

;; The sink's one mutation while a form is open: append a fact to the open form's list
;; for category `cat`, creating that list on first use. The fact is a single object that
;; carries its own entity key (Span/LocalSpan/MacroDep), so there is no tuple wrapper.
;; No model touch, no index maintenance - the by-entity indexes are derived on read
;; (build-index). nil holder (no form open) is a no-op; see the sink for why.
(defn- add-fact! [^OpenForm of ^long cat fact]
  (when of
    (let [^objects cats (.cats of)]
      (if-let [^java.util.ArrayList l (aget cats cat)]
        (.add l fact)
        (let [l (java.util.ArrayList.)]
          (aset cats cat l)
          (.add l fact)))))
  nil)

;; --- retraction (structural only - drops forms; indexes re-derive) ---------

(defn- drop-empty [m idx k]
  (if (empty? (get-in m [idx k])) (update m idx dissoc k) m))

;; Retracting a form is now purely structural: remove it from :forms and from its
;; file's :source->forms. There is no index surgery and no tombstone bookkeeping -
;; the query indexes are a pure function of the surviving forms (build-index), so a
;; var whose last defining form is gone stops appearing in :defs automatically, and
;; one still referenced elsewhere keeps its usages because those live on other forms.
(defn- retract-form [m fid]
  (if-let [fe (get-in m [:forms fid])]
    (let [m (update m :forms dissoc fid)]
      (if-let [src (:source fe)]
        (-> m (update-in [:source->forms src] disj fid) (drop-empty :source->forms src))
        m))
    m))

;; --- model mutators (called by the sink and by drivers) --------------------

(defn- begin-form! [source line column]
  ;; Assign the form a begin-order rank from its file frame's counter (NO model touch)
  ;; and push a fresh buffer for it on the form stack, carrying its frame so end-form!
  ;; routes it back to the right file. The form is not written to the model here, nor
  ;; at end-form! - commit-frame! turns the rank into a real fid (base + rank) when the
  ;; file commits. A form outside any file frame (a bare eval under run-analysis, an
  ;; unsupported use) has no frame and is dropped.
  (when-let [^FileFrame fr (current-frame)]
    (let [^longs c (.counter fr)
          seq      (aget c 0)]
      (aset c 0 (inc seq))
      (swap! *form-stack* conj
             (OpenForm. seq fr (long-array [(long line) (long column)])
                        (object-array N-CATS)))))
  nil)

(defn- form-start! [line column]
  ;; The reader reports the top-level form's true start once it commits to the
  ;; datum - past any leading whitespace, ; comment, #_ discard or non-selected
  ;; reader-conditional branch that beginForm's pre-scan could not skip. Correct
  ;; the open form's position so the recorded form span points at the form itself,
  ;; not the junk before it.
  ;; The reader fires formStart once per skipped leading no-op (each ; line, each
  ;; #_), then once for the datum - "last wins" gives the right position, so the
  ;; earlier calls are redundant swaps. Accepted: this is the analysis path, not a
  ;; hot loop, and the waste is bounded by a form's leading-comment count; avoiding
  ;; it would mean restructuring the reader's read() loop for no correctness gain.
  (when-let [of (current-form)]
    (let [^longs pos (.pos of)]
      (aset pos 0 (long line))
      (aset pos 1 (long column))))
  nil)

(defn- end-form! []
  (let [^OpenForm of (current-form)]
    (when *form-stack* (swap! *form-stack* pop))
    ;; Hand the finished form to its file frame's buffer - no model touch. Empty forms
    ;; (e.g. an outer do, EOF) are dropped; their begin-order rank still counted, so it
    ;; leaves a fid gap at commit, exactly as burning the id did before. A non-empty
    ;; form is frozen whole: each non-empty category list frozen to a vector under its
    ;; own key (empty categories are simply absent, keeping form entries small), plus
    ;; position and owning namespace (read from *ns* NOW, after the form - so an
    ;; `(ns ...)` form files under the ns it established). :seq is the begin-order rank;
    ;; commit-frame! turns it into the fid. Filed under the frame's :source (the file).
    (when of
      (let [^objects cats (.cats of)]
        (when (some #(let [^java.util.ArrayList l (aget cats (long %))]
                       (and l (not (.isEmpty l))))
                    (range N-CATS))
          (let [^longs pos    (.pos of)
                ^FileFrame fr (.frame of)]
            (.add ^java.util.ArrayList (.buffer fr)
                  (reduce (fn [fe i]
                            (let [^java.util.ArrayList l (aget cats (long i))]
                              (if (and l (not (.isEmpty l)))
                                (assoc fe (nth cat-keys i) (vec l))
                                fe)))
                          {:seq (.seq of) :source (.source fr)
                           :line (aget pos 0) :column (aget pos 1)
                           :ns (some-> *ns* ns-name)}
                          (range N-CATS)))))))
  nil))

;; --- file frames: begin/commit one file's forms atomically -----------------

(defn- commit-frame!
  "Install a whole file's buffered forms in ONE swap!, replacing that file's prior
  forms. The file's current forms are retracted and its buffered ones added in the same
  swap, so a reload is an atomic replace of just this file: fids = base + :seq off the
  model's current :next-fid (read inside the swap, so files committing on different
  threads get disjoint blocks), and :next-fid advances by the file's begin count (all
  begins, empties included, matching the old fid gaps). Because each file commits when
  its own load COMPLETES, a reload that throws part-way never reaches its commit - that
  file keeps its prior forms while every file that fully loaded (a transitive require,
  a sibling) is already in. A file with nothing buffered and no prior forms is a no-op,
  so the :forms identity - hence the derived-index cache - is preserved."
  [^FileFrame fr]
  (let [source                     (.source fr)
        ^java.util.ArrayList buffer (.buffer fr)
        begin-count                (aget ^longs (.counter fr) 0)]
    (when (or (pos? (.size buffer))
              (seq (get-in @model [:source->forms source])))
      (swap! model
             (fn [m]
               (let [m     (reduce retract-form m (get-in m [:source->forms source]))
                     base  (long (:next-fid m))
                     forms (persistent!
                            (reduce (fn [t fe]
                                      (assoc! t (+ base (long (:seq fe))) (dissoc fe :seq)))
                                    (transient (:forms m)) buffer))
                     s->f  (reduce (fn [s2f fe]
                                     (update s2f source (fnil conj #{}) (+ base (long (:seq fe)))))
                                   (:source->forms m) buffer)]
                 (assoc m :forms forms :source->forms s->f
                          :next-fid (+ base (long begin-count))))))))
  nil)

(defn- begin-file! [source]
  ;; A new file's load began (Compiler.load re-entered): push a fresh frame. No model
  ;; touch - the file commits only when it finishes (end-file!).
  (when *file-stack*
    (swap! *file-stack* conj (FileFrame. source (java.util.ArrayList.) (long-array [0]))))
  nil)

(defn- end-file! [_source]
  ;; The file finished loading (no throw): pop its frame and commit it. A throw during
  ;; the file's load means end-file! is never called for it (the compiler skips endFile
  ;; on error), so the frame is discarded with the stack unwind - its forms never reach
  ;; the model, and the file keeps whatever it had before.
  (when-let [fr (current-frame)]
    (swap! *file-stack* pop)
    (commit-frame! fr))
  nil)

;; Invariant: a fact is recorded ONLY when a form is open (current-form non-nil).
;; Without a form there is nowhere to file it (no fid to attribute it to, and it
;; could never be dropped on reload - a ghost), so every sink method is a no-op when
;; no form is open. This never drops anything real: load / require always open a
;; form; only a bare eval outside a form window (an unsupported use of run-analysis)
;; would land here, and that was never retractable anyway.
;;
;; Each method builds ONE self-contained fact object and appends it to its category -
;; no index is touched here. build-index replays the categories (in fid order) into the
;; query indexes on read, so the fact must carry everything the index needs, INCLUDING
;; its own entity key: a usage/def its var key, a keyword usage its keyword, a local its
;; binding token plus full info (ns/name/span). That is what lets a fact be a single
;; object with no [op a b] tuple around it.
(deftype AnalysisSink []
  IAnalysisSink
  (beginFile [_ source] (begin-file! source))
  (endFile [_ source] (end-file! source))
  (beginForm [_ source line column] (begin-form! source line column))
  (formStart [_ line column] (form-start! line column))
  (endForm [_] (end-form!))
  (varUsage [_ target from-ns source line column el ec]
    ;; when-let on the key, not let: var-key is nil only for a nil-ns var, which the
    ;; compiler should never resolve to here - but if one slips through, skip it
    ;; rather than write a nil key that would later NPE (namespace nil) in queries.
    (when-let [of (current-form)]
      (when-let [k (var-key target)]
        (add-fact! of CAT-USAGES (span k source line column el ec from-ns nil))))
    nil)
  (varDef [_ v source line column el ec]
    (when-let [of (current-form)]
      (when-let [k (var-key v)]
        (add-fact! of CAT-DEFS (span k source line column el ec))))
    nil)
  (localDef [_ binding name ns source line column el ec]
    (when-let [of (current-form)]
      (add-fact! of CAT-LOCALS (local-span binding source line column el ec ns name)))
    nil)
  (localUsage [_ binding ns source line column el ec]
    (when-let [of (current-form)]
      (add-fact! of CAT-LOCALUSE (local-span binding source line column el ec ns)))
    nil)
  (keywordUsage [_ kw from-ns source line column el ec]
    ;; The branch of a reader conditional this platform does not take is read with
    ;; *suppress-read* on: it is another platform's code, not this program's. A #_
    ;; discard is read normally and IS recorded - it is still written in the file.
    (when-let [of (when-not (RT/suppressRead) (current-form))]
      (add-fact! of CAT-KEYWORDS (span kw source line column el ec from-ns nil)))
    nil)
  (classUsage [_ c from-ns source line column el ec]
    (when-let [of (current-form)]
      (add-fact! of CAT-CLASSES (span (class-key c) source line column el ec from-ns nil)))
    nil)
  (macroExpansion [_ macro from-ns source line column el ec record-usage?]
    (when-let [of (current-form)]
     (when-let [mk (var-key macro)]      ; skip a nil-ns macro var (see varUsage)
      (let [ns-sym (ns-name from-ns)]
        ;; Always record the compile-time edge (stale reload needs it even for
        ;; expansion-introduced calls); record the macro *usage* only for a
        ;; source-written call. The edge's fid (the form's own, filled in by
        ;; build-index) carries the expanding form's file, which the §9 cascade reads.
        (add-fact! of CAT-MACRODEP (MacroDep. ns-sym mk))
        (when record-usage?
          (add-fact! of CAT-USAGES (span mk source line column el ec from-ns true))))))
    nil))

;; --- drivers ---------------------------------------------------------------

(defn reset-model!
  "Clear the whole model (cold-load driver: start from empty, design §8)."
  []
  (reset! model empty-model))

(defn- with-sink
  "Run `thunk` with the sink installed and fresh per-thread file + form stacks. Commits
  happen file-by-file as each file's load completes (commit-frame! at endFile), so there
  is nothing to flush here. If `thunk` throws, the file that was loading never commits
  (its frame is discarded with the stack unwind) while every file that fully loaded is
  already in - the reload's atomicity is per file, matching what the compiler left
  defined."
  [thunk]
  (push-thread-bindings {Compiler/ANALYSIS_SINK (->AnalysisSink)
                         #'*file-stack*         (atom [])
                         #'*form-stack*         (atom [])})
  (try (thunk) (finally (pop-thread-bindings))))

(declare record-file-mtime!)

(defn run-analysis
  "Invoke thunk with the analysis sink installed on this thread, so any
  compilation it triggers (load / require / eval) populates the model,
  form by form. Returns the thunk's value.

  Also records the source mtime of every FILE this run (re)compiled, so the run
  establishes its own staleness baseline. Without it a cold analysis leaves every
  file with a nil baseline, and the next `changed-files` would report them all as
  changed (nil baseline != current mtime), making the first `stale-reload!`
  re-evaluate the whole codebase. Only files actually touched this run are
  snapshotted (their :source->forms changed); baselines for untouched files - e.g.
  ones edited but not yet reloaded - are left intact, so a pending staleness flag
  elsewhere is not silently cleared.

  Every file this run (re)compiles replaces its own prior forms atomically as it
  finishes loading (commit-frame!), so re-running analysis over a file is idempotent -
  no accumulation - without any explicit retraction here."
  [thunk]
  (let [before (:source->forms @model)
        result (with-sink thunk)]
    (doseq [source (keys (:source->forms @model))
            :when (not= (get before source) (get-in @model [:source->forms source]))]
      (record-file-mtime! source))
    result))

(defn- retract-source*
  "Remove every form produced by `source` from the model, preserving all other
  files' references to its vars (design §8, single-file replace). Purely structural
  now - the query indexes re-derive from the surviving forms, so there is nothing to
  GC afterwards; a var still referenced elsewhere keeps its usages, and one no longer
  defined simply drops out of :defs on the next build."
  [source]
  (swap! model (fn [m] (reduce retract-form m (get-in m [:source->forms source]))))
  nil)

(defn retract-file!
  "Remove every form produced by `source` from the model, preserving all other
  files' references to its vars (e.g. before dropping a deleted file). `source` is
  the classpath-relative source path (e.g. \"app/util.clj\")."
  [source]
  (retract-source* source)
  nil)

;; --- §9: per-file source mtime (the staleness baseline) --------------------

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

(defn- resolve-source
  "How the classpath answers `source`, as [mtime jar?]:

    [n false]    a file, last modified at n
    [nil true]   something that is not a file - a jar entry, most often
    [nil false]  nothing at all - never loaded from a file, moved, or deleted

  No namespace->path munging: the source path IS the resource path.

  The last two are told apart because only the middle one is worth remembering, and
  `changed-files` remembers it. Whether a jar answers to a name is settled until the
  classpath changes under the process; whether nothing answers to it is settled by
  nothing at all - a file deleted and written back, a branch changed underneath - so
  that one is asked again every time.

  `source` is nil for a load with no file behind it at all - load-string,
  load-reader, and anything else reaching Compiler.load without a source path -
  which is the same \"no file\" answer, not an error. io/resource would NPE on it."
  [source]
  (if-let [^java.net.URL u (and source (io/resource source))]
    (if (= "file" (.getProtocol u))
      [(.lastModified (resource->file u)) false]
      [nil true])
    [nil false]))

(defn- record-file-mtime! [source]
  (swap! model assoc-in [:file-mtime source] (first (resolve-source source)))
  nil)

(defn classpath-changed!
  "Forget which analysed sources a jar answers to - see `changed-files`.

  To be called by whatever reads the classpath again: adding a directory or a jar
  to the loader, or noticing that one appeared. A source is skipped there because
  a jar answered to its name last time anything asked, and that stops being true
  the moment something earlier on the classpath answers to it instead - a file
  written over a library namespace is a file somebody then wants reloaded, and
  this is what lets it be seen.

  Costs one resolution of every skipped source on the next `changed-files` and
  nothing after that, so calling it when nothing changed is slow rather than
  wrong. Not calling it when something did is wrong."
  []
  (swap! model assoc :non-files #{})
  nil)

(defn snapshot-mtimes!
  "Record the current on-disk mtime of every analysed file, so later staleness
  checks have a reference point. `run-analysis` already baselines the files it
  compiles, so this is not needed after a plain cold analysis; use it to
  force-rebaseline the entire model (e.g. to deliberately clear all pending
  staleness flags at once)."
  []
  (doseq [source (keys (:source->forms @model))] (record-file-mtime! source))
  nil)

(defn- strip-ext [^String source]
  (cond (.endsWith source ".cljc") (subs source 0 (- (count source) 5))
        (.endsWith source ".clj")  (subs source 0 (- (count source) 4))
        :else source))

(defn- load-source!
  ;; Reload a file by its classpath resource: (load \"/app/util\") for source
  ;; \"app/util.clj\". `load` (unlike require) ALWAYS re-runs, and runs the whole
  ;; file - every (ns ...)/in-ns in it - so all of a file's namespaces re-analyse
  ;; together, and it records the same classpath-relative :source key `require` did.
  [source]
  (load (str "/" (strip-ext source))))

(defn- check-resource-source!
  "Reject a `source` that is not a loadable classpath-relative resource path - the
  key the compiler records (e.g. \"app/util.clj\"). An editor deals in ABSOLUTE
  paths and must translate to the resource path (strip the classpath root) before
  calling load-file!; catching that here turns it into a clear error instead of a
  cryptic FileNotFoundException from `load`, or a silent no-op when the key matches
  nothing in the model. A nil `io/resource` (deleted / moved / behind a jar) is
  rejected the same way, since load would fail anyway."
  [source]
  (when (or (not (string? source))
            (.startsWith ^String source "/")
            (nil? (io/resource source)))
    (throw (ex-info (str "load-file! expects a classpath-relative source path, the key the "
                         "compiler records (e.g. \"app/util.clj\") - not " (pr-str source)
                         ". An editor must translate an absolute file path to its resource "
                         "path (strip the classpath root) before calling load-file!.")
                    {:source source})))
  source)

(defn load-file!
  "Single-file analysis: replace `source`'s prior forms by reloading the file under the
  sink - no accumulation. Removes forms deleted from source (their facts vanish with the
  form, and the derived indexes reflect it). Refreshes the stored source mtime. `source`
  is the classpath-relative source path the compiler records (e.g. \"app/util.clj\").

  Reloads via the file's resource (`load`), NOT require-by-namespace, so it handles a
  file that defines several namespaces (a require can't even name a file's second
  namespace) and keeps :source consistent with the cold analysis.

  Atomic BY CONSTRUCTION, per file: each file's forms are buffered and committed - the
  file's old forms retracted and its new ones added - in one swap! only when THAT file's
  load completes (commit-frame! at endFile). If the reload of `source` throws (typically
  an edited source with a compile/syntax error) its frame never commits, so `source`
  keeps its prior forms with no rollback bookkeeping - while every file the reload
  transitively loaded to completion (a fresh require, a sibling) is kept, matching what
  the compiler actually left defined. The mtime is refreshed by run-analysis only for
  files whose forms actually changed, so a failed `source` stays flagged stale and
  retries."
  [source]
  (check-resource-source! source)
  (run-analysis #(load-source! source))
  source)

;; --- derived query indexes (built from :forms, cached) ---------------------

;; The by-entity indexes are a pure function of the stored form log, so they are not
;; maintained as the sink runs - they are rebuilt on demand and cached. So is the file
;; macro graph, further down, which is built from them; `cached-by-forms` is the one
;; way both are kept, so that everything derived from the log goes stale by the same
;; rule and there is one place to read that rule off.
(defn- cached-by-forms
  "What `build` computes from the form log, recomputed only when `forms` is not the
  log `cache` already holds a value for.

  The cache key is the IDENTITY of the :forms map. Any analysis or retraction
  produces a new :forms value (immutable, structurally shared) while nothing else
  touches it, so `identical?` decides in one pointer comparison whether the cached
  value still describes the model, and a quiescent model - nothing being analysed -
  is a straight cache hit. `build` is a thunk over the same `forms`, so two threads
  racing on one log compute the same value and the second writer simply overwrites
  the first with its equal, harmlessly. `cache` is an atom holding
  {:forms <the log the value was built from> :value <the value>}."
  [cache forms build]
  (let [c @cache]
    (if (identical? forms (:forms c))
      (:value c)
      (let [built (build)]
        (reset! cache {:forms forms :value built})
        built))))

(defonce ^:private index-cache (atom {:forms nil :value nil}))

(defn- build-index
  "Replay the per-form fact log into the by-entity query indexes. Forms are replayed
  in ascending fid (definition) order, so a redefinition - a later form defining the
  same var - naturally overwrites the earlier :defs entry: highest fid wins, which is
  what the old eager retract-on-redefine achieved. A var referenced but defined by no
  live form gets usages but no :defs entry, so `definition` returns nil for it (what
  the old incremental tombstone yielded). Pure function of `forms`.

  Returns {:usages :defs :keyword-usages :class-usages :locals :macro-deps}, each
  shaped exactly as the eagerly-maintained index was, so the queries are unchanged.

  The six by-entity sub-indexes are accumulated as TRANSIENT maps: on a large log a
  single entity map grows to thousands of keys, and a persistent update-in would
  rebuild its spine on every one of the (many) facts touching it. Transient assoc!
  mutates in place, so replaying the log is close to allocation-free apart from the
  entity values themselves (the persistent sets / entry maps that are the actual
  data). The transient must be threaded (assoc! may promote and return a new object),
  so each sub-index is re-stored into the (also transient) idx via its return value.
  The result is frozen with persistent! - a plain, fully persistent index.

  Facts are stored per CATEGORY on the form (no [op a b] tuples), so there is no tag to
  dispatch on: each category list is folded straight into its sub-index, and every fact
  carries its own entity key. Locals are folded before local-uses, so a form's binding
  defs are all registered before any of its uses are attached (a local is lexically
  scoped to its form, so this is exactly the right scope)."
  [forms]
  (let [add-span (fn [idx k ^Span s]
                   (let [sub (get idx k)
                         e   (.entity s)]
                     (assoc! idx k (assoc! sub e (conj (get sub e #{}) s)))))
        idx (reduce
             (fn [idx fid]
               (let [fe (get forms fid)]
                 (as-> idx idx
                   (reduce (fn [idx s] (add-span idx :usages s)) idx (:usages fe))
                   (reduce (fn [idx s] (add-span idx :keyword-usages s)) idx (:keyword-usages fe))
                   (reduce (fn [idx s] (add-span idx :class-usages s)) idx (:class-usages fe))
                   (reduce (fn [idx ^Span s]
                             (let [sub (get idx :defs)]
                               (assoc! idx :defs (assoc! sub (.entity s) {:span s}))))
                           idx (:defs fe))
                   ;; A local's def carries its full info (a LocalSpan); project it to the
                   ;; plain-map index entry, keeping any :uses already gathered.
                   (reduce (fn [idx ^LocalSpan l]
                             (let [sub (get idx :locals)
                                   b   (.binding l)]
                               (assoc! idx :locals
                                       (assoc! sub b (assoc (local->map l)
                                                            :uses (get (get sub b) :uses #{}))))))
                           idx (:locals fe))
                   (reduce (fn [idx ^LocalSpan l]
                             (let [sub (get idx :locals)
                                   b   (.binding l)
                                   cur (get sub b)]
                               (if cur
                                 (assoc! idx :locals
                                         (assoc! sub b (update cur :uses (fnil conj #{}) (local->map l))))
                                 idx)))
                           idx (:local-uses fe))
                   ;; The edge is stamped with fid (the expanding form), so the §9 file
                   ;; cascade can find the expanding file.
                   (reduce (fn [idx ^MacroDep d]
                             (let [sub (get idx :macro-deps)
                                   n   (.mns d)]
                               (assoc! idx :macro-deps
                                       (assoc! sub n (update (get sub n {}) (.mvar d)
                                                             (fnil conj #{}) fid)))))
                           idx (:macro-deps fe)))))
             (transient {:usages (transient {}) :defs (transient {}) :keyword-usages (transient {})
                         :class-usages (transient {}) :locals (transient {}) :macro-deps (transient {})})
             (sort (keys forms)))]
    (reduce-kv (fn [m k v] (assoc m k (persistent! v))) {} (persistent! idx))))

(defn- derived
  "The cached by-entity indexes for model value `m` (deref the model once and pass
  it, so a query reads a single consistent snapshot). Rebuilt only when `m`'s :forms
  differ from the ones the cached indexes were built from."
  [m]
  (let [forms (:forms m)]
    (cached-by-forms index-cache forms #(build-index forms))))

;; --- queries ---------------------------------------------------------------

(defn- ->var-key
  "Normalise a find-usages / definition argument to a var-key: accept a Var or a
  fully-qualified name symbol (my.ns/foo), the latter being what an editor has at a
  cursor without a live Var object."
  [var-or-sym]
  (cond
    (instance? Var var-or-sym) (var-key var-or-sym)
    (qualified-symbol? var-or-sym) var-or-sym
    :else (throw (IllegalArgumentException.
                  (str "find-usages/definition expect a Var or fully-qualified symbol, got: "
                       (pr-str var-or-sym))))))

(defn find-usages
  "Usage sites recorded for a var - pass the Var, or its fully-qualified name symbol
  (my.ns/foo). Returns a set of spans
  {:from-ns :source :line :column :end-line :end-column [:macro]}."
  [var-or-sym]
  (spans->maps (get (:usages (derived @model)) (->var-key var-or-sym))))

(defn definition
  "Definition site recorded for a var - pass the Var or its fully-qualified name
  symbol. Returns a span, or nil. A var referenced but defined by no live form (its
  def deleted from source, or never analysed) is treated as undefined - returns nil."
  [var-or-sym]
  (some-> (:span (get (:defs (derived @model)) (->var-key var-or-sym))) span->map))

(defn find-keyword-usages
  "Occurrence sites recorded for keyword kw. Auto-resolved keywords are indexed
  fully-qualified, so pass e.g. (keyword \"my.ns\" \"x\")."
  [kw]
  (spans->maps (get (:keyword-usages (derived @model)) kw)))

(defn find-class-usages
  "Occurrence sites recorded for class c - a java.lang.Class, or its fully-qualified
  name as a string/symbol. Usages are keyed by class name, so a reloaded class's
  occurrences unify with the original's and no stale Class/loader is pinned."
  [c]
  (spans->maps (get (:class-usages (derived @model)) (if (class? c) (.getName ^Class c) (str c)))))

(defn macro-deps
  "Compile-time macro dependency edges. No arg: {ns-sym #{macro-qsym}}. With a
  namespace symbol: the set of macro var names (qualified symbols) it expanded
  (design §9)."
  ([] (reduce-kv (fn [acc ns mm] (assoc acc ns (set (keys mm)))) {} (:macro-deps (derived @model))))
  ([ns-sym] (set (keys (get-in (derived @model) [:macro-deps ns-sym])))))

(defn unused-locals
  "Source-written local bindings with no recorded reference. Optionally restrict
  to a namespace. Each result is the binding's def site plus :name and :ns."
  ([] (unused-locals nil))
  ([ns-sym]
   (for [[_ info] (:locals (derived @model))
         :when (empty? (:uses info))
         :when (or (nil? ns-sym) (= ns-sym (ns-name (:ns info))))]
     (dissoc info :uses))))

(defn file-forms
  "The fids currently attributed to file `source` (for inspection/tests)."
  [source]
  (get-in @model [:source->forms source] #{}))

(defn file-namespaces
  "The namespaces (ns-name symbols) file `source` defines, per the model - one file
  can define several. Use this to drive the per-namespace lints for a file."
  [source]
  (set (for [fid (file-forms source)
             :let [n (get-in @model [:forms fid :ns])]
             :when n]
         n)))

(defn ns-forms
  "The fids currently attributed to ns-sym (scans :forms by :ns metadata). Present
  for inspection; the reload unit is the file (see file-forms)."
  [ns-sym]
  (set (for [[fid fe] (:forms @model) :when (= ns-sym (:ns fe))] fid)))

(defn source->file
  "The on-disk java.io.File for a classpath-relative source path, or nil if it
  can't be resolved to a file (behind a jar, moved). For an editor to open the file
  a span's :source names."
  [source]
  (when-let [u (io/resource source)]
    (when (= "file" (.getProtocol u)) (resource->file u))))

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
  (let [m (derived @model)
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
  (let [uses (:usages (derived @model))
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

;; --- stale reload + prune (design §9) --------------------------------------

(defn changed-files
  "Analysed files (classpath-relative source paths) whose on-disk mtime differs from
  the recorded baseline - edited since last analysis/reload. A file that no longer
  resolves to a file (mtime nil - moved, deleted, or now behind a jar) is skipped:
  reloading it would only fail, so it is not flagged.

  A source a jar answers to is skipped without being resolved at all, and is
  remembered here as one, because resolving a source costs a classloader lookup
  per source per call and most of a real model is library namespaces read out of
  jars - 477 of the 868 files in one measured project - none of which anybody can
  edit. Remembered here rather than where they are analysed, which is the only
  other place that resolves them: the set is dropped whenever the classpath
  changes (see `classpath-changed!`), so one only ever filled by a load would sit
  empty from the first drop until the next load."
  []
  (let [m @model
        non-files (:non-files m)
        asked (vec (for [source (keys (:source->forms m))
                         :when (not (contains? non-files source))]
                     (into [source] (resolve-source source))))
        in-jars (into #{} (for [[source _ jar?] asked :when jar?] source))]
    (when (seq in-jars)
      (swap! model update :non-files (fnil into #{}) in-jars))
    (set (for [[source now] asked
               :when (and (some? now) (not= now (get (:file-mtime m) source)))]
           source))))

(defn- macro-owner
  "The macro-defining namespace symbol for a macro key (a qualified symbol)."
  [macro-key] (symbol (namespace macro-key)))

(defn- build-file-macro-graph
  "Forward compile-time dependency graph over FILES: {source #{dep-source}} where a
  form in `source` expands a macro whose defining namespace lives in `dep-source`.
  Derived from :macro-deps (each edge's fid carries the expanding form's file) and
  the ns->sources projection of :forms (a macro-defining ns maps to the file(s) it
  lives in). Self-edges are dropped - a file that expands its own macros needs no
  cross-file reload of itself."
  [m]
  (let [forms    (:forms m)
        ns->srcs (reduce-kv (fn [acc _ fe]
                              (if-let [n (:ns fe)]
                                (update acc n (fnil conj #{}) (:source fe))
                                acc))
                            {} forms)]
    (reduce-kv
     (fn [g _ mm]
       (reduce-kv
        (fn [g mk fids]
          (let [owner-srcs (get ns->srcs (macro-owner mk))]
            (reduce (fn [g fid]
                      ;; :macro-deps fids are the forms build-index replayed, so each
                      ;; is a live form and s is normally non-nil; guard anyway so any
                      ;; future drift injects no nil-source edge.
                      (if-let [s (:source (get forms fid))]
                        (reduce (fn [g os] (if (= os s) g (update g s (fnil conj #{}) os)))
                                g owner-srcs)
                        g))
                    g fids)))
        g mm))
     {} (:macro-deps (derived m)))))

;; Cached exactly as the query indexes it is built from are, and for the same reason:
;; the graph is a pure function of the form log, and building it walks every macro-dep
;; edge in the model - 5.6 ms over 400 files / 8400 forms, and the dominant cost of
;; answering "what is stale?", which is a question a client asks before anything it
;; wants a current answer to and so one asked far more often than the log changes.
;; Keyed by :forms identity, so a load or a retraction invalidates it and nothing
;; else has to.
(defonce ^:private file-graph-cache (atom {:forms nil :value nil}))

(defn- file-macro-graph
  "`build-file-macro-graph` of model value `m`, built once per form log."
  [m]
  (cached-by-forms file-graph-cache (:forms m) #(build-file-macro-graph m)))

(defn- reverse-file-graph
  "Invert a forward file graph {source #{dep-source}} to {dep-source #{dependent
  source}} - the direction the stale cascade walks (edit a file -> its dependents)."
  [fwd]
  (reduce-kv (fn [rev src deps]
               (reduce (fn [rev d] (update rev d (fnil conj #{}) src)) rev deps))
             {} fwd))

(defn stale-files
  "The set of files to reload: every file whose source was edited since last loaded
  (the seed - no arg = changed-files), plus every file that transitively compile-
  time-depends on the seed through the file macro graph (design §9). Runtime-only
  (function-call) dependents are excluded - a plain var re-resolves at runtime and
  needs no recompile; only macro dependents do. Conservative: any edit to a
  macro-defining file marks ALL its macro-dependent files stale (it does not
  distinguish which form in the file changed)."
  ([] (stale-files (changed-files)))
  ([seed]
   (let [rev (reverse-file-graph (file-macro-graph @model))]
     (loop [dirty (set seed), queue (vec seed)]
       (if-let [x (peek queue)]
         (let [fresh (remove dirty (get rev x))]
           (recur (into dirty fresh) (into (pop queue) fresh)))
         dirty)))))

(defn- topo-order
  "Order files so each file's macro-dependency files come first. Cycles are broken
  arbitrarily (remaining nodes appended). Deps outside `nodes` are ignored - they
  are not being reloaded, so they are already current."
  [files dep-fn]
  (let [nodes (set files)]
    (loop [order [], placed #{}, remaining nodes]
      (if (empty? remaining)
        order
        (let [ready (filter (fn [n] (every? #(or (placed %) (not (nodes %))) (dep-fn n)))
                            remaining)]
          (if (empty? ready)
            (into order remaining)
            (recur (into order ready) (into placed ready) (reduce disj remaining ready))))))))

(defn- healthy-def?
  "True when the derived index `idx` records a def for var-key k. (There is no longer
  a tombstone flag: a var no live form defines simply has no :defs entry.)"
  [idx k]
  (some? (get (:defs idx) k)))

(defn file-def-vars
  "The fully-qualified name symbols the derived index `idx` records a `def` form for
  IN file `source`, keyed off each def's span :source. Exactly the population
  prune-file! may consider: only vars the compiler saw defined by a top-level def can
  be judged 'deleted' by disappearance. Pass (derived @model) as `idx`."
  [idx source]
  (set (for [[k e] (:defs idx)
             :when (= source (:source (:span e)))]
         k)))

(defn file-def-var-snapshot
  "Capture {qsym -> the currently-interned Var object} for the defs in file `source`.
  This is prune-file!'s `prior`; take it *before* the reload so that, since vars are
  keyed by name (not identity), prune can still tell a lingering deleted-def var (the
  SAME Var object survives a reload) from one the reloaded source deleted and
  re-created under a fresh identity (which must be preserved)."
  [m source]
  (into {} (for [k (file-def-vars (derived m) source)
                 :let [home (find-ns (symbol (namespace k)))
                       v    (when home (get (ns-interns home) (symbol (name k))))]]
             [k v])))

(defn prune-file!
  "Unmap the *runtime* vars whose defining `def` form vanished from file `source`.
  `prior` is the {qsym -> Var} snapshot the model recorded for `source` *before* the
  reload that just ran (capture it with `file-def-var-snapshot` immediately before
  `load-file!`); a var is pruned when it was in `prior`, the model now records NO
  healthy def for it anywhere (deleted outright - not merely moved to another file
  that has since been reloaded), and the SAME Var object is still interned in its
  home namespace. The identity check matters because vars are keyed by name, not
  object: a def deleted from source but re-created under a fresh Var (an explicit
  intern, or unmap-then-reintern) is a different object, so it is left alone rather
  than destroyed. Warns - but still unmaps - if a pruned var has recorded usages
  (design §9.3: reflective uses can't be seen, so warn-and-prune, don't block).
  Returns the pruned qsyms.

  Model-side, nothing to do here: load-file!'s retract already dropped the vanished
  def's form, so the derived :defs no longer records a def for it (its usages, living
  on other files' forms, are untouched). This only reconciles the live namespace:
  `require :reload` / `load` re-def existing vars but never *remove* a var whose def
  was deleted, so the interned var would linger and shadow the source.

  Gating on `prior` (not `ns-interns` minus :defs) is deliberate: vars never recorded
  as a `def` are never candidates, so intern-created vars are left alone. In
  particular a `defprotocol`'s method vars (created by `intern`, never a DefExpr) are
  never pruned; the cost is that a genuinely *deleted* protocol method (or a deleted
  `defonce`, which reload also does not re-def) leaks a stale interned var until a
  cold reanalysis. That is the safe direction: never unmap a live protocol method.

  PRECONDITION: only valid immediately after `load-file!` of `source` (which
  `stale-reload!` does), so :defs has just been fully repopulated. Refuses to run on
  a file the model has never analysed (no forms in :source->forms), turning misuse
  into a loud error instead of silent data loss."
  [source prior]
  (when-not (seq (get-in @model [:source->forms source]))
    (throw (ex-info (str "prune-file! refused: " source " has no analysed forms in the model. "
                         "Run (load-file! \"" source "\") first - prune is only valid right after "
                         "a full analysis, else it would unmap vars it simply never recorded.")
                    {:source source})))
  (let [m    @model
        idx  (derived m)
        gone (for [[k old-var] prior
                   :let [home (find-ns (symbol (namespace k)))
                         cur  (when home (get (ns-interns home) (symbol (name k))))]
                   :when (and old-var (identical? cur old-var) (not (healthy-def? idx k)))]
               k)]
    (doseq [k gone]
      (when-let [us (seq (get (:usages idx) k))]
        (binding [*out* *err*]
          (println "WARN: pruning" (str k) "still referenced at"
                   (vec (for [s us] [(some-> (:from-ns s) ns-name) (:line s) (:column s)])))))
      (ns-unmap (symbol (namespace k)) (symbol (name k))))
    (vec gone)))

(defn- topo-respected?
  "True when `order` already loads every file after all its macro-deps (per dep-fn).
  Deps outside `order` are ignored - they were not reloaded, so they are current."
  [order dep-fn]
  (let [idx (zipmap order (range))]
    (every? (fn [x] (every? (fn [y] (or (nil? (idx y)) (< (idx y) (idx x))))
                            (dep-fn x)))
            order)))

(defn reload-files!
  "Reload `files` (classpath-relative source paths) via load-file! in macro-
  dependency (topological) order - macro-defining files before the files that
  re-expand them - and optionally prune vanished vars (:prune true). Returns the
  final reload order (a vector of source paths). stale-reload! is this over
  stale-files; clojure.cljs.analysis calls it over the macro files a ClojureScript
  compile depends on.

  Fail-fast, like require: if a file fails to compile, load-file! re-throws and the
  reload stops there (files later in the order, and the second pass, do not run).
  This is intentional - it surfaces the error immediately. No staleness is lost:
  load-file! advances a file's mtime baseline only on a successful load, so the
  failed file and any not yet reached stay stale (see changed-files) and are retried
  on the next stale-reload! call.

  Two-pass, to handle a macro dependency introduced by the very edit being reloaded.
  The first-pass order comes from the pre-reload macro graph, which cannot yet know
  an edge only this edit adds (e.g. file A newly requires and expands a macro from
  file B): A could be ordered before B and expand B's stale macro. Pass 1 reloads in
  that best-guess order, which recompiles every edited file and so completes the
  graph. We then recompute the order; if pass 1 already respected it (the common
  case) we are done at no extra cost, otherwise a file expanded a stale macro and we
  reload once more in the corrected order. Two passes always suffice: after pass 1
  the on-disk source is fixed and every edited file analysed, so the recomputed
  graph - and its order - is stable.

  Limitation: this repairs *stale* expansion (the macro exists but is the old
  version). An edit that calls a macro which did not exist in the dependency's old
  version can still make pass 1 error if misordered; ordering by the new requires
  would be needed for that, which this does not do."
  [files & {:keys [prune]}]
  (let [dep-fn  (fn [g] (fn [s] (get g s #{})))
        reload! (fn [order]
                  (doseq [source order]
                    ;; Snapshot the file's def-vars (with their Var identities) BEFORE
                    ;; load-file! retracts them, so prune can tell which def forms
                    ;; vanished - and preserve any re-created afresh (see prune-file!).
                    (let [prior (when prune (file-def-var-snapshot @model source))]
                      (load-file! source)
                      (when prune (prune-file! source prior)))))
        stale   (set files)
        order1  (topo-order stale (dep-fn (file-macro-graph @model)))]
    (reload! order1)
    ;; Pass 1 completed the macro graph; re-derive the order from it.
    (let [df (dep-fn (file-macro-graph @model))]
      (if (topo-respected? order1 df)
        order1
        (let [order2 (topo-order stale df)]
          (reload! order2)
          order2)))))

(defn stale-reload!
  "Macro-aware stale reload (design §9.2): reload-files! over the stale set
  (stale-files - changed files + their transitive macro-dependent files), in
  macro-dependency order, optionally pruning vanished vars (:prune true). Returns
  the final reload order (a vector of source paths). Fail-fast, two-pass - see
  reload-files!."
  [& {:keys [prune]}]
  (reload-files! (stale-files) :prune prune))

(defn snapshot
  "The whole model, for inspection/tests: the stored form log merged with the derived
  by-entity indexes (:usages/:defs/:keyword-usages/:class-usages/:locals/:macro-deps),
  so callers see the same keys as before the indexes became lazy. Span records are
  normalised to plain maps here too, so the whole public surface is record-free and
  spans compare = to map literals."
  []
  (let [m        @model
        idx      (derived m)
        norm-set (fn [mm] (reduce-kv (fn [a k s] (assoc a k (spans->maps s))) {} mm))]
    (merge m idx
           {:usages         (norm-set (:usages idx))
            :keyword-usages (norm-set (:keyword-usages idx))
            :class-usages   (norm-set (:class-usages idx))
            :defs           (reduce-kv (fn [a k e] (assoc a k (update e :span span->map)))
                                       {} (:defs idx))})))
