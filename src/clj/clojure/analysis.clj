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
  (macro-aware cascade, §9), retract-file!. Query with find-usages, definition,
  unused-*, file-namespaces, etc. - find-usages/definition take a Var or its
  fully-qualified name symbol.

  See doc/analysis-and-reload.md for the full design."
      :author "replique-clj"}
    clojure.analysis
  (:require [clojure.java.io :as io])
  (:import [clojure.lang IAnalysisSink Compiler Var]))

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
;;   :forms           {fid {:ns :source :line :column :facts [instr]}}
;;                                          instr = [op a b], self-contained so the
;;                                          derived indexes can be rebuilt from it alone
;;   :source->forms   {source #{fid}}   the file each form belongs to (the reload unit)
;;   :next-fid        long          global unique-id source for forms (shared)
;;   :file-mtime      {source long}   per-file on-disk mtime baseline (§9); a live file
;;                                    whose mtime differs is "changed"
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
  {:forms {} :source->forms {} :next-fid 0 :file-mtime {}})

(defonce ^:private model (atom empty-model))

;; The stack of active (nested) top-level forms is per-thread, not part of the
;; shared model: with-sink binds it to a fresh atom for each analysis. This keeps
;; "which form am I inside" thread-local (matching the thread-local sink binding),
;; so concurrent analyses on different threads cannot stamp facts with each other's
;; form ids. Only the recorded facts - and :next-fid, the global id source - live
;; in the shared model. Each stack entry is a thread-local OpenForm buffer, not a
;; bare fid, so a form's facts accumulate off the shared atom until end-form! commits
;; them. nil when no analysis is in flight; current-form then yields nil and facts are
;; simply dropped (no form to attribute them to).
(def ^:private ^:dynamic *form-stack* nil)

;; When bound to an atom, begin-form! logs every fid it allocates here. load-file!
;; uses this to roll back a failed reload precisely - retracting exactly the forms
;; that reload created (wherever endForm filed them) - instead of resetting the
;; whole shared model, which would clobber facts other threads committed meanwhile.
;; nil outside load-file!, so ordinary analyses pay nothing for it.
(def ^:private ^:dynamic *created-fids* nil)

;; A usage/def span. The sink files one per var/keyword/class occurrence - by far
;; the most numerous fact - so its shape drives allocation during an analysed load.
;; A record with primitive int coordinates costs ~1/7th the bytes of the equivalent
;; array-map (measured), chiefly by not boxing the four coordinates into Integers.
;; The four coordinates are always ints at the sink boundary (IAnalysisSink passes
;; them as int); an absent end-line/end-column arrives non-nat and is stored as -1.
;; from-ns is the referencing namespace (nil for a def); macro is true for a
;; macro-call usage, else nil. Locals use their own record (LocalSpan) below.
(defrecord Span [source ^int line ^int column ^int end-line ^int end-column from-ns macro])

(defn- norm-end [x] (if (nat-int? x) (int x) -1))

(defn- span
  ([source line column el ec] (span source line column el ec nil nil))
  ([source line column el ec from-ns macro]
   (->Span source (int line) (int column) (norm-end el) (norm-end ec) from-ns (when macro true))))

;; A local binding's def/use site. Locals are numerous too (every fn-arg and
;; let-binding), so they get the same lightweight-record treatment as Span rather
;; than a map built via merge: one allocation per local, primitive int coordinates,
;; no boxing. `lns` is the owning namespace; `lname` the binding's source name
;; (present for a def, nil for a use). Fields are named to avoid shadowing
;; clojure.core/ns and /name; build-index (local->map) projects them to the public
;; :ns/:name keys, so the query surface stays plain maps.
(defrecord LocalSpan [source ^int line ^int column ^int end-line ^int end-column lns lname])

(defn- local-span
  ([source line column el ec lns] (local-span source line column el ec lns nil))
  ([source line column el ec lns lname]
   (->LocalSpan source (int line) (int column) (norm-end el) (norm-end ec) lns lname)))

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

;; An open form is buffered in a thread-local mutable holder, NOT written to the
;; shared model fact-by-fact. Facts accumulate in a plain ArrayList and the form's
;; position is corrected in place (form-start! fires repeatedly, last wins); the
;; whole form is committed to the model in a single swap! at end-form!. This keeps
;; the per-fact hot path allocation-free (an ArrayList.add, no persistent-map spine
;; rebuild) and off the shared atom - only begin-form! (fid bump) and end-form!
;; (one commit) touch `model`. `pos` is [line column]; `fid` was allocated at begin
;; so build-index still replays forms in allocation order.
(deftype OpenForm [^long fid source ^longs pos ^java.util.ArrayList facts])

(defn- current-form ^OpenForm [] (when-let [s *form-stack*] (peek @s)))

;; The sink's one mutation while a form is open: append a self-contained fact instr
;; [op a b] to the open form's buffer. No model touch, no index maintenance - the
;; by-entity indexes are derived on read (build-index). nil holder (no form open) is
;; a no-op; see the sink for why.
(defn- add-fact! [^OpenForm of instr]
  (when of (.add ^java.util.ArrayList (.facts of) instr))
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

;; Re-add one previously-retracted form to the live model, used only by load-file!
;; to roll back a failed reload without disturbing any other form. Restores just the
;; stored layer (the form and its file membership) from the pre-reload snapshot; the
;; indexes re-derive from it. `snap` is that snapshot.
(defn- reinstate-form [m snap fid]
  (if-let [fe (get-in snap [:forms fid])]
    (let [m (assoc-in m [:forms fid] fe)]
      (if-let [src (:source fe)]
        (update-in m [:source->forms src] (fnil conj #{}) fid)
        m))
    m))

;; --- model mutators (called by the sink and by drivers) --------------------

(defn- begin-form! [source line column]
  ;; Allocate a globally-unique fid from the shared model (the only begin-time model
  ;; touch - just the counter bump), then push a fresh thread-local buffer for the
  ;; form on this thread's stack. The form itself is not written to the model until
  ;; end-form! commits it. The fid used is (dec :next-fid) after the atomic bump.
  (let [m'  (swap! model update :next-fid inc)
        fid (dec (:next-fid m'))]
    (when *form-stack*
      (swap! *form-stack* conj
             (OpenForm. fid source (long-array [(long line) (long column)])
                        (java.util.ArrayList.))))
    (when *created-fids* (swap! *created-fids* conj fid)))
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
    ;; Commit the buffered form in one swap!. Empty forms (e.g. an outer do, EOF) are
    ;; simply never written - the begin-time fid bump already burned their id, exactly
    ;; as the old drop-empty path did. A non-empty form is installed whole: its facts
    ;; (frozen from the buffer), position, file membership and owning namespace (read
    ;; from *ns* now, after the form - so an `(ns ...)` form files under the ns it
    ;; established). The reload unit is the file, so it is also filed under :source.
    (when (and of (not (.isEmpty ^java.util.ArrayList (.facts of))))
      (let [fid    (.fid of)
            src    (.source of)
            ^longs pos (.pos of)]
        (swap! model
               (fn [m]
                 (-> m
                     (assoc-in [:forms fid] {:source src
                                             :line (aget pos 0) :column (aget pos 1)
                                             :ns (some-> *ns* ns-name)
                                             :facts (vec (.facts of))})
                     (update-in [:source->forms src] (fnil conj #{}) fid)))))))
  nil)

;; Invariant: a fact is recorded ONLY when a form is open (current-form non-nil).
;; Without a form there is nowhere to file it (no fid to attribute it to, and it
;; could never be dropped on reload - a ghost), so every sink method is a no-op when
;; no form is open. This never drops anything real: load / require always open a
;; form; only a bare eval outside a form window (an unsupported use of run-analysis)
;; would land here, and that was never retractable anyway.
;;
;; Each method builds a SELF-CONTAINED fact instr [op a b] and appends it - no index
;; is touched here. build-index replays these instrs (in fid order) into the query
;; indexes on read. So the instr must carry everything the index needs: a def
;; carries its span (not just the qsym), a local its full info (ns/name/span).
(deftype AnalysisSink []
  IAnalysisSink
  (beginForm [_ source line column] (begin-form! source line column))
  (formStart [_ line column] (form-start! line column))
  (endForm [_] (end-form!))
  (varUsage [_ target from-ns source line column el ec]
    ;; when-let on the key, not let: var-key is nil only for a nil-ns var, which the
    ;; compiler should never resolve to here - but if one slips through, skip it
    ;; rather than write a nil key that would later NPE (namespace nil) in queries.
    (when-let [of (current-form)]
      (when-let [k (var-key target)]
        (add-fact! of [:usages k (span source line column el ec from-ns nil)])))
    nil)
  (varDef [_ v source line column el ec]
    (when-let [of (current-form)]
      (when-let [k (var-key v)]
        (add-fact! of [:defs k (span source line column el ec)])))
    nil)
  (localDef [_ binding name ns source line column el ec]
    (when-let [of (current-form)]
      (add-fact! of [:locals binding (local-span source line column el ec ns name)]))
    nil)
  (localUsage [_ binding ns source line column el ec]
    (when-let [of (current-form)]
      (add-fact! of [:local-use binding (local-span source line column el ec ns)]))
    nil)
  (keywordUsage [_ kw from-ns source line column el ec]
    (when-let [of (current-form)]
      (add-fact! of [:keyword-usages kw (span source line column el ec from-ns nil)]))
    nil)
  (classUsage [_ c from-ns source line column el ec]
    (when-let [of (current-form)]
      (add-fact! of [:class-usages (class-key c) (span source line column el ec from-ns nil)]))
    nil)
  (macroExpansion [_ macro from-ns source line column el ec record-usage?]
    (when-let [of (current-form)]
     (when-let [mk (var-key macro)]      ; skip a nil-ns macro var (see varUsage)
      (let [ns-sym (ns-name from-ns)]
        ;; Always record the compile-time edge (stale reload needs it even for
        ;; expansion-introduced calls); record the macro *usage* only for a
        ;; source-written call. The edge's fid (the form's own, filled in by
        ;; build-index) carries the expanding form's file, which the §9 cascade reads.
        (add-fact! of [:macro-dep ns-sym mk])
        (when record-usage?
          (add-fact! of [:usages mk (span source line column el ec from-ns true)])))))
    nil))

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
  ;; and pays nothing; when a caller (load-file!) has established it, this inherits
  ;; that binding so the caller sees every fid this analysis allocates, for rollback.
  (push-thread-bindings {Compiler/ANALYSIS_SINK (->AnalysisSink)
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
  elsewhere is not silently cleared."
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

(defn- file-mtime
  "The on-disk last-modified time of the file behind classpath resource `source`,
  or nil if it can't be resolved to a file (never loaded from a file, moved,
  deleted, or now behind a jar - a jar-entry URL has protocol \"jar\", not
  \"file\"). No namespace->path munging: the source path IS the resource path."
  [source]
  (when-let [u (io/resource source)]
    (when (= "file" (.getProtocol u))
      (.lastModified (resource->file u)))))

(defn- record-file-mtime! [source]
  (swap! model assoc-in [:file-mtime source] (file-mtime source))
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
  "Single-file analysis: retract `source`'s prior forms, then reload the file under
  the sink so the model is replaced cleanly - no accumulation. Removes forms deleted
  from source (their facts vanish with the form, and the derived indexes reflect it).
  Refreshes the stored source mtime. `source` is the classpath-relative source path
  the compiler records (e.g. \"app/util.clj\").

  Reloads via the file's resource (`load`), NOT require-by-namespace, so it handles
  a file that defines several namespaces (a require can't even name a file's second
  namespace) and keeps :source consistent with the cold analysis.

  Atomic: retract + reload + mtime update either all take effect or, if the reload
  throws (typically an edited source with a compile/syntax error), none do - the
  file is reverted to its prior state and the error re-thrown. The rollback reverts
  ONLY this file, via swap! (never reset!): it retracts this reload's created forms
  belonging to `source` and reinstates the file's prior forms from a pre-retract
  snapshot, so facts other threads committed meanwhile, and any OTHER file this
  reload happened to load fresh (an edit adding a new require), are preserved. The
  mtime is left unrefreshed on failure, so the file stays flagged stale and retries."
  [source]
  (check-resource-source! source)
  (let [snapshot @model
        old-fids (get-in snapshot [:source->forms source])]
    (binding [*created-fids* (atom [])]
      (try
        (retract-source* source)
        (run-analysis #(load-source! source))
        (record-file-mtime! source)
        (catch Throwable t
          (swap! model
                 (fn [m]
                   (let [mine (filter #(= source (:source (get-in m [:forms %]))) @*created-fids*)
                         m    (reduce retract-form m mine)]
                     (reduce (fn [m fid] (reinstate-form m snapshot fid)) m old-fids))))
          (throw t))))))

;; --- derived query indexes (built from :forms, cached) ---------------------

;; The by-entity indexes are a pure function of the stored form log, so they are
;; not maintained as the sink runs - they are rebuilt on demand and cached, keyed by
;; the IDENTITY of the :forms map. Any analysis / retraction produces a new :forms
;; value (immutable, structurally shared), so `identical?` cheaply detects that the
;; cache is stale; a quiescent model (no analysis in flight) is a straight cache hit.
;; The cache holds {:forms <the forms it was built from> :index <the built indexes>}.
(defonce ^:private index-cache (atom {:forms nil :index nil}))

(defn- build-index
  "Replay the per-form fact log into the by-entity query indexes. Forms are replayed
  in ascending fid (definition) order, so a redefinition - a later form defining the
  same var - naturally overwrites the earlier :defs entry: highest fid wins, which is
  what the old eager retract-on-redefine achieved. A var referenced but defined by no
  live form gets usages but no :defs entry, so `definition` returns nil for it (what
  the old incremental tombstone yielded). Pure function of `forms`.

  Returns {:usages :defs :keyword-usages :class-usages :locals :macro-deps}, each
  shaped exactly as the eagerly-maintained index was, so the queries are unchanged."
  [forms]
  (reduce
   (fn [idx fid]
     (reduce
      (fn [idx [op a b]]
        (case op
          :usages         (update-in idx [:usages a] (fnil conj #{}) b)
          :keyword-usages (update-in idx [:keyword-usages a] (fnil conj #{}) b)
          :class-usages   (update-in idx [:class-usages a] (fnil conj #{}) b)
          :defs           (assoc-in idx [:defs a] {:span b})
          ;; A local's def carries its full info (a LocalSpan record); project it to
          ;; the plain-map index entry and keep any :uses already gathered from
          ;; local-use facts earlier in this form (def normally precedes use).
          :locals         (update-in idx [:locals a]
                                     (fn [cur] (assoc (local->map b) :uses (get cur :uses #{}))))
          :local-use      (cond-> idx
                            (get-in idx [:locals a])
                            (update-in [:locals a :uses] (fnil conj #{}) (local->map b)))
          ;; a = defining ns-sym, b = macro qsym; the edge is stamped with fid (the
          ;; expanding form), so the §9 file cascade can find the expanding file.
          :macro-dep      (update-in idx [:macro-deps a b] (fnil conj #{}) fid)
          idx))
      idx (:facts (get forms fid))))
   {:usages {} :defs {} :keyword-usages {} :class-usages {} :locals {} :macro-deps {}}
   (sort (keys forms))))

(defn- derived
  "The cached by-entity indexes for model value `m` (deref the model once and pass
  it, so a query reads a single consistent snapshot). Rebuilds only when `m`'s :forms
  differ from the cached ones. The build is a pure function of :forms, so two threads
  racing to build the same :forms compute the same value - last writer wins, harmless."
  [m]
  (let [forms (:forms m)
        c     @index-cache]
    (if (identical? forms (:forms c))
      (:index c)
      (let [built (build-index forms)]
        (reset! index-cache {:forms forms :index built})
        built))))

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
  reloading it would only fail, so it is not flagged."
  []
  (let [m @model]
    (set (for [source (keys (:source->forms m))
               :let [now (file-mtime source)]
               :when (and (some? now) (not= now (get-in m [:file-mtime source])))]
           source))))

(defn- macro-owner
  "The macro-defining namespace symbol for a macro key (a qualified symbol)."
  [macro-key] (symbol (namespace macro-key)))

(defn- file-macro-graph
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

(defn stale-reload!
  "Macro-aware stale reload (design §9.2). Computes the stale set (changed files +
  their transitive macro-dependent files), reloads each via load-file! in macro-
  dependency (topological) order - macro-defining files before the files that
  re-expand them - and optionally prunes vanished vars (:prune true). Returns the
  final reload order (a vector of source paths).

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
  [& {:keys [prune]}]
  (let [dep-fn  (fn [g] (fn [s] (get g s #{})))
        reload! (fn [order]
                  (doseq [source order]
                    ;; Snapshot the file's def-vars (with their Var identities) BEFORE
                    ;; load-file! retracts them, so prune can tell which def forms
                    ;; vanished - and preserve any re-created afresh (see prune-file!).
                    (let [prior (when prune (file-def-var-snapshot @model source))]
                      (load-file! source)
                      (when prune (prune-file! source prior)))))
        stale   (stale-files)
        order1  (topo-order stale (dep-fn (file-macro-graph @model)))]
    (reload! order1)
    ;; Pass 1 completed the macro graph; re-derive the order from it.
    (let [df (dep-fn (file-macro-graph @model))]
      (if (topo-respected? order1 df)
        order1
        (let [order2 (topo-order stale df)]
          (reload! order2)
          order2)))))

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
