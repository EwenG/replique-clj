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
  demand and cached, one cache each (index / derived), so the sink does no index
  maintenance.

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
  (the compile-time cascade, §9), reload-files! (a given set, in dependency order),
  retract-file!. changed-files / deleted-files are what the disk says about the
  files already analysed. Query with find-usages (which includes the code in #_ and
  (comment ...), resolved without compiling it), definition,
  unused-*, file-namespaces, and what a lint is made of - file-facts, file-mtime,
  file-failure, version - etc. - find-usages/definition take a Var or its
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
;; rebuilt from the forms and cached, one cache per index (see `index`). The sink
;; does no index maintenance and no retract-on-redefine: a redefinition is just a later
;; form, and build-defs resolves "which form defines each var" by replaying forms in fid
;; (definition) order, so the highest-fid def wins. A var referenced but not defined
;; by any live form simply has no :defs entry - definition returns nil for it, which
;; is what the old incremental tombstone yielded.
;;
;; stored (write model - mutated only by the sink / drivers):
;;   :forms           {fid {:ns :source :line :column + one key per non-empty fact
;;                          category: :usages :defs :keyword-usages :class-usages
;;                          :locals :local-uses :macro-deps :invokes :warnings
;;                          :ns-specs :require-calls :member-usages :ref-usages
;;                          :local-refs :qualifiers, each a vector of facts}}
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
;; derived (built from :forms by `index`, each cached keyed by :forms identity):
;;   :usages          {qsym  #{span}}       qsym = fully-qualified var name (my.ns/foo)
;;                                          span = a Span record (compact, primitive
;;                                          int coords); the public queries normalise
;;                                          it to {:source :line :column :end-line
;;                                          :end-column :from-ns [:macro]} via span->map
;;   :defs            {qsym  {:span span}}   only vars a live form defines
;;   :locals          {binding {:ns :name ...span :uses #{span}}}
;;   :keyword-usages  {kw    #{span}}
;;   :class-usages    {class-name-string #{span}}  (keyed by name, not Class - see class-key)
;;   :member-usages   {[class-name member] #{span}}  a Java method, field or constructor
;;                                          ("new"), keyed by the class declaring it
;;   :ref-usages      {qsym  #{span}}       references that are NOWHERE - every span at
;;                                          line -1, read by the unused-* questions only
;;   :qualifiers      {sym   #{span}}       the namespace part of every qualified symbol
;;                                          the READER read, at the place it is written:
;;                                          what the text spells, which is all there is
;;                                          of an alias a macro ate or re-spelled
;;   :macro-deps      {ns-sym {macro-qsym #{fid}}}   compile-time edges (§9); each fid
;;                                          carries the expanding form's file (:source)
;;   :ns-usages       {lib   #{span-map}}   where each ns form or require call loads
;;                                          lib, read out of the :ns-specs and
;;                                          :require-calls facts (see find-namespace-usages)
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
(defn- libspec?
  "clojure.core/libspec?, and it has to be the same test: it is what tells one lib
  and its options from a prefix and the specs under it, and a vector whose second
  element is a keyword - or which has none - is the first of those."
  [x]
  (or (symbol? x)
      (and (vector? x) (or (nil? (second x)) (keyword? (second x))))))

(defn- opts-of
  "The trailing key/value options of a libspec, as a map.

  In pairs rather than through `apply hash-map', because this reads a form somebody
  is still writing: an option with no value yet is an odd count, and a walk that
  threw on one would fail the macroexpansion of the `ns' form it is looking at -
  turning a half-typed require into a file that will not load."
  [more]
  (into {} (map vec) (partition 2 more)))

(defn- spec-refers
  "The [qualified-name written-symbol] pairs the libspec `spec' writes, under the
  prefix `prefix' - what its :refer, its :only and the keys of its :rename name.

  A :rename's keys are in because they are the var's name as this file writes it:
  {twice t2} renames what `twice' means here, and a rename of the var itself has
  to replace that key. Its values are not - they are the new name, and no var
  anywhere is called that.

  :refer :all names nothing in particular and is left alone, as a plain require is:
  what it writes is the namespace, not any of the names in it."
  [prefix spec]
  (cond
    (symbol? spec) nil

    (libspec? spec)
    (let [lib     (if prefix (symbol (str prefix \. (first spec))) (first spec))
          opts    (opts-of (next spec))
          named   (concat (when (sequential? (:refer opts)) (:refer opts))
                          (when (sequential? (:only opts)) (:only opts))
                          (when (map? (:rename opts)) (keys (:rename opts))))]
      (for [written named :when (simple-symbol? written)]
        [(symbol (name lib) (name written)) written]))

    (sequential? spec)
    (let [prefix (if prefix (symbol (str prefix \. (first spec))) (first spec))]
      (mapcat #(spec-refers prefix %) (next spec)))))

(defn- ns-form-refers
  "The [qualified-name written-symbol] pairs an `ns' form writes in its clauses.

  Nothing is resolved: the namespaces these name are not loaded yet - this form is
  what loads them - so a name is qualified by the libspec it is written under and
  by nothing else. Which is also why a name that turns out not to be there is
  recorded all the same: the form is about to throw over it, and the file it is in
  never commits.

  :refer-clojure's :only and :rename name vars of clojure.core, which is the one
  clause that writes a namespace nowhere in itself."
  [form]
  (let [more (->> (next form) next        ; past the name
                  (drop-while string?)    ; past the docstring
                  (drop-while map?))]     ; past the attribute map
    (mapcat (fn [clause]
              (when (sequential? clause)
                (case (first clause)
                  (:require :use) (mapcat #(spec-refers nil %) (next clause))
                  :refer-clojure  (spec-refers nil (vec (cons 'clojure.core (next clause))))
                  nil)))
            more)))

(defn- written-span
  "The span the reader put on a symbol or a collection, or nil."
  [x]
  (let [m (meta x)]
    (when (:line m) (select-keys m [:line :column :end-line :end-column]))))

(defn- string-lib-span
  "Where the string lib `s' written first in the libspec vector `v' is: a string
  carries no metadata, and is written right after the vector's bracket."
  [v ^String s]
  (when-let [{:keys [line column]} (written-span v)]
    {:line line :column (inc column) :end-line line
     :end-column (+ column 1 (count (pr-str s)))}))

(defn ns-specs
  "What the clauses of the ns form `form' write, positioned where they write it -
  the form as the reader read it, with the positions the analysis has it record:

    {:requires [{:lib sym-or-string :clause :require :at span
                 :as sym :as-at span
                 :refer [[sym span]] :refer-macros [[sym span]]
                 :renamed {original new} :refer-all? true}]
     :imports  [{:name short-sym :class \"full.Name\" :at span}]}

  Of :require, :use, :require-macros and :use-macros - ClojureScript's two as
  well, so that its model reads its ns forms with this - and of :import. Prefix
  lists are read out into the libraries they name. A key is absent where the spec
  does not write it; a span is nil where the reader gave the name none.

  Nothing is resolved: it is what the form SAYS, which is the one thing a
  namespace's live state cannot answer - it knows an alias is unused, and not
  where the alias was written."
  [form]
  (let [spec (fn [clause lib-form]
               (cond
                 (or (symbol? lib-form) (string? lib-form))
                 [{:lib lib-form :at (written-span lib-form) :clause clause}]

                 (vector? lib-form)
                 (let [[lib & more] lib-form
                       opts (opts-of more)
                       refer (:refer opts)
                       rename (:rename opts)]
                   [(cond-> {:lib lib
                             :at (if (string? lib) (string-lib-span lib-form lib) (written-span lib))
                             :clause clause}
                      (symbol? (:as opts)) (assoc :as (:as opts) :as-at (written-span (:as opts)))
                      (sequential? refer) (assoc :refer (vec (for [r refer :when (symbol? r)]
                                                               [r (written-span r)])))
                      (= :all refer) (assoc :refer-all? true)
                      (sequential? (:refer-macros opts))
                      (assoc :refer-macros (vec (for [r (:refer-macros opts) :when (symbol? r)]
                                                  [r (written-span r)])))
                      (map? rename) (assoc :renamed rename))])

                 :else nil))
        prefixed (fn [clause lib-form]
                   (if (and (seq? lib-form) (symbol? (first lib-form)))
                     (let [prefix (first lib-form)
                           join #(symbol (str prefix "." %))]
                       (mapcat (fn [x]
                                 (spec clause
                                       (cond (symbol? x) (with-meta (join x) (meta x))
                                             (and (vector? x) (symbol? (first x)))
                                             (with-meta (into [(with-meta (join (first x))
                                                                 (meta (first x)))]
                                                              (rest x))
                                               (meta x))
                                             :else nil)))
                               (rest lib-form)))
                     (spec clause lib-form)))
        clauses (filter seq? (drop 2 form))]
    {:requires (vec (for [clause clauses
                          :when (#{:require :use :require-macros :use-macros} (first clause))
                          lib-form (rest clause)
                          :when (not (keyword? lib-form))
                          lib (prefixed (first clause) lib-form)
                          :when lib]
                      lib))
     :imports (vec (for [clause clauses
                         :when (= :import (first clause))
                         spec (rest clause)
                         entry (cond
                                 (symbol? spec)
                                 (let [n (str spec)]
                                   [{:name (symbol (subs n (inc (.lastIndexOf n "."))))
                                     :class n :at (written-span spec)}])

                                 (and (sequential? spec) (symbol? (first spec)))
                                 (for [c (rest spec) :when (symbol? c)]
                                   {:name c :class (str (first spec) "." c)
                                    :at (written-span c)})

                                 :else nil)]
                     entry))}))

(defn require-call-specs
  "What a call of `require` or `use` the source wrote says it loads, positioned -
  `ns-specs`' :requires, read off the call's quoted arguments as the ns form's
  clause would read them. `f` is which of the two was called, and is the :clause.

  Only what is written as a literal: (require 'my.lib) and (require '[my.lib :as l])
  name a library, and (require (symbol s)) names none the source can point at, so
  it is skipped - as are the flags, :reload and :verbose, which name nothing."
  [form f]
  (let [libs (keep (fn [arg]
                     (when (and (seq? arg) (= 'quote (first arg)) (next arg))
                       (second arg)))
                   (rest form))]
    (when (seq libs)
      (:requires (ns-specs (list 'ns 'call (cons (keyword (name f)) libs)))))))

(defn requiring-resolve-names
  "What a call of `requiring-resolve` the source wrote names, positioned: for each
  var it names as a literal - (requiring-resolve 'my.lib/f) - {:var my.lib/f
  :written the symbol as read :at its span :lib {:lib my.lib :at the span of the
  namespace part :clause :requiring-resolve}}. The call loads the namespace and
  resolves the var, and is a use of each; a name the source computes is neither
  and is skipped, as require-call-specs skips one."
  [form]
  (for [arg (rest form)
        :when (and (seq? arg) (= 'quote (first arg)) (next arg))
        :let [sym (second arg)
              at (when (qualified-symbol? sym) (written-span sym))]
        :when at]
    {:var (symbol (namespace sym) (name sym))
     :written sym
     :at at
     :lib {:lib (symbol (namespace sym))
           :at (assoc at :end-line (:line at)
                      :end-column (+ (long (:column at)) (count (namespace sym))))
           :clause :requiring-resolve}}))

;; A record with primitive int coordinates costs ~1/7th the bytes of the equivalent
;; array-map (measured), chiefly by not boxing the four coordinates into Integers.
;; The four coordinates are always ints at the sink boundary (IAnalysisSink passes
;; them as int); an absent end-line/end-column arrives non-nat and is stored as -1.
;; from-ns is the referencing namespace (nil for a def); macro is true for a
;; macro-call usage, else nil; dead is :discard or :comment for a usage in code the
;; program does not run (see dead-facts), else nil; declaration is :refer or :import
;; for the name an ns form writes in a clause rather than a use of it (see
;; referUsage), :declare for a def that only declares its name (`declare'), else
;; nil. written is the symbol a usage was spelled by, without its metadata - but
;; only where that is not the var's own name, unqualified: `str/join', a renamed
;; refer. The common spelling is implied by the key, and costs nothing. var-form is
;; true for a usage through the `var' special form - #'x, or a symbol a macro
;; var-ized - else nil. role is what the name is written as a part of, where that is
;; more than a use: :defmethod for the multimethod a defmethod adds a method to,
;; :destructuring for a keyword a :keys writes as the local it binds,
;; :requiring-resolve for a var a requiring-resolve names by its quoted name - else
;; nil.
;; Locals use their own record (LocalSpan) below.
;;
;; `entity` is the thing this span is ABOUT - the var key for a usage/def, the Keyword
;; for a keyword usage, the class-name string for a class usage. Carrying it on the
;; span makes a fact a SINGLE object: the form's per-category lists hold bare spans, so
;; there is no [op a b] tuple wrapper per fact (one fewer allocation each, and one
;; fewer object retained in the :forms log for the life of the code). span->map never
;; exposes it, so the public span shape is unchanged.
(defrecord Span [entity source ^int line ^int column ^int end-line ^int end-column from-ns macro dead
                 declaration written var-form role])

(defn- norm-end [x] (if (nat-int? x) (int x) -1))

(defn- span
  ([entity source line column el ec] (span entity source line column el ec nil nil))
  ([entity source line column el ec from-ns macro]
   (span entity source line column el ec from-ns macro nil))
  ([entity source line column el ec from-ns macro dead]
   (span entity source line column el ec from-ns macro dead nil))
  ([entity source line column el ec from-ns macro dead declaration]
   (span entity source line column el ec from-ns macro dead declaration nil nil))
  ([entity source line column el ec from-ns macro dead declaration written var-form]
   (span entity source line column el ec from-ns macro dead declaration written var-form nil))
  ([entity source line column el ec from-ns macro dead declaration written var-form role]
   (->Span entity source (int line) (int column) (norm-end el) (norm-end ec)
           from-ns (when macro true) dead declaration written (when var-form true) role)))

(defn- written-as
  "The spelling `written' of the var keyed `k' worth keeping on its span: nil
  where it is the var's own name, unqualified, which the key already says - the
  common case, so the common case allocates nothing - and the symbol without its
  metadata otherwise."
  [k ^clojure.lang.Symbol written]
  (when (and written
             (or (.getNamespace written) (not= (.getName written) (name k))))
    (with-meta written nil)))

;; A local binding's def/use site. Locals are numerous too (every fn-arg and
;; let-binding), so they get the same lightweight-record treatment as Span rather
;; than a map built via merge: one allocation per local, primitive int coordinates,
;; no boxing. `binding` is the opaque identity token linking a def to its uses (the
;; entity key, carried on the span for the same one-object-per-fact reason as Span).
;; `lns` is the owning namespace; `lname` the binding's source name (present for a def,
;; nil for a use). Fields are named to avoid shadowing clojure.core/ns and /name;
;; build-locals (local->map) projects them to the public :ns/:name keys, so the query
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

;; A call the source wrote of a var, with how many arguments it was given
;; (IAnalysisSink.invokeUsage). As numerous as the calls in a file, so a record with
;; primitive coordinates like Span; `entity` is the var key of what is called and
;; `from-ns` the namespace the call is written in.
(defrecord Invoke [entity source ^int line ^int column ^int end-line ^int end-column from-ns
                   ^int argc])

(defn- span->map
  "Normalise a Span record to the documented plain-map span shape, for the public
  query API - so results carry no record type and compare = to map literals. Omits
  an absent end-line/end-column (stored as -1) and a nil from-ns/macro/dead/
  declaration/written/var-form/role, exactly reproducing the map the sink used to build."
  [s]
  (cond-> {:source (:source s) :line (:line s) :column (:column s)}
    (nat-int? (:end-line s))   (assoc :end-line (:end-line s))
    (nat-int? (:end-column s)) (assoc :end-column (:end-column s))
    (:from-ns s)               (assoc :from-ns (:from-ns s))
    (:macro s)                 (assoc :macro true)
    (:dead s)                  (assoc :dead (:dead s))
    (:declaration s)           (assoc :declaration (:declaration s))
    (:written s)               (assoc :written (:written s))
    (:var-form s)              (assoc :var-form true)
    (:role s)                  (assoc :role (:role s))))

(defn- spans->maps [spans]
  (when spans (into #{} (map span->map) spans)))

(defn- local->map
  "Normalise a LocalSpan record to the plain-map local shape build-locals files in the
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
;; current :next-fid. `dead` collects the file's dead code (deadForm) until endFile
;; resolves it - see dead-facts.
(deftype FileFrame [source ^java.util.ArrayList buffer ^longs counter
                    ^java.util.ArrayList dead])

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
(def ^:private ^:const CAT-INVOKES  7)
(def ^:private ^:const CAT-WARNINGS 8)
(def ^:private ^:const CAT-NSSPECS  9)
(def ^:private ^:const CAT-REQCALLS 10)
(def ^:private ^:const CAT-MEMBERS  11)
;; A REFERENCE THAT IS NOWHERE - see the sink's varUsage/localUsage. The two
;; categories of their own, rather than the position sentinel loose in :usages and
;; :local-uses, so that everything answering WHERE keeps reading exactly what it
;; read before and cannot be given a place that is not one. Only the unused-*
;; questions look here, and they ask whether a thing is referenced at all.
(def ^:private ^:const CAT-REFS     12)
(def ^:private ^:const CAT-LOCALREFS 13)
;; WHAT THE TEXT SPELLS, from the reader and not from the compiler: the namespace
;; part of every qualified symbol read. Its own category because it is its own
;; question - a name's prefix, resolved against nothing - and because the compiler
;; answers it for no symbol a macro eats or rewrites. See the sink's qualifierUsage.
(def ^:private ^:const CAT-QUALIFIERS 14)
(def ^:private ^:const N-CATS       15)

;; The model key each category is stored under on a committed form entry, indexed by
;; the constants above.
(def ^:private cat-keys
  [:usages :defs :keyword-usages :class-usages :locals :local-uses :macro-deps
   :invokes :warnings :ns-specs :require-calls :member-usages
   :ref-usages :local-refs :qualifiers])

;; An open form is buffered in a thread-local mutable holder, NOT written to the shared
;; model fact-by-fact. Facts accumulate in per-category ArrayLists (`cats`, allocated
;; lazily - most forms touch only one or two categories) and the form's position is
;; corrected in place (form-start! fires repeatedly, last wins); at end-form! the
;; finished form is handed to its file `frame`'s buffer. So the sink never touches the
;; shared atom - not per fact, not per form. `pos` is [line column]; `seq` is the form's
;; begin-order rank within its file, used to assign a fid = base + seq at commit, so
;; build-defs still replays a file's forms in begin order.
(deftype OpenForm [^long seq ^FileFrame frame ^longs pos ^objects cats])

(defn- current-frame ^FileFrame [] (when-let [s *file-stack*] (peek @s)))
(defn- current-form  ^OpenForm  [] (when-let [s *form-stack*] (peek @s)))

;; The sink's one mutation while a form is open: append a fact to the open form's list
;; for category `cat`, creating that list on first use. The fact is a single object that
;; carries its own entity key (Span/LocalSpan/MacroDep), so there is no tuple wrapper.
;; No model touch, no index maintenance - the by-entity indexes are derived on read
;; (see `index`). nil holder (no form open) is a no-op; see the sink for why.
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
;; the query indexes are a pure function of the surviving forms (see `index`), so a
;; var whose last defining form is gone stops appearing in :defs automatically, and
;; one still referenced elsewhere keeps its usages because those live on other forms.
(defn- retract-form [m fid]
  (if-let [fe (get-in m [:forms fid])]
    (let [m (update m :forms dissoc fid)]
      (if-let [src (:source fe)]
        (-> m (update-in [:source->forms src] disj fid) (drop-empty :source->forms src))
        m))
    m))

;; --- dead code: #_ and (comment ...) ---------------------------------------

;; Code written in a file that the program does not run: the form a #_ discards, and
;; the body of a (comment ...). The compiler never compiles it, so none of the events
;; above report what it names - but it is still code somebody wrote, reads, and runs
;; at a REPL, so find-usages and a rename have to see it.
;;
;; It is RESOLVED, not compiled. The sink is handed the form whole (deadForm), and at
;; the end of the file each symbol the reader wrote in it is looked up in the
;; namespace it was written in - the first thing the compiler would do, without the
;; rest: no macroexpansion, no eval, nothing interned, no class initialised, and no
;; error from code that no longer compiles, which dead code often is. At the END of
;; the file, because a rich comment block uses what its file defines and requires,
;; and much of that is written after it.
;;
;; Macros are not expanded, so which symbols are locals is decided by knowing the
;; binding forms of clojure.core by name (let, fn, loop, for, letfn, deftype, ...)
;; and destructuring. That is exact for them and a guess for any other macro that
;; binds a name: a name it binds that also names a var or a class is recorded as a
;; use of it. The locals of the LIVE code around a dead form - a #_ or a comment
;; inside a defn - are taken from the top-level form's own local facts: a name the
;; form bound before the dead symbol is taken to be that local.
;;
;; What comes out is var and class usages, marked :dead :discard or :dead :comment,
;; filed on one extra form per file - and the libraries a call of require or use in
;; it loads (:require-calls), marked the same way, since a comment block that
;; requires what it plays with is the commonest dead code there is. Nothing else: no defs (a def in a comment defines
;; nothing, and must not keep a deleted var from being pruned), no locals, no macro
;; edges, no part in the compile graphs or the reload order. Whether a query counts
;; them is up to it - see counts-as-use?.

(defn- pattern-locals
  "What binding pattern `pat` binds, as [names code]: the local names it introduces,
  and the forms inside it that are code - the defaults of an :or."
  [pat]
  (let [names (volatile! #{})
        code  (volatile! [])]
    (letfn [(walk [p]
              (cond
                (symbol? p) (when-not (= '& p) (vswap! names conj (name p)))
                (vector? p) (run! walk p)
                (map? p)
                (doseq [[k v] p]
                  (cond
                    (= :as k) (walk v)
                    (= :or k) (when (map? v) (vswap! code into (vals v)))
                    (and (keyword? k) (#{"keys" "syms" "strs"} (name k)))
                    (doseq [x v :when (or (symbol? x) (keyword? x))]
                      (vswap! names conj (name x)))
                    :else (walk k)))))]
      (walk pat))
    [@names @code]))

(declare walk-dead)

(defn- walk-all [forms env]
  (doseq [f forms] (walk-dead f env)))

(defn- with-locals [env names]
  (update env :locals into names))

(defn- bind-pairs
  "Walk a binding vector, each init seeing the names bound before it; the env its
  body sees. `comprehension?` for the :let / :when / :while of a for or a doseq."
  [bvec env comprehension?]
  (reduce (fn [env [pat init]]
            (cond
              (and comprehension? (= :let pat) (vector? init)) (bind-pairs init env false)
              (and comprehension? (keyword? pat))              (do (walk-dead init env) env)
              :else (let [[names code] (pattern-locals pat)
                          _   (walk-dead init env)
                          env (with-locals env names)]
                      (walk-all code env)
                      env)))
          env (partition 2 bvec)))

(defn- walk-let [args env comprehension?]
  (let [[bvec & body] args]
    (if (vector? bvec)
      (walk-all body (bind-pairs bvec env comprehension?))
      (walk-all args env))))

(defn- walk-method
  "([params] body...) - one arity of a fn, or a method of a deftype or a reify."
  [[params & body] env]
  (let [[names code] (pattern-locals params)
        env          (with-locals env names)]
    (walk-all code env)
    (walk-all body env)))

(defn- walk-fn-tail
  "What follows a fn's name: one arity, or several in lists."
  [tail env]
  (if (vector? (first tail))
    (walk-method tail env)
    (doseq [m tail]
      (if (and (seq? m) (vector? (first m)))
        (walk-method m env)
        (walk-dead m env)))))

(defn- walk-named-fn-tail
  "A fn tail that may start with the fn's own name, which is a local in it."
  [tail env]
  (if (symbol? (first tail))
    (walk-fn-tail (rest tail) (with-locals env [(name (first tail))]))
    (walk-fn-tail tail env)))

(defn- walk-impls
  "The specs of a deftype, a reify, an extend-type... A method - (name [params]
  body), or (name ([params] body)...) - binds its params, and its name is the method
  it implements rather than a reference. Anything else is walked."
  [specs env]
  (doseq [x specs]
    (if (and (seq? x) (symbol? (first x))
             (let [y (second x)] (or (vector? y) (and (seq? y) (vector? (first y))))))
      (walk-fn-tail (rest x) env)
      (walk-dead x env))))

(defn- class-non-loading
  "The class named `n`, or nil - loaded if it must be, never initialised."
  [^String n]
  (try (RT/classForNameNonLoading n) (catch Throwable _ nil)))

(defn- dead-class
  "The class unqualified symbol `sym` names in `ns`: imported, or fully qualified."
  [^clojure.lang.Namespace ns sym]
  (let [o (.getMapping ns sym)]
    (cond (class? o)                   o
          (.contains (name sym) ".")   (class-non-loading (name sym))
          :else                        nil)))

(defn- dead-target
  "What `sym` names in `ns` - a Var, a Class, or nil - the way the compiler would
  resolve it, but touching nothing: no var interned, no class initialised, and no
  answer rather than an error for a name that resolves to nothing.

  `alias/name` and `ns.name/name` are vars; `Class/member` is the class, as the
  compiler records it; `Foo.` is the class it constructs; `.method` is nothing."
  [^clojure.lang.Namespace ns sym]
  (let [n (name sym)]
    (if-let [q (namespace sym)]
      (let [qs (symbol q)]
        (if-let [^clojure.lang.Namespace target (or (.lookupAlias ns qs) (find-ns qs))]
          (.findInternedVar target (symbol n))
          (dead-class ns qs)))
      (let [o (.getMapping ns sym)]
        (cond
          (or (var? o) (class? o)) o
          (.startsWith n ".")      nil
          (.endsWith n ".")        (dead-class ns (symbol (subs n 0 (dec (count n)))))
          (.contains n ".")        (class-non-loading n)
          :else                    nil)))))

(defn- jvm-target
  "dead-target in namespace `ns`, as the walk's :target - a head is resolved no
  differently from any other symbol on the JVM."
  [ns]
  (fn [sym _head?] (dead-target ns sym)))

(defn- jvm-op
  "The walk's :op on the JVM: the var-key of the macro or function a head names."
  [ns]
  (fn [sym] (let [t (dead-target ns sym)] (when (var? t) (var-key t)))))

(defn- local?
  "Is `sym` a local where it is written: bound in the dead code around it, or -
  going by the top-level form's own local facts - by the live code before it."
  [env sym]
  (and (nil? (namespace sym))
       (let [n (name sym)]
         (or (contains? (:locals env) n)
             (when-let [[l c] (get (:outer env) n)]
               (let [m (meta sym) sl (:line m) sc (:column m)]
                 (and sl sc (or (> sl l) (and (= sl l) (> sc c))))))))))

(defn- dead-symbol! [sym env head?]
  (when (and (:line (meta sym)) (not (local? env sym)))
    (when-let [t ((:target env) sym head?)]
      ((:emit env) t sym))))

(defn- walk-dead-call [form env]
  (let [[head & args] form
        op (when (and (symbol? head) (not (local? env head)))
             (if (special-symbol? head)
               head
               ((:op env) head)))]
    (when-let [on-call (when op (:on-call env))]
      (on-call op form))
    (if (symbol? head)
      (when-not (special-symbol? head) (dead-symbol! head env true))
      (walk-dead head env))
    (case op
      (quote clojure.core/ns clojure.core/defprotocol clojure.core/definterface
             clojure.core/gen-class clojure.core/gen-interface) nil
      (let* loop* clojure.core/let clojure.core/loop clojure.core/when-let
            clojure.core/if-let clojure.core/when-some clojure.core/if-some
            clojure.core/when-first clojure.core/with-open clojure.core/dotimes
            clojure.core/with-local-vars)
      (walk-let args env false)
      (clojure.core/for clojure.core/doseq) (walk-let args env true)
      (fn* clojure.core/fn) (walk-named-fn-tail args env)
      (clojure.core/defn clojure.core/defn- clojure.core/defmacro)
      (walk-fn-tail (drop-while #(or (string? %) (map? %)) (rest args)) env)
      def (walk-all (rest args) env)
      clojure.core/defmethod (do (walk-dead (let [m (first args)]
                                              ;; as clojure.core/defmethod marks it
                                              (cond-> m
                                                (symbol? m)
                                                (vary-meta assoc :clojure.analysis/defmethod true)))
                                            env)
                                 (walk-dead (second args) env)
                                 (walk-named-fn-tail (drop 2 args) env))
      (letfn* clojure.core/letfn)
      (let [[specs & body] args]
        (if (vector? specs)
          (let [star? (= 'letfn* op)
                names (map #(name (if (seq? %) (first %) %))
                           (if star? (take-nth 2 specs) specs))
                env   (with-locals env names)]
            (if star?
              (walk-all (take-nth 2 (rest specs)) env)
              (doseq [s specs :when (seq? s)] (walk-fn-tail (rest s) env)))
            (walk-all body env))
          (walk-all args env)))
      catch (let [[c e & body] args]
              (walk-dead c env)
              (walk-all body (cond-> env (symbol? e) (with-locals [(name e)]))))
      . (let [[target member & more] args]
          (walk-dead target env)
          (if (seq? member) (walk-all (rest member) env) (walk-all more env)))
      clojure.core/case (let [[e & clauses] args]
                          (walk-dead e env)
                          (doseq [[test then :as clause] (partition-all 2 clauses)]
                            (if (= 1 (count clause))
                              (walk-dead test env)
                              (walk-dead then env))))
      (clojure.core/deftype clojure.core/defrecord)
      (let [[_ fields & specs] args]
        (walk-impls specs (with-locals env (first (pattern-locals fields)))))
      (clojure.core/reify clojure.core/extend-type clojure.core/extend-protocol)
      (walk-impls args env)
      clojure.core/proxy (walk-impls args (with-locals env ["this"]))
      (walk-all args env))))

(defn- walk-dead
  "Walk dead `form`, calling (:emit env) with what each symbol in it names."
  [form env]
  (cond
    (symbol? form)                  (dead-symbol! form env false)
    (seq? form)                     (when (seq form) (walk-dead-call form env))
    (map? form)                     (doseq [[k v] form] (walk-dead k env) (walk-dead v env))
    (or (vector? form) (set? form)) (walk-all form env)
    :else                           nil))

(defn walk-dead-code
  "Walk `form`, code the program does not run, calling (emit target sym) for each
  symbol written in it that names something - see the dead code section.

  The walk is this namespace's; what a name means is the caller's, so that
  clojure.cljs.analysis walks ClojureScript with it, resolving in its own world:

    :target  (fn [sym head?] ...) what `sym` names, or nil. head? when it is the
             head of a call, where ClojureScript prefers a macro to a var
    :op      (fn [sym] ...) the name of the macro or function a head names, as a
             symbol - clojure.core/let for the binding forms this walk knows - or
             nil
    :outer   {name [line column]}, the locals the live code around `form` binds,
             each where it is first bound (locals-at), or nil
    :on-call (fn [op form] ...) called with each call in it whose head names
             something, `op` what :op named - for what a call says as a whole
             rather than symbol by symbol, a (require 'my.lib) - or nil

  A form that cannot be walked throws; the caller skips it."
  [form {:keys [target op emit outer on-call]}]
  (walk-dead form {:locals #{} :outer outer :target target :op op :emit emit
                   :on-call on-call}))

(defn dead-body
  "What of dead `form` of `kind` is dead: all of a #_, and the arguments of a
  (comment ...) - the comment call itself is live code, compiled and recorded as
  such. As one form walk-dead-code can take."
  [form kind]
  (if (and (= :comment kind) (seq? form)) (vec (rest form)) form))

(defn locals-at
  "{name [line column]} of the named locals among `local-spans` - LocalSpan-shaped:
  :lname (a string or a symbol) :line :column - each at the first place it is
  bound. What the walk reads the live code's scope off (walk-dead-code's :outer)."
  [local-spans]
  (reduce (fn [acc s]
            (let [n (some-> (:lname s) name) p [(:line s) (:column s)]]
              (if (and n (neg? (compare p (get acc n [Long/MAX_VALUE 0]))))
                (assoc acc n p)
                acc)))
          {} local-spans))

(defn- outer-locals
  "locals-at of the locals open form `of` binds in its live code."
  [^OpenForm of]
  (locals-at (aget ^objects (.cats of) CAT-LOCALS)))

(defn- dead-kind-at
  "The kind of the innermost of `spans` - [kind [line column end-line end-column]]
  - that holds position line:column, or nil. The end is exclusive."
  [spans line column]
  (let [at [line column]]
    (some->> spans
             (filter (fn [[_ [l c el ec]]]
                       (and (not (neg? (compare at [l c])))
                            (neg? (compare at [el ec])))))
             seq
             (apply max-key (fn [[_ [l c]]] (+ (* 100000 (long l)) (long c))))
             first)))

(defn mark-dead!
  "Mark the facts in `facts` - an ArrayList of Span-shaped records, with :line
  :column and a :dead field - that lie inside one of `spans` as dead code of that
  span's kind (dead-kind-at). For what the READER reports inside a #_ or a comment
  while it reads it: a keyword, a syntax-quoted reference. The compiler reports
  nothing from dead code, so everything inside a dead span is one of those."
  [^java.util.ArrayList facts spans]
  (when (and facts (seq spans))
    (dotimes [i (.size facts)]
      (let [f (.get facts i)]
        (when-let [kind (dead-kind-at spans (:line f) (:column f))]
          (.set facts i (assoc f :dead kind))))))
  nil)

(defn- close-dead!
  "Open form `of` has ended: give the dead code written in it the locals it bound -
  its local facts are complete only now, as a #_ is read before the form around it
  is compiled - and mark dead what the reader reported inside it (mark-dead!)."
  [^OpenForm of]
  (let [^java.util.ArrayList dead (.dead ^FileFrame (.frame of))
        outer (delay (outer-locals of))
        spans (java.util.ArrayList.)]
    (dotimes [i (.size dead)]
      (let [d (.get dead i)]
        (when (identical? of (:of d))
          (when-let [sp (:span d)] (.add spans [(:kind d) sp]))
          (.set dead i (-> d (dissoc :of) (assoc :outer @outer))))))
    (when-not (.isEmpty spans)
      (let [^objects cats (.cats of)
            spans (vec spans)]
        (doseq [cat [CAT-USAGES CAT-CLASSES CAT-KEYWORDS CAT-QUALIFIERS]]
          (mark-dead! (aget cats cat) spans)))))
  nil)

(defn- commit-dead!
  "Resolve the dead code of the file frame `fr` - it has loaded to the end, so
  everything it defines and requires is there - and add what it names to the frame's
  buffer, as one more form. A dead form that cannot be walked is skipped: it is the
  program's to be wrong, never the load's."
  [^FileFrame fr]
  (let [^java.util.ArrayList dead (.dead fr)]
    (when-not (.isEmpty dead)
      (let [source  (.source fr)
            uses    (java.util.ArrayList.)
            classes (java.util.ArrayList.)
            reqs    (java.util.ArrayList.)]
        (doseq [{:keys [form kind ns outer]} dead]
          (let [emit (fn [t sym]
                       (let [m  (meta sym) line (:line m) col (:column m)
                             el (:end-line m -1) ec (:end-column m -1)]
                         (when col
                           (if (var? t)
                             (when-let [k (var-key t)]
                               (.add uses (span k source line col el ec ns
                                                (:macro (meta t)) kind nil
                                                (written-as k sym) nil
                                                (when (:clojure.analysis/defmethod m)
                                                  :defmethod))))
                             ;; Foo. records Foo, as the compiler does
                             (let [ec (if (and (nil? (namespace sym))
                                               (.endsWith (name sym) ".")
                                               (pos? (long ec)))
                                        (dec (long ec))
                                        ec)]
                               (.add classes (span (class-key t) source line col el ec
                                                   ns nil kind)))))))]
            (try
              ;; a comment's body: the comment call itself is live, and recorded
              (walk-dead-code (dead-body form kind)
                              {:target (jvm-target ns) :op (jvm-op ns)
                               :outer outer :emit emit
                               ;; requireCall's facts, which the compiler reports
                               ;; of live code only
                               :on-call
                               (fn [op form]
                                 (case op
                                   (clojure.core/require clojure.core/use)
                                   (when-let [rs (seq (require-call-specs
                                                       form (symbol (name op))))]
                                     (.add reqs {:ns (ns-name ns)
                                                 :requires (mapv #(assoc % :dead kind) rs)}))

                                   clojure.core/requiring-resolve
                                   (when-let [named (seq (requiring-resolve-names form))]
                                     (doseq [{k :var :keys [written at]} named]
                                       (.add uses (span k source (:line at) (:column at)
                                                        (:end-line at) (:end-column at) ns
                                                        nil kind nil (written-as k written)
                                                        nil :requiring-resolve)))
                                     (.add reqs {:ns (ns-name ns)
                                                 :requires (mapv #(assoc (:lib %) :dead kind)
                                                                 named)}))
                                   nil))})
              (catch Exception _ nil))))
        (when-not (and (.isEmpty uses) (.isEmpty classes) (.isEmpty reqs))
          (let [^longs c (.counter fr)
                seq      (aget c 0)
                ;; the call's head is a use of require, so a require call is never
                ;; alone - but a form needs a position whatever it holds
                s1       (or (first (concat uses classes))
                             (:at (first (:requires (first reqs)))))]
            (aset c 0 (inc seq))
            (.add ^java.util.ArrayList (.buffer fr)
                  (cond-> {:seq seq :source source :line (:line s1) :column (:column s1)
                           :ns nil}
                    (not (.isEmpty uses))    (assoc :usages (vec uses))
                    (not (.isEmpty classes)) (assoc :class-usages (vec classes))
                    (not (.isEmpty reqs))    (assoc :require-calls (vec reqs))))))))
    nil))

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

(defn- def-echo?
  "Is `s` a usage sitting exactly on one of `defs`? A macro that defines a name
  often writes that same symbol again in its expansion - `defmacro' hands the
  name to `(. (var name) (setMacro))' and returns `(var name)' - and the copy
  carries the reader's position, so it passes the capture rule and arrives as a
  reference to the var at the very place the var is being defined. It is the
  definition seen twice, not a use.

  Only a var-quote can produce one: a def's name never reaches `analyzeSymbol'.
  `clojure.cljs.analysis' has the same rule for the same reason, and had it
  first - there a `deftype' expansion echoes the type's name."
  [defs ^Span s]
  (contains? defs [(.entity s) (.line s) (.column s)]))

(defn- drop-def-echoes!
  "Remove from this form's usages the ones that are its own defs seen twice.

  Per FORM, which is the scope that makes it safe: a var-quote of a name defined
  somewhere else in the same file is a real reference and is kept, and so is one
  written on the same line as a def of a DIFFERENT var. What is dropped is a
  usage of the very var this form defines, at the very position the def is
  recorded at."
  [^objects cats]
  (let [^java.util.ArrayList uses (aget cats CAT-USAGES)
        ^java.util.ArrayList defs (aget cats CAT-DEFS)]
    (when (and uses defs (not (.isEmpty uses)) (not (.isEmpty defs)))
      (let [at (into #{} (map (fn [^Span s] [(.entity s) (.line s) (.column s)])) defs)]
        (.removeIf uses (reify java.util.function.Predicate
                          (test [_ x] (boolean (def-echo? at x))))))))
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
      (close-dead! of)
      (let [^objects cats (.cats of)]
        (drop-def-echoes! cats)
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
                 (-> (assoc m :forms forms :source->forms s->f
                            :next-fid (+ base (long begin-count)))
                     ;; it loaded to the end, so whatever failed before is behind it
                     (update :failures dissoc source)))))))
  nil)

(defn- begin-file! [source]
  ;; A new file's load began (Compiler.load re-entered): push a fresh frame. No model
  ;; touch - the file commits only when it finishes (end-file!).
  (when *file-stack*
    (swap! *file-stack* conj (FileFrame. source (java.util.ArrayList.) (long-array [0])
                                         (java.util.ArrayList.))))
  nil)

(defn- end-file! [_source]
  ;; The file finished loading (no throw): pop its frame and commit it. A throw during
  ;; the file's load means end-file! is never called for it (the compiler skips endFile
  ;; on error), so the frame is discarded with the stack unwind - its forms never reach
  ;; the model, and the file keeps whatever it had before.
  (when-let [fr (current-frame)]
    (swap! *file-stack* pop)
    (commit-dead! fr)
    (commit-frame! fr))
  nil)

(def ^:dynamic *defined*
  "Where the compiler says what it has just defined, or nil.

  A function of one map. The sink calls it for every `def` the compiler analyses,
  and `prune-vars!` for every var a reload takes away:

    {:dialect :clj :op :define :ns my.app :var my.app/render :source \"my/app.clj\"}
    {:dialect :clj :op :remove :ns my.app :var my.app/gone}

  WHAT IT IS FOR is somebody who has to be told when the code under them was
  replaced - a program whose top level built a tree that now has to be rebuilt out
  of the new definitions. Nothing else in a REPL protocol knows that on anyone's
  behalf, and everything that tried to work it out from the outside got a worse
  answer: watching every var's root reports `alter-var-root`, which is a value
  changing and no new code, and comparing what a namespace maps before and after
  misses a redefinition that lands on the same names. The compiler is the only
  thing that KNOWS, and it costs it a deref per def to say so.

  INDEPENDENT OF THE MODEL, which is the whole of why this is a separate channel
  and not a query over what was analysed. The model is disk-only on purpose - a
  form typed at a prompt is compiled inside no file and the sink drops it - and a
  `def` typed at a prompt is exactly what a person fixing one function does. So
  this is told BEFORE the invariant below applies, and `defining*' can install a
  sink with no file and no form stack: every other method is then a no-op and this
  one still reports.

  Its sibling is `*reload-progress*', and the two answer different halves of the
  same want: that one says what is being loaded while it loads, this one says what
  came out of it. `clojure.cljs.analysis' reports through this var too, adding
  :dialect :cljs, for the reason it shares the other one - a ClojureScript reload
  loads Clojure macro files on this JVM, so a watcher that bound two vars would
  see half of one reload in each.

  Nil by default and called for its effect. Dynamic, so the binding belongs to the
  thread evaluating: two REPLs evaluating at once are two threads, each reporting
  into its own connection. Exceptions out of it are not caught, for
  `*reload-progress*'s reason."
  nil)

(defn- defined!
  "Tell *defined* about `event`, if anything is listening."
  [event]
  (when-let [f *defined*] (f event))
  nil)

;; Invariant: a fact is recorded ONLY when a form is open (current-form non-nil).
;; Without a form there is nowhere to file it (no fid to attribute it to, and it
;; could never be dropped on reload - a ghost), so every sink method is a no-op when
;; no form is open. This never drops anything real: load / require always open a
;; form; only a bare eval outside a form window (an unsupported use of run-analysis)
;; would land here, and that was never retractable anyway.
;;
;; `*defined*' IS THE ONE EXCEPTION and is told outside the invariant, because what
;; it answers is about the program and not about the model - see it.
;;
;; Each method builds ONE self-contained fact object and appends it to its category -
;; no index is touched here. The builders replay the categories (in fid order for
;; `:defs`, which is the one that needs it) into the query indexes on read, so the
;; fact must carry everything the index needs, INCLUDING its own entity key: a
;; usage/def its var key, a keyword usage its keyword, a local its binding token plus
;; full info (ns/name/span). That is what lets a fact be a single object with no
;; [op a b] tuple around it.
(deftype AnalysisSink []
  IAnalysisSink
  (beginFile [_ source] (begin-file! source))
  (endFile [_ source] (end-file! source))
  (beginForm [_ source line column] (begin-form! source line column))
  (formStart [_ line column] (form-start! line column))
  (endForm [_] (end-form!))
  (deadForm [_ form kind ns _source line column el ec]
    ;; Kept on the file frame, not the open form: it is resolved when the file ends
    ;; (commit-dead!). The open form is remembered so that, when it ends, the dead
    ;; code can be given the locals it binds, and what the reader reported inside
    ;; its span can be marked dead (close-dead!).
    (when-let [^FileFrame fr (current-frame)]
      (.add ^java.util.ArrayList (.dead fr)
            {:form form :kind kind :ns ns :of (current-form)
             :span (when (and (nat-int? line) (nat-int? el)) [line column el ec])}))
    nil)
  (varUsage [_ target written var-form from-ns source line column el ec]
    ;; when-let on the key, not let: var-key is nil only for a nil-ns var, which the
    ;; compiler should never resolve to here - but if one slips through, skip it
    ;; rather than write a nil key that would later NPE (namespace nil) in queries.
    (when-let [of (current-form)]
      (when-let [k (var-key target)]
        (let [w (written-as k written)]
          (if (neg? line)
            ;; NOWHERE, and kept only for what its SPELLING says. A reference this
            ;; namespace could not have made without its own `ns' form - a bare name
            ;; that a :refer supplies, a name through an alias - is what the unused-*
            ;; questions are about, and it is load-bearing however it got here: if the
            ;; refer or the alias went, this would not compile. One spelled in full is
            ;; not: it needs nothing of the ns form, and it is also exactly what
            ;; macroexpansion leaves behind, since syntax-quote qualifies everything
            ;; it names. So the fully-spelled ones are dropped, and a macro's own body
            ;; does not silently make its caller's requires look used.
            ;;
            ;; Except a var of the very namespace being compiled, spelled however:
            ;; no require holds that up, so it cannot make one look used, and it is
            ;; the only trace left of a private helper called from inside a `go'
            ;; block - which re-emits every var it rewrites as a fresh, qualified,
            ;; positionless symbol. See file-facts' :refs.
            (when (or (nil? w) (not= (namespace w) (namespace k))
                      (and from-ns (= (namespace k) (name (ns-name from-ns)))))
              (add-fact! of CAT-REFS (span k source -1 -1 -1 -1 from-ns nil nil nil
                                           w var-form)))
            (add-fact! of CAT-USAGES (span k source line column el ec from-ns nil nil nil
                                           w var-form
                                           ;; clojure.core/defmethod marks the name it
                                           ;; adds a method to - see its expansion
                                           (when (:clojure.analysis/defmethod (meta written))
                                             :defmethod)))))))
    nil)
  (varDef [_ v declared source line column el ec]
    ;; OUTSIDE THE FORM WINDOW, and the only thing here that is: a def typed at a
    ;; prompt is inside no file, so there is no form to file it under and nothing
    ;; for the model to hold - and it is still a definition somebody has to be
    ;; told about. See `*defined*'.
    (when-let [k (var-key v)]
      (defined! {:dialect :clj :op :define
                 :ns (symbol (namespace k)) :var k :source source}))
    (when-let [of (current-form)]
      (when-let [k (var-key v)]
        (add-fact! of CAT-DEFS (span k source line column el ec nil nil nil
                                     (when declared :declare)))))
    nil)
  (localDef [_ binding name ns source line column el ec]
    (when-let [of (current-form)]
      (add-fact! of CAT-LOCALS (local-span binding source line column el ec ns name)))
    nil)
  (localUsage [_ binding ns source line column el ec]
    (when-let [of (current-form)]
      (if (neg? line)
        ;; NOWHERE: the binding is read and the read is no place. Only the token,
        ;; because only the token is asked for - whether anything read this binding.
        (add-fact! of CAT-LOCALREFS binding)
        (add-fact! of CAT-LOCALUSE (local-span binding source line column el ec ns))))
    nil)
  (qualifierUsage [_ qualifier from-ns source line column el ec]
    ;; The reader's, so the same line as keywordUsage's: another platform's branch
    ;; of a reader conditional is not this program's text, and a #_ discard is -
    ;; recorded, and marked :dead by close-dead! like everything else written
    ;; inside one.
    (when-let [of (when-not (RT/suppressRead) (current-form))]
      (add-fact! of CAT-QUALIFIERS (span qualifier source line column el ec from-ns nil)))
    nil)
  (keywordUsage [_ kw from-ns source line column el ec]
    ;; The branch of a reader conditional this platform does not take is read with
    ;; *suppress-read* on: it is another platform's code, not this program's. A #_
    ;; discard is read normally and IS recorded - it is still written in the file -
    ;; and close-dead! marks it :dead, as it does one in a comment.
    (when-let [of (when-not (RT/suppressRead) (current-form))]
      (add-fact! of CAT-KEYWORDS (span kw source line column el ec from-ns nil)))
    nil)
  (memberUsage [_ c member from-ns source line column el ec]
    (when-let [of (current-form)]
      (add-fact! of CAT-MEMBERS (span [(class-key c) member] source line column el ec
                                      from-ns nil)))
    nil)
  (destructuredKeyword [_ kw from-ns source line column el ec]
    ;; with the keyword's other uses, marked for how it is written: a rename of the
    ;; keyword renames the local with it, which is what makes it a place at all
    (when-let [of (current-form)]
      (add-fact! of CAT-KEYWORDS (span kw source line column el ec from-ns nil nil nil
                                       nil nil :destructuring)))
    nil)
  (classUsage [_ c from-ns source line column el ec]
    (when-let [of (current-form)]
      (add-fact! of CAT-CLASSES (span (class-key c) source line column el ec from-ns nil)))
    nil)
  (nsForm [_ form nsym source]
    ;; Filed with the uses, marked for what they are: one list of places the name is
    ;; written, which is what a rename walks, and a mark on the ones that are the
    ;; declaration - which is what counts-as-use? reads and what a client shows
    ;; differently.
    ;;
    ;; And the clauses themselves, positioned (ns-specs): the namespace's live
    ;; state says which alias, refer or import nothing uses, and nothing about where
    ;; the ns form wrote it.
    (when-let [of (current-form)]
      (let [from-ns (create-ns nsym)]
        (doseq [[qsym written] (ns-form-refers form)
                :let [m (meta written)]
                :when (:line m)]
          (add-fact! of CAT-USAGES
                     (span qsym source (:line m) (:column m) (:end-line m) (:end-column m)
                           from-ns nil nil :refer)))
        (add-fact! of CAT-NSSPECS (assoc (ns-specs form) :ns nsym))))
    nil)
  (requireCall [_ form f from-ns source]
    ;; nsForm's clauses, for a call: where the source says a library is loaded,
    ;; top-level or in a function body alike. Kept apart from :ns-specs, which is
    ;; what the ns form is - a call is not the ns form, and a lint reading the
    ;; ns form's clauses must not be handed it as one.
    ;;
    ;; A requiring-resolve is both halves of what it does: a use of the var it
    ;; names, where the source wrote it and marked :requiring-resolve, and a load
    ;; of its namespace, at the namespace part of the name.
    (when-let [of (current-form)]
      (if (= "requiring-resolve" (name f))
        (let [named (requiring-resolve-names form)]
          (doseq [{k :var :keys [written at]} named]
            (add-fact! of CAT-USAGES (span k source (:line at) (:column at) (:end-line at)
                                           (:end-column at) from-ns nil nil nil
                                           (written-as k written) nil :requiring-resolve)))
          (when (seq named)
            (add-fact! of CAT-REQCALLS {:ns (ns-name from-ns) :requires (mapv :lib named)})))
        (when-let [requires (seq (require-call-specs form f))]
          ;; a call that is the whole top-level form is one the file makes as it
          ;; loads - what a lint of the file's requires reads as a clause of its
          ;; ns form, the way clj-kondo does; one in a function body loads when
          ;; the function runs, which may be never
          (let [{:keys [line column]} (written-span form)
                ^longs pos (.pos ^OpenForm of)]
            (add-fact! of CAT-REQCALLS
                       (cond-> {:ns (ns-name from-ns) :requires (vec requires)}
                         (and line (= (long line) (aget pos 0)) (= (long column) (aget pos 1)))
                         (assoc :top-level true)))))))
    nil)
  (invokeUsage [_ target argc from-ns source line column el ec]
    (when-let [of (current-form)]
      (when-let [k (var-key target)]
        (add-fact! of CAT-INVOKES (->Invoke k source (int line) (int column) (norm-end el)
                                            (norm-end ec) from-ns (int argc)))))
    nil)
  (warning [_ kind message ns source line column el ec]
    ;; Few - only what the developer asked to be warned about - so a plain map.
    (when-let [of (current-form)]
      (add-fact! of CAT-WARNINGS
                 (cond-> {:kind kind :message message :source source
                          :line line :column column :ns (some-> ns ns-name)}
                   (nat-int? el) (assoc :end-line el)
                   (nat-int? ec) (assoc :end-column ec))))
    nil)
  (importUsage [_ c from-ns source line column el ec]
    (when-let [of (current-form)]
      (add-fact! of CAT-CLASSES
                 (span (class-key c) source line column el ec from-ns nil nil :import)))
    nil)
  (macroExpansion [_ macro from-ns source line column el ec record-usage?]
    (when-let [of (current-form)]
     (when-let [mk (var-key macro)]      ; skip a nil-ns macro var (see varUsage)
      (let [ns-sym (ns-name from-ns)]
        ;; Always record the compile-time edge (stale reload needs it even for
        ;; expansion-introduced calls); record the macro *usage* only for a
        ;; source-written call. The edge's fid (the form's own, filled in by
        ;; the frame) carries the expanding form's file, which the §9 cascade reads.
        (add-fact! of CAT-MACRODEP (MacroDep. ns-sym mk))
        (when record-usage?
          (add-fact! of CAT-USAGES (span mk source line column el ec from-ns true))))))
    nil))

;; --- drivers ---------------------------------------------------------------

(defn reset-model!
  "Clear the whole model (cold-load driver: start from empty, design §8)."
  []
  (reset! model empty-model))

(declare resolve-source)

(defn- failed-at
  "Where `t` says the compile failed, as {:line :column}, or nil: the first of its
  causes whose data names a line - a CompilerException's :clojure.error/line, or an
  ex-info's :line."
  [^Throwable t]
  (some (fn [^Throwable c]
          (let [d (ex-data c)]
            (cond (:clojure.error/line d) {:line (:clojure.error/line d)
                                           :column (:clojure.error/column d)}
                  (:line d) {:line (:line d) :column (:column d)})))
        (take-while some? (iterate #(.getCause ^Throwable %) t))))

(defn- root-message
  "The message of the deepest cause of `t` that has one - `Unable to resolve symbol:
  foo in this context` rather than the `Syntax error compiling at ...` wrapped
  around it, which says where and not what."
  [^Throwable t]
  (or (last (keep #(.getMessage ^Throwable %)
                  (take-while some? (iterate #(.getCause ^Throwable %) t))))
      (.getName (class t))))

(defn- record-failure!
  "The file `fr` is the load of threw `t`: remember it, against the version of the
  file on disk that failed, until the file next loads to the end - see file-failure.
  At the form that was being compiled when nothing more precise is known."
  [^FileFrame fr ^Throwable t]
  (let [source (.source fr)
        ^OpenForm of (current-form)
        pos (or (failed-at t)
                (when of {:line (aget ^longs (.pos of) 0) :column (aget ^longs (.pos of) 1)}))]
    (when source
      (swap! model assoc-in [:failures source]
             (merge {:mtime (first (resolve-source source)) :message (root-message t)}
                    pos)))))

(defn- with-sink
  "Run `thunk` with the sink installed and fresh per-thread file + form stacks. Commits
  happen file-by-file as each file's load completes (commit-frame! at endFile), so there
  is nothing to flush here. If `thunk` throws, the file that was loading never commits
  (its frame is discarded with the stack unwind) while every file that fully loaded is
  already in - the reload's atomicity is per file, matching what the compiler left
  defined.

  And the file that was loading is remembered to have failed, and where: the frame
  still on top of the stack is the innermost file being loaded, which is the one the
  throw came out of."
  [thunk]
  (push-thread-bindings {Compiler/ANALYSIS_SINK (->AnalysisSink)
                         #'*file-stack*         (atom [])
                         #'*form-stack*         (atom [])})
  (try (thunk)
       (catch Throwable t
         (when-let [fr (current-frame)] (record-failure! fr t))
         (throw t))
       (finally (pop-thread-bindings))))

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

(defn defining*
  "Invoke `thunk` with `report` told every var it defines, and answer what it
  answers. See `*defined*' for the events.

  A SINK IS INSTALLED ONLY WHERE THERE IS NONE, which is what makes this usable
  around an arbitrary evaluation. The compiler reports a def to whatever sink is
  bound and to nothing otherwise, so something has to be bound - and the stacks
  are deliberately left unbound, which makes every other sink method a no-op
  (they are each gated on `current-frame' / `current-form', both nil-safe). So a
  `(require 'foo)` typed at a prompt reports the vars it defines WITHOUT quietly
  starting to populate a model that is disk-only by design.

  And where a sink IS installed - inside `load-file!', inside `stale-reload!',
  inside anything under `run-analysis' - this adds the reporting and leaves that
  sink alone, so the model goes on being filled exactly as it was. Replacing it
  with a stackless one would be a load that analysed nothing.

  Nesting is the caller's to make sense of: the innermost `report' wins, as a
  thread binding does, and one binding around a whole evaluation is what collects
  everything that evaluation defined - however many files it turned out to load."
  [report thunk]
  (if (.deref Compiler/ANALYSIS_SINK)
    (push-thread-bindings {#'*defined* report})
    (push-thread-bindings {Compiler/ANALYSIS_SINK (->AnalysisSink)
                           #'*defined*            report}))
  (try (thunk) (finally (pop-thread-bindings))))

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
  the classpath-relative source path (e.g. \"app/util.clj\").

  Its staleness baselines go with it, so that a file dropped is one the model has
  nothing left to say about: none of what it recorded, and no record of when it last
  read it. A file written back afterwards has not been analysed, and is analysed
  when something loads it."
  [source]
  (retract-source* source)
  (swap! model (fn [m] (-> m
                           (update :file-mtime dissoc source)
                           (update :failures dissoc source)
                           (update :non-files disj source))))
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
  "Reject a `source` load cannot be given: one that is not a classpath-relative
  resource path - the key the compiler records (e.g. \"app/util.clj\") - and one
  that is spelled right and that nothing on the classpath answers to.

  TWO REFUSALS AND NOT ONE, because they are two different things to do about it.
  An editor deals in ABSOLUTE paths and must translate to the resource path (strip
  the classpath root) before calling load-file!, and catching that here turns it
  into a clear error instead of a cryptic FileNotFoundException from `load` or a
  silent no-op when the key matches nothing in the model. A source nothing answers
  to is the other one - deleted, renamed, moved off the classpath - and telling the
  caller that its path is the wrong shape when the shape is the one thing right
  about it sends them looking where the answer is not. `deleted-files` is what names
  these, and a reload drops them rather than loading them."
  [source]
  (when (or (not (string? source)) (.startsWith ^String source "/"))
    (throw (ex-info (str "load-file! expects a classpath-relative source path, the key the "
                         "compiler records (e.g. \"app/util.clj\") - not " (pr-str source)
                         ". An editor must translate an absolute file path to its resource "
                         "path (strip the classpath root) before calling load-file!.")
                    {:source source})))
  (when (nil? (io/resource source))
    (throw (ex-info (str "load-file! cannot load " (pr-str source)
                         ": nothing on the classpath answers to it. The file has been"
                         " deleted, renamed or moved off the classpath - see"
                         " deleted-files, which names these, and stale-reload!, which"
                         " drops them from the model instead of loading them.")
                    {:source source :deleted true})))
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

;; ONE CACHE PER SUB-INDEX, and not one cache for all of them. Every one of them is
;; a pure function of the same form log, so they all go stale by the same rule - but
;; they are not wanted at the same moments, and that is the difference worth having.
;; A reload asks what `:defs` says while it prunes; the file graphs ask `:macro-deps`
;; and `:class-usages`; `:usages` and `:locals` - much the largest, and the dearest
;; to fold - answer an editor's questions and nothing the reload does. Held as one
;; index they were all rebuilt whenever any of them was, and since every file load
;; is a new form log, a reload of K files rebuilt the whole model K times: on a
;; 400-file model, reloading 40 files spent 1.9 of 3.0 seconds replaying facts no
;; part of the reload reads. Each index cached on its own, the reload touches only
;; the small one it uses and the rest are built again when somebody asks.
(defonce ^:private index-caches
  (into {} (for [k [:usages :defs :keyword-usages :class-usages :locals :macro-deps
                    :ns-usages :member-usages :ref-usages :qualifiers]]
             [k (atom {:forms nil :value nil})])))

(defn- sorted-fids
  "The live form ids, ascending, in a primitive array.

  `:defs` is the one index that depends on the order the log is replayed in, so it
  is the one place this is needed - and it is worth not doing in boxed Longs:
  `(sort (keys forms))` over an 18000-form log is 6 ms, and this is 2.4."
  ^longs [forms]
  (let [^longs a (long-array (keys forms))]
    (java.util.Arrays/sort a)
    a))

(defn- build-spans
  "{entity #{Span}} over one fact category - `:usages`, `:keyword-usages` or
  `:class-usages`, which differ in nothing but which category they fold. No replay
  order to respect: each fact joins the set under its own entity key, and a set does
  not care when it was joined.

  The index is accumulated as a TRANSIENT map: on a large log one of these grows to
  thousands of keys, and a persistent assoc would rebuild its spine on every one of
  the (many) facts touching it. The transient must be threaded, since assoc! may
  promote and return a new object."
  [forms cat]
  (persistent!
   (reduce-kv (fn [idx _ fe]
                (reduce (fn [idx ^Span s]
                          (let [e (.entity s)]
                            (assoc! idx e (conj (get idx e #{}) s))))
                        idx (get fe cat)))
              (transient {}) forms)))

(defn- build-defs
  "{qsym {:span span}} - the one index replayed in fid (definition) order, because
  it is the one where a later fact has to beat an earlier one: a redefinition is
  just a later form defining the same var, and replaying in order lets it overwrite
  the earlier entry, so the highest fid wins. That is what the old eager
  retract-on-redefine achieved. A var referenced but defined by no live form gets no
  entry at all, so `definition` returns nil for it - what the old incremental
  tombstone yielded."
  [forms]
  (let [^longs fids (sorted-fids forms)
        n           (alength fids)]
    (loop [i 0, idx (transient {})]
      (if (< i n)
        (recur (inc i)
               (reduce (fn [idx ^Span s] (assoc! idx (.entity s) {:span s}))
                       idx (:defs (get forms (aget fids i)))))
        (persistent! idx)))))

(defn- build-locals
  "{binding {:ns :name ...span :uses #{use} [:referenced true]}} - three fact
  categories in one index, since a local's uses belong to its entry. A form's
  bindings are folded before its uses, so every binding is registered before a use
  can attach to it; a local is lexically scoped to its own form, so that is exactly
  the right scope and the order between forms does not come into it.

  `:uses` is the PLACES the binding is read, which is what a rename rewrites and
  what find-local-usages answers. `:referenced` is the other fact: that something
  read it from nowhere - a macro handed the symbol on with its position destroyed,
  so there is a read and no place. A binding may have one, the other or both, and
  unused-binding is about the two together; see the sink's localUsage."
  [forms]
  (persistent!
   (reduce-kv
    (fn [idx _ fe]
      (as-> idx idx
        ;; A local's def carries its full info (a LocalSpan); project it to the plain-
        ;; map index entry, keeping any :uses already gathered.
        (reduce (fn [idx ^LocalSpan l]
                  (let [b (.binding l)]
                    (assoc! idx b (cond-> (assoc (local->map l)
                                                 :uses (get (get idx b) :uses #{}))
                                    (:referenced (get idx b)) (assoc :referenced true)))))
                idx (:locals fe))
        (reduce (fn [idx ^LocalSpan l]
                  (let [b   (.binding l)
                        cur (get idx b)]
                    (if cur
                      (assoc! idx b (update cur :uses (fnil conj #{}) (local->map l)))
                      idx)))
                idx (:local-uses fe))
        ;; the bare token, which is the whole of what an unpositioned read has to say
        (reduce (fn [idx b]
                  (if-let [cur (get idx b)]
                    (assoc! idx b (assoc cur :referenced true))
                    idx))
                idx (:local-refs fe))))
    (transient {}) forms)))

(defn- build-macro-deps
  "{ns-sym {macro-qsym #{fid}}} - the compile-time edges (§9). Each edge is stamped
  with the fid of the form that expanded it, which is how the file cascade finds the
  expanding file."
  [forms]
  (persistent!
   (reduce-kv (fn [idx fid fe]
                (reduce (fn [idx ^MacroDep d]
                          (let [n (.mns d)]
                            (assoc! idx n (update (get idx n {}) (.mvar d)
                                                  (fnil conj #{}) fid))))
                        idx (:macro-deps fe)))
              (transient {}) forms)))

(defn- build-ns-usages
  "{lib #{span}} - where each live form writes a library it loads: an ns form in a
  :require or a :use (its :ns-specs facts), a call of require or use (its
  :require-calls facts, each place marked :call true). Plain maps rather than
  Spans: the facts are what `ns-specs` read off the form, and they are few - one
  per library written - so there is nothing to save by packing them.

  A library written with no position (one the reader gave none) is not a place
  anybody can be sent to, and is left out."
  [forms]
  (let [add (fn [idx fe facts call?]
              (reduce (fn [idx {:keys [ns requires]}]
                        (reduce (fn [idx {:keys [lib at clause dead]}]
                                  (if at
                                    (assoc! idx lib (conj (get idx lib #{})
                                                          (cond-> (assoc at :source (:source fe)
                                                                         :from-ns ns
                                                                         :declaration clause)
                                                            call? (assoc :call true)
                                                            dead (assoc :dead dead))))
                                    idx))
                                idx requires))
                      idx facts))]
    (persistent!
     (reduce-kv (fn [idx _ fe]
                  (-> idx
                      (add fe (:ns-specs fe) false)
                      (add fe (:require-calls fe) true)))
                (transient {}) forms))))

(def ^:private index-keys
  "The indexes `derived` is all of, which is what `snapshot` shows."
  [:usages :defs :keyword-usages :class-usages :locals :macro-deps])

(defn- index
  "One derived index of model value `m`, built from its form log and cached until
  that log changes (`cached-by-forms`). `k` is one of :usages, :ref-usages, :defs,
  :keyword-usages, :class-usages, :member-usages, :locals, :macro-deps, :ns-usages,
  :qualifiers.

  `:ref-usages` is the references that are NOWHERE - shaped like `:usages' and never
  to be mistaken for it, since every span in it is at line -1. Only the unused-*
  questions read it; see the sink's varUsage.

  Ask for the one that answers the question at hand: nothing here forces any of the
  others, which is the whole of why there is a cache each."
  [m k]
  (let [forms (:forms m)]
    (cached-by-forms
     (get index-caches k) forms
     (fn []
       (case k
         :usages         (build-spans forms :usages)
         :ref-usages     (build-spans forms :ref-usages)
         :qualifiers     (build-spans forms :qualifiers)
         :keyword-usages (build-spans forms :keyword-usages)
         :class-usages   (build-spans forms :class-usages)
         :member-usages  (build-spans forms :member-usages)
         :defs           (build-defs forms)
         :locals         (build-locals forms)
         :macro-deps     (build-macro-deps forms)
         :ns-usages      (build-ns-usages forms))))))

(defn- derived
  "Every by-entity index for model value `m` as one map, shaped as the one index
  these replace was: {:usages :defs :keyword-usages :class-usages :locals
  :macro-deps}. What `snapshot` shows, and what a caller wanting several of them off
  one consistent log should take (deref the model once and pass it).

  It forces all of them, so prefer `index` with the key actually needed - a caller
  that wants `:defs` and takes this pays for `:usages` and `:locals` as well."
  [m]
  (into {} (for [k index-keys] [k (index m k)])))

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

(defn- interned-var
  "The var the qualified name `k` names in its OWN namespace, or nil - not a refer
  of somebody else's var under that name, and not a class or anything else a
  namespace can map a name to.

  `(.getMapping)` rather than `ns-interns`, which answers the same question by
  building a map of every intern in the namespace: this is asked once per recorded
  def when the compile-time graph is built, and the graph is built over the whole
  model."
  [k]
  (when-let [^clojure.lang.Namespace home (find-ns (symbol (namespace k)))]
    (let [o (.getMapping home (symbol (name k)))]
      (when (and (var? o) (identical? home (.ns ^clojure.lang.Var o)))
        o))))

(defn- protocol-value
  "The protocol `v` holds, or nil where it holds no protocol.

  A protocol is a map `defprotocol` built and `def`-ed, carrying the interface it
  generated and the methods it named; anything else - including a var with no root -
  is not one. Read off the var rather than off the model, because it is the protocol
  itself that says which methods it has now: the reload just re-`def`-ed it, and a
  method it stopped naming is a method the source stopped writing."
  [v]
  (when (and (var? v) (.hasRoot ^clojure.lang.Var v))
    (let [value (.getRawRoot ^clojure.lang.Var v)]
      ;; `:sigs' is asked for by presence and not by value: a protocol with no
      ;; methods left carries it as nil, and it is exactly the protocol whose
      ;; methods all have to go
      (when (and (map? value) (class? (:on-interface value)) (contains? value :sigs))
        value))))

(defn- protocol-interface
  "The name of the interface the var-key `k` names a protocol of, or nil.

  A protocol generates an interface, and that is what a `deftype`, a `defrecord` or
  a `reify` implementing the protocol actually names: `clojure.core/deftype` resolves
  the protocol and puts `(:on @the-protocol)` in the form it emits, so the compiler
  sees a class where the source wrote a var. The occurrence is recorded under the
  class - see `find-usages`, which reads this to put the two together.

  Read out of the running process rather than out of the model, for
  `protocol-value`'s reason and one more: a protocol whose var has been unmapped is
  a name nothing implements any more, and nil here is that answer."
  [k]
  (when-let [home (find-ns (symbol (namespace k)))]
    (when-let [value (protocol-value (get (ns-interns home) (symbol (name k))))]
      (.getName ^Class (:on-interface value)))))

(defn- interface-protocol
  "The var-key of the protocol that generated the interface named `cname`, or nil -
  `protocol-interface' the other way round.

  What the unused-namespace and unused-refer questions need of an implementation: a
  `deftype` naming `p/P` is recorded as a use of the interface `P` generated, and
  the source that wrote it wrote the alias and the protocol - see `find-usages`.
  `defprotocol` names the interface after the namespace, munged, and the protocol;
  which var holds it is asked of the protocols of that namespace rather than
  unmunged, since munging is not one-to-one."
  [^String cname]
  (let [i (.lastIndexOf cname ".")]
    (when (pos? i)
      (let [prefix (subs cname 0 i)]
        (some (fn [n]
                (when (= prefix (str (munge (namespace-munge (ns-name n)))))
                  (some (fn [[s v]]
                          (when-let [p (protocol-value v)]
                            (when (= cname (.getName ^Class (:on-interface p)))
                              (symbol (str (ns-name n)) (str s)))))
                        (ns-interns n))))
              (all-ns))))))

(defn find-usages
  "Usage sites recorded for a var - pass the Var, or its fully-qualified name symbol
  (my.ns/foo). Returns a set of spans
  {:from-ns :source :line :column :end-line :end-column [:macro] [:dead]
   [:declaration]}.

  Code the program does not run is included: a use in a #_ carries :dead :discard,
  one in a (comment ...) :dead :comment. It is resolved rather than compiled - see
  the dead code section - so it can name something the compiler would not have.

  THE NS FORM'S OWN MENTION is included too, carrying :declaration :refer - the name
  as it is written in a :refer, a :use's :only or a :refer-clojure's :only. It is not
  a use of the var and does not count as one (counts-as-use?), but it is a place the
  name is written, and a rename that skipped it would leave the ns form naming
  something gone. See IAnalysisSink.referUsage; an :as alias is not this - it names a
  namespace, and ns-referenced-namespaces is the question about those.

  A PROTOCOL answers the places that implement it as well. A `deftype`, a `defrecord`
  or a `reify` naming a protocol names the interface it generated by the time the
  compiler sees it, so the occurrence is recorded as a class usage of that interface
  (positioned where the protocol was written - see `clojure.core/parse-opts+specs`),
  and this merges the two: asking where a protocol is used answers both the code
  that calls through it and the code that implements it. Uses of the interface
  written as an interface - a type hint, an `instance?` - come along with them, and
  they are uses of the protocol too.

  A protocol METHOD answers its call sites only. What implements a method is the
  form that implements its protocol, which the model files under the protocol
  rather than under the method: a `deftype` need not implement every method it
  could, and answering a method with its protocol's implementations would be
  answering a question nobody asked."
  [var-or-sym]
  (let [k (->var-key var-or-sym)
        m @model]
    (into (spans->maps (get (index m :usages) k))
          (when-let [interface (protocol-interface k)]
            (spans->maps (get (index m :class-usages) interface))))))

(defn definition
  "Definition site recorded for a var - pass the Var or its fully-qualified name
  symbol. Returns a span, or nil. A var referenced but defined by no live form (its
  def deleted from source, or never analysed) is treated as undefined - returns nil."
  [var-or-sym]
  (some-> (:span (get (index @model :defs) (->var-key var-or-sym))) span->map))

(defn find-keyword-usages
  "Occurrence sites recorded for keyword kw. Auto-resolved keywords are indexed
  fully-qualified, so pass e.g. (keyword \"my.ns\" \"x\")."
  [kw]
  (spans->maps (get (index @model :keyword-usages) kw)))

(defn find-class-usages
  "Occurrence sites recorded for class c - a java.lang.Class, or its fully-qualified
  name as a string/symbol. Usages are keyed by class name, so a reloaded class's
  occurrences unify with the original's and no stale Class/loader is pinned.

  The name an :import writes is among them, carrying :declaration :import, for the
  reason find-usages keeps a :refer: it is where the name is written and what a
  rename replaces. It is not a use and does not count as one - an import used
  nowhere else is still an unused import."
  [c]
  (spans->maps (get (index @model :class-usages) (if (class? c) (.getName ^Class c) (str c)))))

(defn- covers?
  "Does the span `s` - :line :column :end-line :end-column - hold position
  line:column? The end counts: a cursor just past a name is still on it."
  [s line column]
  (let [l (:line s) c (:column s)
        el (if (nat-int? (:end-line s)) (:end-line s) l)
        ec (if (nat-int? (:end-column s)) (:end-column s) c)]
    (and (not (neg? (compare [line column] [l c])))
         (not (pos? (compare [line column] [el ec]))))))

(defn find-member-usages
  "Where the source names a Java member - `c` the class declaring it (a Class or its
  name), `member` its name, or \"new\" for a constructor. A set of spans shaped like
  find-usages', each at the member's name as it is written: `length` in (.length s),
  in String/.length and in (. s length).

  Only what the compiler resolved. A call through a target of no known type is
  resolved by reflection when it runs, and names no member here; a method value
  names every overload of its name, as each class declaring one of them.

  By the DECLARING class, which is the one question with one answer: a method
  written on a String and inherited from Object is Object's. Asking about a class
  and a name is the caller's to turn into the classes declaring what it has of
  that name - replique does, off the class's own methods."
  [c member]
  (spans->maps (get (index @model :member-usages)
                    [(if (class? c) (.getName ^Class c) (str c)) (str member)])))

(defn member-at
  "The Java member the source names at `line`:`column` of file `source`, as the
  compiler resolved it - [declaring-class-name member], what find-member-usages
  takes - or nil where it names none there. What a name written .length is
  cannot be said from the text, which does not say what it is called on, and the
  compiler has said it already."
  [source line column]
  (let [m @model]
    (some (fn [fid]
            (some (fn [^Span s]
                    (when (covers? (span->map s) line column) (.entity s)))
                  (get-in m [:forms fid :member-usages])))
          (get-in m [:source->forms source]))))

(defn find-namespace-usages
  "Where a namespace is required - pass the Namespace or its name symbol. A set of
  {:from-ns :source :line :column :end-line :end-column :declaration [:call]}: the
  library as an ns form's :require or :use writes it, :declaration the clause
  (:require or :use) as find-usages marks a :refer, and :from-ns the requiring
  namespace's name symbol.

  A CALL of require, use or requiring-resolve is among them, carrying :call true,
  wherever it is written - at the top level, or in a function that loads the
  library lazily - and :declaration the function called. It is where the source
  says the namespace is loaded, which is the same thing an ns form says, and it is
  recorded as the call is compiled rather than as it runs: one in a function
  nobody has called is here too. Only a library written as a literal is: see
  require-call-specs. A requiring-resolve is placed at the namespace part of the
  name it writes - the rest is the var, a use of it (requiring-resolve-names).

  One in code the program does not run is here as well, as find-usages has it -
  a (require 'my.lib) in a (comment ...) carries :dead :comment, one in a #_
  :dead :discard. It is resolved rather than compiled, like the rest of the dead
  code, so it is here although the compiler never saw the call.

  That is the whole of what a namespace is used as. Its vars and its keywords are
  things of their own, asked about with find-usages and find-keyword-usages: a
  `my.lib/f` is a use of f, and answering it here as well would make every use of
  every var of the namespace a use of the namespace. Nor is a (requiring-resolve
  'my.lib/f), which names f."
  [ns-or-sym]
  (get (index @model :ns-usages)
       (if (instance? clojure.lang.Namespace ns-or-sym) (ns-name ns-or-sym) ns-or-sym)))

(defn macro-deps
  "Compile-time macro dependency edges. No arg: {ns-sym #{macro-qsym}}. With a
  namespace symbol: the set of macro var names (qualified symbols) it expanded
  (design §9)."
  ([] (reduce-kv (fn [acc ns mm] (assoc acc ns (set (keys mm)))) {} (index @model :macro-deps)))
  ([ns-sym] (set (keys (get (index @model :macro-deps) ns-sym)))))

(defn unused-locals
  "Source-written local bindings with no recorded reference. Optionally restrict
  to a namespace. Each result is the binding's def site plus :name and :ns.

  A SITE, NOT A BINDING, as clojure.cljs.analysis/unused-locals. A macro may bind
  one written symbol more than once: a `loop` that destructures binds its pattern
  in a `let` outside the loop and again inside it, and only the inner one is read
  - and a binding the macro never reads is not the programmer's to remove while
  another one at the same place is read. So a site is unused only when every
  binding written there is.

  AND READ IS READ, whether or not the reading has a place. A macro that hands a
  binding's symbol on with its metadata replaced - `clojure.core/vswap' does it to
  the volatile, io.pedestal.log/error to its :exception - leaves a read that is
  nowhere, and a binding read from nowhere is still not one to delete. So `:uses'
  (the places) and `:referenced' (that something read it) are asked together; see
  build-locals."
  ([] (unused-locals nil))
  ([ns-sym]
   (for [[_ infos] (group-by (juxt :source :line :column)
                             (vals (index @model :locals)))
         :let  [info (first infos)]
         :when (every? #(and (empty? (:uses %)) (not (:referenced %))) infos)
         :when (or (nil? ns-sym) (= ns-sym (ns-name (:ns info))))]
     (dissoc info :uses :referenced))))

(defn find-local-usages
  "Where the local written at `line`:`column` of file `source` is - its binding and
  every use of it - or nil where no local is written there. The position may be
  the binding's or any of its uses'. A set of {:source :line :column :end-line
  :end-column :from-ns [:declaration :binding]}: the binding carries :declaration
  :binding, which is a place a rename rewrites and not a use.

  BY SITE, for unused-locals' reason: a macro may bind one written symbol more than
  once - a destructuring `loop` binds its pattern outside the loop and again inside
  it - and the programmer wrote one local. So the answer is every binding the
  source wrote at the binding's place, and every use of any of them.

  A local is lexically its form's, so this reads the forms of `source` and nothing
  else. One in code the program does not run - a #_, a (comment ...) - is not
  recorded, and is not found."
  [source line column]
  (let [m      @model
        forms  (keep #(get-in m [:forms %]) (get-in m [:source->forms source]))
        defs   (mapcat :locals forms)
        uses   (mapcat :local-uses forms)
        hit    (into #{} (comp (filter #(covers? % line column)) (map :binding))
                     (concat defs uses))
        site   (juxt :line :column)
        sites  (into #{} (comp (filter #(hit (:binding %))) (map site)) defs)
        bound  (into hit (comp (filter #(sites (site %))) (map :binding)) defs)
        place  (fn [l] (cond-> {:source (:source l) :line (:line l) :column (:column l)
                                :from-ns (some-> (:lns l) ns-name)}
                         (nat-int? (:end-line l))   (assoc :end-line (:end-line l))
                         (nat-int? (:end-column l)) (assoc :end-column (:end-column l))))]
    (when (seq bound)
      (into (into #{} (comp (filter #(bound (:binding %)))
                            (map #(assoc (place %) :declaration :binding)))
                  defs)
            (comp (filter #(bound (:binding %))) (map place))
            uses))))

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

(defn- counts-as-use?
  "Does usage span `s` count as a use for the unused-* lints?

  A usage in a #_ does not: the code is gone, and a require kept alive by it is a
  require nothing needs. A usage in a (comment ...) does: a rich comment block is
  code meant to be run at the REPL, and dropping the require it uses breaks it -
  which is also how clj-kondo counts it.

  A DECLARATION does not, and cannot: what `:refer [f]' and `:import [p C]' name is
  the very thing these lints ask about, so counting them would answer \"is this
  refer used\" with the refer itself and no unused refer or import could ever be
  reported again. They are in find-usages because a rename has to rewrite them; they
  are not uses."
  [s]
  (and (not= :discard (:dead s)) (nil? (:declaration s))))

(defn ns-referenced-namespaces
  "Namespace-name symbols whose vars or namespaced keywords are referenced from
  ns-sym, per the model. A var used only in a #_ does not count; one used in a
  (comment ...) does - see counts-as-use?.

  A reference that is NOWHERE counts, which is the whole reason `:ref-usages' is
  kept: a use inside a macro that rebuilt the body it was given - a core.async `go'
  block is the common one - has no place in the file, and the require it needs is
  needed all the same. Only the ones spelled short enough to need this namespace's
  ns form are there at all; see the sink's varUsage."
  [ns-sym]
  (let [m @model
        from? (fn [uses] (some #(and (counts-as-use? %)
                                     (= ns-sym (some-> (:from-ns %) ns-name)))
                               uses))]
    (into #{}
          (concat
           (for [idx   [(index m :usages) (index m :ref-usages)]
                 [qsym uses] idx
                 :when (and (namespace qsym) (from? uses))]
             (symbol (namespace qsym)))
           (for [[kw uses] (index m :keyword-usages)
                 :when (and (namespace kw) (from? uses))]
             (symbol (namespace kw)))
           ;; a protocol implemented, which the compiler saw as its interface
           (for [[cname uses] (index m :class-usages)
                 :when (from? uses)
                 :let [k (interface-protocol cname)]
                 :when k]
             (symbol (namespace k)))))))

(defn- written-qualifiers
  "The namespace parts the source of ns-sym writes, as a set of symbols - the
  reader's record of what the text spells, aliases and full namespace names alike
  (and whatever else was written in front of a /). One in a #_ does not count; one
  in a (comment ...) does - see counts-as-use?."
  [m ns-sym]
  (into #{} (for [[q uses] (index m :qualifiers)
                  :when (some #(and (counts-as-use? %)
                                    (= ns-sym (some-> (:from-ns %) ns-name)))
                              uses)]
              q)))

(defn unused-aliases
  "Aliases in ns-sym whose target namespace has no var or namespaced-keyword
  reference from ns-sym AND whose own name the source nowhere writes. Returns
  {alias ns-sym}. A use in a (comment ...) counts, one in a #_ does not
  (counts-as-use?).

  THE SECOND QUESTION IS THE READER'S, and it is asked because the first cannot
  always be answered. A macro that consumes a qualified symbol at expansion time -
  `(sql/jsonb-build-object flags/k v)', where the key is read and something else is
  emitted - compiles to nothing naming the target namespace at all; a macro that
  rebuilds the body it was given - core.async's `go' - re-emits `json/f' as
  `cheshire.core/f', so the alias is gone rather than merely unpositioned. In both
  the alias is written and the file stops reading without it. See the sink's
  qualifierUsage.

  The union of the two, and not the spelling alone, because the spelling is not
  always there either: `::flags/k' reaches the model as the keyword it auto-resolves
  to and never as the alias token, and only the first question sees it."
  [ns-sym]
  (let [m     @model
        used  (ns-referenced-namespaces ns-sym)
        spelt (written-qualifiers m ns-sym)]
    (into {} (for [[a ns] (ns-aliases ns-sym)
                   :when (and (not (contains? used (ns-name ns)))
                              (not (contains? spelt a)))]
               [a (ns-name ns)]))))

(defn unused-refers
  "Non-core vars referred into ns-sym that are never used from it.
  Returns {referred-sym var}. clojure.core auto-refers are excluded. A use in a
  (comment ...) counts, one in a #_ does not (counts-as-use?).

  BY HOW THE NAME IS SPELLED, and not by whether the var is used at all, because
  that is what a refer is: `(:require [a.b :as x :refer [f]])' and then only ever
  `x/f' is a refer nothing needs, and taking it out changes nothing. So a use
  counts for the refer only where the source wrote the short name - `:written' nil,
  which is the span's way of saying the var's own name unqualified, or the local
  name where a `:rename' gave it another one.

  A reference that is nowhere counts too, spelling and all (`:ref-usages'): a bare
  name that survived a macro's rebuilding still resolves through this refer, and
  would stop compiling without it.

  The protocol path is the exception and cannot be spelled at all: a protocol
  implemented in a `deftype' reaches the model as its interface, a class usage with
  no symbol on it, so implementing one counts however it was named."
  [ns-sym]
  (let [m          @model
        uses       (index m :usages)
        refs       (index m :ref-usages)
        class-uses (index m :class-usages)
        core       (the-ns 'clojure.core)
        here?      (fn [s] (and (counts-as-use? s)
                                (= ns-sym (some-> (:from-ns s) ns-name))))
        short?     (fn [local s] (let [w (:written s)]
                                   (or (nil? w) (= w local))))
        used? (fn [local ^Var v]
                (let [k (var-key v)]
                  (or (some #(and (here? %) (short? local %))
                            (concat (get uses k) (get refs k)))
                      ;; a protocol is used where it is implemented too
                      (some here? (some->> (protocol-interface k) (get class-uses))))))]
    (into {} (for [[sym ^Var v] (ns-refers ns-sym)
                   :when (and (not (identical? core (.ns v))) (not (used? sym v)))]
               [sym v]))))

(defn unused-imports
  "User-imported classes in ns-sym that are never referenced from it.
  Returns {imported-sym class}. java.lang.* auto-imports are excluded. A use in a
  (comment ...) counts, one in a #_ does not (counts-as-use?)."
  [ns-sym]
  (let [defaults @default-imports
        used? (fn [c] (some #(and (counts-as-use? %)
                                  (= ns-sym (some-> (:from-ns %) ns-name)))
                            (find-class-usages c)))]
    (into {} (for [[sym c] (ns-imports ns-sym)
                   :when (and (not (contains? defaults c)) (not (used? c)))]
               [sym c]))))

;; --- one file's facts, for lints ---------------------------------------------

(defn file-facts
  "What the model holds of file `source`, as it was when the file was last analysed -
  the per-file material lints are made of, the way find-usages is the per-entity one:

    {:mtime    the file's mtime baseline: the version on disk these facts are about
     :usages   [{:var qsym ...span}]   every use of a var the file writes, :refer
                                        declarations and dead code included (marked),
                                        with :written where it was not spelled by its
                                        own name and :var-form for a #'
     :defs     [{:var qsym ...span}]   every def, in the order the forms define them -
                                        a var defined twice is here twice, and one a
                                        `declare' wrote is :declaration :declare
     :invokes  [{:var qsym :argc n ...span}]  every call of a var the file writes,
                                        with its argument count after macroexpansion
     :warnings [{:kind :message ...span}]     what the compiler warned about
     :forms    [{:line :column :ns}]   the top-level forms, in order
     :ns-specs [{:ns sym :requires [...] :imports [...]}]  what each ns form's
                                        clauses write, where - see ns-specs
     :require-calls [{:ns sym :requires [...]}]  what each call of require or use
                                        loads, where - see require-call-specs -
                                        :top-level where the call is the whole
                                        top-level form
     :refs     [{:var qsym :line :column ...}]  every use of a var the file makes
                                        NOWHERE - see the sink's varUsage - at the
                                        :line and :column of the top-level form it is
                                        in, since it has no place of its own}

  Spans are plain maps as find-usages answers them, :from-ns a namespace SYMBOL.

  Nothing here is a verdict. Whether a call has the wrong arity, or a use names a var
  that has gone, is a question about the rest of the program as it is NOW - the
  callee's :arglists, whether the var is still interned - and asking it is the
  caller's. What this answers is what the file said, which is all the model knows."
  [source]
  (let [m     @model
        forms (map #(get-in m [:forms %]) (sort (get-in m [:source->forms source])))
        from  (fn [x] (if (instance? clojure.lang.Namespace x) (ns-name x) x))
        fact  (fn [s] (-> (span->map s) (assoc :var (:entity s)) (update :from-ns from)))]
    {:mtime    (get-in m [:file-mtime source])
     :usages   (into [] (comp (mapcat :usages) (map fact)) forms)
     :defs     (into [] (comp (mapcat :defs) (map fact)) forms)
     :invokes  (into [] (comp (mapcat :invokes)
                              (map (fn [i] (-> (span->map i)
                                               (assoc :var (:entity i) :argc (:argc i))
                                               (update :from-ns from)))))
                     forms)
     :warnings (into [] (mapcat :warnings) forms)
     :forms    (mapv #(select-keys % [:line :column :ns]) forms)
     :ns-specs (into [] (mapcat :ns-specs) forms)
     :require-calls (into [] (mapcat :require-calls) forms)
     :refs     (into [] (mapcat (fn [f]
                                  (map #(merge (fact %) (select-keys f [:line :column]))
                                       (:ref-usages f))))
                     forms)}))

(defn version
  "An opaque token for the model as it is now: `identical?' to one taken earlier
  exactly when nothing has been analysed, retracted or failed since. What a tool
  compares around an evaluation to know whether what it showed from the model is
  still what the model says."
  []
  @model)

(defn file-mtime
  "The mtime baseline of file `source`: its on-disk mtime when it was last analysed,
  which is the version of it the model is about - or nil for a file the model does
  not hold, or one that is not a file (a jar entry)."
  [source]
  (get-in @model [:file-mtime source]))

(defn file-failure
  "How the last load of file `source` failed, or nil when it loaded to the end:

    {:mtime n :line n :column n :message \"Unable to resolve symbol: foo ...\"}

  :mtime is the file's on-disk mtime when that load threw - the version that does
  not compile, which is not the version the rest of the model is about: a file that
  fails keeps the facts of its last load that did not. Cleared by the next load of
  the file that reaches its end."
  [source]
  (get-in @model [:failures source]))

;; --- stale reload + prune (design §9) --------------------------------------

(defn analysed-files
  "The classpath-relative source paths this process has analysed: every file the
  compiler read under the sink and has not since had retracted.

  The population `changed-files` and `stale-files` are answers about, and here for
  the difference between the two ways their answer can be empty. \"Nothing has
  changed since this process read these files\" and \"this process has read no
  files\" read identically in an empty answer and are not the same fact - the
  first says the program is up to date, the second says nothing at all - and only
  a caller that can tell them apart can say which it is holding. The sink is a
  thread binding `run-analysis` and `load-file!` push, so a namespace that arrived
  by `require` at a prompt is loaded and is not in here."
  []
  (set (for [[source fids] (:source->forms @model) :when (seq fids)] source)))

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

(defn deleted-files
  "Analysed files whose file is gone - deleted, renamed, or moved off the classpath.

  What `changed-files` cannot answer for. A file that no longer resolves is not
  stale there, and rightly: staleness is a file to load again, and there is nothing
  to load this one from. It is not current either, though - the process still holds
  what the file defined, and the model still answers for a file nobody can open -
  and that is what this names.

  A source is one of these when it was read from a real file, which a recorded
  mtime is the record of, and nothing answers to its name now. A source a jar
  answers to is NOT one: a file a jar has taken over is shadowed rather than gone,
  and what this process holds still came from the file. Neither is a source that
  never had a file behind it - a `load-string`, or a namespace read out of a jar all
  along.

  Costs one classpath lookup per analysed file that has a file behind it - the same
  files `changed-files` resolves, and unrememberable for the same reason: whether
  nothing answers to a name is settled by nothing at all.

  Whether a file is gone or merely between two writes is not a question this can
  answer, and an editor that saves by writing a new file over the old one is a
  process where the answer changes twice per save. It is asked by `stale-reload!`,
  which is asked for by hand."
  []
  (let [m @model]
    (set (for [[source t] (:file-mtime m)
               :when (and t (= [nil false] (resolve-source source)))]
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
                      ;; :macro-deps fids are the forms the index replayed, so each
                      ;; is a live form and s is normally non-nil; guard anyway so any
                      ;; future drift injects no nil-source edge.
                      (if-let [s (:source (get forms fid))]
                        (reduce (fn [g os] (if (= os s) g (update g s (fnil conj #{}) os)))
                                g owner-srcs)
                        g))
                    g fids)))
        g mm))
     {} (index m :macro-deps))))

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

(defn- generated-class
  "The name of the class the def of var-key `k` generated, or nil.

  Read out of the running process rather than guessed from the name, because the
  name says nothing: `a/P` is the class `a.P` when a `defprotocol` made it and is no
  class at all when a `def` did.

  A PROTOCOL's var holds the interface it generated (`:on-interface`). A `deftype`'s
  or a `defrecord`'s class is held by no var, but the form that made it also interned
  a `->T` factory and imported `T` into the same namespace - so a `->T` whose
  namespace imports a `T` of that namespace's own package is that form's class. An
  import of somebody else's `T` is not, which is what the name check is for: a file
  that imports a class does not define it, and a `->Date` written by hand over an
  imported `java.util.Date` would otherwise make its file the owner of a class the
  JDK ships."
  [k]
  (or (when-let [p (protocol-value (interned-var k))]
        (.getName ^Class (:on-interface p)))
      (let [n (name k)]
        (when (.startsWith n "->")
          (when-let [home (find-ns (symbol (namespace k)))]
            (let [sym  (symbol (subs n 2))
                  c    (get (ns-imports home) sym)
                  made (str (.replace (str (ns-name home)) \- \_) "." sym)]
              (when (and (class? c) (= made (.getName ^Class c)))
                (.getName ^Class c))))))))

(defn- class-owners
  "{class-name -> the file whose def form generated it}, over every def the model
  holds - the other half of `:class-usages`, which is keyed by class name and says
  where each class is NAMED.

  Only classes a def generated are in here, so a class from a jar, from `import`, or
  from the JDK owns nothing and makes no edge: nothing in the model defines it and
  no reload can change it."
  [m]
  (persistent!
   (reduce-kv (fn [acc k e]
                (if-let [c (generated-class k)]
                  (assoc! acc c (:source (:span e)))
                  acc))
              (transient {}) (index m :defs))))

(defn- build-file-class-graph
  "Forward compile-time dependency graph over FILES for generated classes: {source
  #{dep-source}} where a form in `source` NAMES a class that a `defprotocol`, a
  `deftype` or a `defrecord` in `dep-source` generated. Self-edges are dropped.

  This is the compile-time coupling that is not a macro, and the reason it has to be
  here is that the macro graph cannot see it: a `deftype` implementing a protocol
  expands `clojure.core/deftype`, so the only macro edge it has is to `clojure.core`,
  and the file that actually matters - the one whose `defprotocol` generated the
  interface the type was compiled against - is not in it at all. Reloading the
  protocol alone generates a NEW interface, and every type compiled against the old
  one stops satisfying the protocol: the call fails at run time with no
  implementation of a method of a protocol, and nothing has changed in the file that
  implements it. Same for a `deftype`'s or a `defrecord`'s own class: recompiling the
  file that defines it leaves two classes of one name, and whoever was compiled
  against the first one no longer agrees with the rest of the program about what
  `instance?` means.

  A class NAMED is the whole test, and it is the right one: a type hint, an
  `instance?`, a constructor call and an `implements` are all resolved when the file
  is compiled, and the form holds the class it resolved to. Calls of the protocol's
  METHODS are not here and need not be - a method is a var, resolved again every
  time it runs."
  [m]
  (let [owner (class-owners m)]
    (reduce-kv
     (fn [g c spans]
       (if-let [o (get owner c)]
         (reduce (fn [g s]
                   (let [src (:source s)]
                     (if (or (nil? src) (= src o) (:dead s))
                       g
                       (update g src (fnil conj #{}) o))))
                 g spans)
         g))
     {} (index m :class-usages))))

;; Cached like the macro graph, and beside it rather than folded into it: the two are
;; built from different halves of the model and the tests of each want to see it
;; alone. The class half also asks the running process what each def generated, which
;; is why it is not built more often than the form log changes.
(defonce ^:private compile-graph-cache (atom {:forms nil :value nil}))

(defn- file-compile-graph
  "The whole compile-time dependency graph over files: what a file expands
  (`build-file-macro-graph`) and what it names (`build-file-class-graph`), merged.
  Built once per form log.

  This is the graph the stale cascade walks and the graph the reload order comes
  from. Both halves are compile-time edges - a file holding an expansion of a macro
  that changed, and a file holding a class that was generated again - and both are
  repaired the same way, by compiling the file again after the file it depends on."
  [m]
  (cached-by-forms compile-graph-cache (:forms m)
                   #(merge-with into (file-macro-graph m) (build-file-class-graph m))))

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
  time-depends on the seed through the file compile graph (design §9): the files
  that expanded one of its macros, and the files that named a class one of its def
  forms generated - a `defprotocol`'s interface, a `deftype`'s or a `defrecord`'s
  class. Runtime-only (function-call) dependents are excluded - a plain var
  re-resolves at runtime and needs no recompile. Conservative in both halves: an
  edit to a macro-defining file marks ALL its macro-dependent files stale, and an
  edit to a file that generates a class marks every file that names it, neither one
  distinguishing which form in the file changed.

  NEVER A FILE THAT IS GONE. The seed cannot be one - `changed-files` asks the disk
  and skips a file nothing answers to - but a DEPENDENT can, and a branch switch is
  where that happens: the file that expands a changed macro was deleted by the same
  checkout that changed the macro. Handing one to `reload-files!` is handing `load`
  a resource path nothing answers to, so they are dropped from the answer here.
  Dropped from the ANSWER and not from the walk, which leaves the cascade the shape
  it had: a file behind a gone one is reached as it always was, and reloading it
  costs a reload rather than an error. What has no file to be read is
  `deleted-files`, which is a different answer and a different thing to do about it.

  `gone` is that set, and it is an argument because asking the classpath about every
  analysed file is a thing to do once per reload: `stale-reload!` needs the same set
  to drop those files, and `clojure.cljs.analysis/macro-closure` asks this question
  once per file it tests."
  ([] (stale-files (changed-files)))
  ([seed] (stale-files seed (deleted-files)))
  ([seed gone]
   (let [rev (reverse-file-graph (file-compile-graph @model))]
     (loop [dirty (set seed), queue (vec seed)]
       (if-let [x (peek queue)]
         (let [fresh (remove dirty (get rev x))]
           (recur (into dirty fresh) (into (pop queue) fresh)))
         (into #{} (remove gone) dirty))))))

(defn- file-var-graph
  "Forward dependency graph over `files` only: {source #{dep-source}} where a form
  in `source` refers to a var that a `def` in `dep-source` defines. Self-edges are
  dropped, and so is everything outside `files` - nothing else is being loaded, so
  nothing else can be loaded out of order.

  NOT a compile-time graph, and deliberately not part of the stale cascade: a file
  that merely calls a var does not need compiling again when that var's file
  changes, because a call re-resolves its var every time it runs. That is why
  `file-compile-graph` is the right answer to WHAT IS STALE, and it is the wrong
  answer to WHAT ORDER TO LOAD IT IN. A var that does not exist yet does not
  re-resolve at run time: the compiler resolves `alias/sym` when it compiles the
  form, and a name the loaded namespace does not have is `No such var` on the spot.
  So two files being reloaded together, where one has just started using a
  definition the other has just grown, have to be loaded in that order - and this
  is the graph that says so. Ordering by it costs nothing: it loads the same files,
  and only says which of them goes first.

  Built against the set being reloaded rather than cached whole, because it can be:
  one pass over the defs to find those the reloaded files own, and then a lookup of
  each one's recorded usages, rather than a walk of every usage in the program."
  [m files]
  (let [nodes  (set files)
        usages (index m :usages)
        owner  (reduce-kv (fn [acc k e]
                            (let [src (:source (:span e))]
                              (if (nodes src) (assoc acc k src) acc)))
                          {} (index m :defs))]
    (reduce-kv
     (fn [g k home]
       (reduce (fn [g span]
                 (let [src (:source span)]
                   (if (and (nodes src) (not= src home) (not (:dead span)))
                     (update g src (fnil conj #{}) home)
                     g)))
               g (get usages k)))
     {} owner)))

(defn- lib-names
  "The namespace-name symbols the specs of a `:require` / `:use` /
  `:require-macros` clause name, prefix lists expanded.

  A spec is a symbol, or a sequential whose first element is a name and whose rest
  is either options - which start with a keyword - or, when it does not, more specs
  carrying that name as a prefix. That is the rule `require` itself reads them by,
  and the reason the shapes cannot be told apart any other way: `[a b]` is the
  prefix list a.b and `[a :as b]` is the lib a."
  [specs]
  (mapcat (fn [spec]
            (cond
              (symbol? spec) [spec]
              (sequential? spec)
              (let [[head & more] spec]
                (when (symbol? head)
                  (if (or (empty? more) (keyword? (first more)))
                    [head]
                    (map #(symbol (str head "." %)) (lib-names more)))))
              :else nil))
          specs))

(defn- ns-declaration
  "The `ns` form of source `source`, read off the disk AS IT IS NOW - the one thing
  about a file that is about to be reloaded that the model cannot answer, because
  everything the model holds about it was written the last time it was loaded.

  Nil when the file has no `ns` form, and nil when it will not read for any reason
  whatever, which is why every last thing in here is caught. The only use of the
  answer is to put two files being reloaded in an order, nothing is lost by not
  having it, and a file that does not read is the compiler's to complain about a
  moment later, in its own words and at the right place."
  [source]
  (try
    (when-let [url (io/resource source)]
      (with-open [r (java.io.PushbackReader. (io/reader url))]
        (binding [*read-eval* false
                  *default-data-reader-fn* (fn [_tag value] value)]
          (let [opts {:read-cond :allow :features #{:clj} :eof ::eof}]
            (loop []
              (let [form (read opts r)]
                (cond
                  (= ::eof form)                         nil
                  (and (seq? form) (= 'ns (first form))) form
                  :else                                  (recur))))))))
    (catch Throwable _ nil)))

(defn- ns-sources
  "The sources namespace `n` could be loaded from: the classpath path `require`
  derives from the name, in each extension the JVM side reads."
  [n]
  (let [base (-> (str n) (.replace \- \_) (.replace \. \/))]
    [(str base ".clj") (str base ".cljc")]))

(defn- file-require-graph
  "Forward dependency graph over `files` only, read from their `ns` forms ON DISK:
  {source #{dep-source}} where the new source of `source` requires a namespace that
  another file being reloaded holds. Nothing outside `files`, and no self-edges.

  This is the one ordering edge that cannot come from the model. `file-var-graph`
  and `file-compile-graph` are built from what the compiler recorded the LAST time
  these files were loaded, so they know every dependency the old sources had and
  none that the edit introduces - and an edit that first reaches into a file this
  one never touched before is exactly the one whose order matters most, because the
  definition it has come for is a definition that was not there before. Switching
  branches does it wholesale. A require is the declaration of that reach, it is
  written at the top of the new file, and reading it costs one pass of the reader
  over a file that is about to be handed to the compiler anyway.

  A namespace is matched to a file the way `require` matches one - the name, with
  dashes to underscores and dots to slashes - and also through the model, for a
  file whose namespace is not named after it. Neither has to find anything: a
  require of something not being reloaded says nothing about the order of what is."
  [m files]
  (let [nodes    (set files)
        ns->srcs (reduce-kv (fn [acc _ fe]
                              (if-let [n (:ns fe)]
                                (update acc n (fnil conj #{}) (:source fe))
                                acc))
                            {} (:forms m))
        sources  (fn [n] (filter nodes (into (set (ns-sources n)) (get ns->srcs n))))
        clause?  (fn [x] (and (sequential? x)
                              (#{:require :use :require-macros} (first x))))]
    (reduce
     (fn [g source]
       (if-let [form (ns-declaration source)]
         (let [deps (into #{} (comp (filter clause?)
                                    (mapcat #(lib-names (rest %)))
                                    (mapcat sources)
                                    (remove #(= source %)))
                          (rest form))]
           (if (seq deps) (update g source (fnil into #{}) deps) g))
         g))
     {} nodes)))

(defn- topo-order
  "Order files so each file's dependency files come first - the files whose macros
  it expands, the files whose generated classes it names, and the files defining the
  vars it refers to. Deps outside `nodes` are ignored - they are not being reloaded,
  so they are already current.

  A cycle is broken by placing ONE file and carrying on, rather than by giving up:
  the files that are not in the cycle keep their order, and the cycle is cut at one
  arbitrary but stable point (the lowest name left) instead of spilling every
  remaining file out in whatever order a set happens to iterate in."
  [files dep-fn]
  (let [nodes (set files)]
    (loop [order [], placed #{}, remaining nodes]
      (if (empty? remaining)
        order
        (let [ready (filter (fn [n] (every? #(or (placed %) (not (nodes %))) (dep-fn n)))
                            remaining)
              ready (if (seq ready) ready [(first (sort remaining))])]
          (recur (into order ready) (into placed ready) (reduce disj remaining ready)))))))

(defn- healthy-def?
  "True when the `:defs` index `defs` records a def for var-key k. (There is no longer
  a tombstone flag: a var no live form defines simply has no :defs entry.)"
  [defs k]
  (some? (get defs k)))

(defn file-def-vars
  "The fully-qualified name symbols model value `m` records a `def` form for IN file
  `source`, keyed off each def's span :source. Exactly the population prune-file! may
  consider: only vars the compiler saw defined by a top-level def can be judged
  'deleted' by disappearance.

  READ OFF THE FILE'S OWN FORMS and not by walking every def in the model, which is
  what it did and what cost 346 ms of a 40-file reload over a 400-file model: it is
  asked once per file reloaded and again per file pruned, and the model it walked
  grows with the project while the file does not.

  The same answer, though, and the `:defs` lookup is what keeps it so: a name two
  files define belongs to the one whose def WON - the highest fid - so a file's own
  def form is in its answer only while `:defs` still names it as that def's file.
  Which is what filtering the whole index by span source said."
  [m source]
  (let [defs  (index m :defs)
        forms (:forms m)]
    (into #{} (for [fid     (get (:source->forms m) source)
                    ^Span s (:defs (get forms fid))
                    :let    [k (.entity s)]
                    :when   (= source (:source (:span (get defs k))))]
                k))))

(defn file-def-var-snapshot
  "Capture {qsym -> the currently-interned Var object} for the defs in file `source`.
  This is prune-file!'s `prior`; take it *before* the reload so that, since vars are
  keyed by name (not identity), prune can still tell a lingering deleted-def var (the
  SAME Var object survives a reload) from one the reloaded source deleted and
  re-created under a fresh identity (which must be preserved)."
  [m source]
  (into {} (for [k (file-def-vars m source)
                 :let [home (find-ns (symbol (namespace k)))
                       v    (when home (get (ns-interns home) (symbol (name k))))]]
             [k v])))

(defn- protocol-methods-gone
  "The qsyms of the method vars protocol var `pv` no longer names.

  Its methods are the vars interned in its own namespace whose `:protocol` is this
  very var - identity, so a var that merely carries the key is not one of them - and
  a method is gone when the protocol no longer names it: all of them when the
  protocol itself has just been unmapped (`deleted?`), and those missing from its
  `:sigs` when it is still there.

  Which is the one thing `prior` cannot answer. A method var is created by `intern`
  and is never a `def`, so the model records nothing about it and disappearance
  cannot be read off the model - but it does not have to be, because the protocol is
  its own record of what it defines."
  [pv deleted?]
  (let [^clojure.lang.Namespace home (.ns ^clojure.lang.Var pv)
        named (when-not deleted?
                (set (map name (keys (:sigs (protocol-value pv))))))]
    (for [[sym v] (ns-interns home)
          :when (and (var? v)
                     (identical? pv (:protocol (meta v)))
                     (or deleted? (not (named (name sym)))))]
      (symbol (name (ns-name home)) (name sym)))))

(defn- unmap-everywhere!
  "Unmap every mapping to one of `vars`, wherever a namespace maps it.

  One sweep over what every namespace maps, rather than each var's home namespace
  alone: the interned name is in the `ns-map` of its own namespace, a `:refer` of it
  is in the `ns-map` of the namespace that referred it, and a refer taken under
  another name is in there under that name. One rule finds all three, and finds each
  by the name it is actually written as. Leaving the referred ones behind would leave
  the name resolving in every file that referred it while the file that defined it no
  longer says it - which is the state pruning exists to get out of, and the one the
  referring file would then be compiled against next time something loaded it.

  By VAR IDENTITY, never by name: a namespace that happens to map the same name to a
  var of its own keeps it. The scan is over `ns-map` and not `ns-refers` because both
  cost a walk of the same mappings, and one of them also answers for the home.

  A walk of every mapping in the process is not free, and it is not paid for either:
  nothing is swept when nothing was pruned, which is every reload but one that
  followed somebody deleting a definition."
  [vars]
  (when (seq vars)
    (doseq [^clojure.lang.Namespace ns (all-ns)
            [sym v] (ns-map ns)
            :when (contains? vars v)]
      (ns-unmap ns sym))))

(defn- prune-vars!
  "What `prune-file!` does, without the precondition it checks - see it.

  Called directly for a file the disk no longer has, whose forms have just been
  retracted: `prune-file!` would refuse that file, and refuse it for the right
  reason (a file with no forms is normally one nothing has analysed), but a file
  just retracted is the one case where no forms is the answer rather than the
  question. Everything `prior` holds is gone, since nothing defines any of it any
  more, and every protocol the file defined is a deleted one."
  [source prior]
  (let [m        @model
        ;; `:defs` and nothing else, because that is all it takes to say whether a
        ;; def has gone. The usage index is what the warning below reads, and it is
        ;; forced only once something has actually been pruned - which is every
        ;; reload but one that followed somebody deleting a definition.
        defs     (index m :defs)
        interned (fn [k]
                   (when-let [home (find-ns (symbol (namespace k)))]
                     (get (ns-interns home) (symbol (name k)))))
        gone     (vec (for [[k old-var] prior
                            :let [cur (interned k)]
                            :when (and old-var (identical? cur old-var)
                                       (not (healthy-def? defs k)))]
                        k))
        ;; and then the protocol methods, which no snapshot could have held: the
        ;; protocols this file no longer defines lose all of theirs, and the ones it
        ;; still defines lose the methods they stopped naming.
        pruned-protocols (for [k gone
                               :let [v (get prior k)]
                               :when (protocol-value v)]
                           [v true])
        live-protocols   (for [k (file-def-vars m source)
                               :let [v (interned k)]
                               :when (protocol-value v)]
                           [v false])
        methods  (vec (distinct (mapcat (fn [[v deleted?]]
                                          (protocol-methods-gone v deleted?))
                                        (concat pruned-protocols live-protocols))))
        pruned   (into gone methods)
        ;; Read while they are all still interned: the sweep works by identity, and
        ;; unmapping one of them as we went would take away the answer to where the
        ;; rest of its mappings are.
        vars     (into #{} (keep interned) pruned)]
    (when (seq pruned)
      (let [usages (index m :usages)]
        (doseq [k pruned]
          (when-let [us (seq (remove :dead (get usages k)))]
            (binding [*out* *err*]
              (println "WARN: pruning" (str k) "still referenced at"
                       (vec (for [s us] [(some-> (:from-ns s) ns-name)
                                         (:line s) (:column s)]))))))))
    (unmap-everywhere! vars)
    ;; AFTER the unmapping and not before it: what this says is that the name has
    ;; gone, and it has not gone until it is gone. A reload is the one thing that
    ;; takes a definition away without anybody having typed anything, so it is the
    ;; one that has to say so - see `*defined*'.
    (doseq [k pruned]
      (defined! {:dialect :clj :op :remove :ns (symbol (namespace k)) :var k}))
    pruned))

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
  Returns the pruned qsyms, the protocol methods among them.

  Unmapped WHEREVER IT IS MAPPED, and not in its home namespace alone: a `:refer` is
  a mapping of its own in the namespace that took it, and one left behind would go
  on resolving there to a definition the source no longer has. See
  `unmap-everywhere!`.

  Model-side, nothing to do here: load-file!'s retract already dropped the vanished
  def's form, so the derived :defs no longer records a def for it (its usages, living
  on other files' forms, are untouched). This only reconciles the live namespace:
  `require :reload` / `load` re-def existing vars but never *remove* a var whose def
  was deleted, so the interned var would linger and shadow the source.

  Gating on `prior` (not `ns-interns` minus :defs) is deliberate: vars never recorded
  as a `def` are never candidates, so intern-created vars are left alone. Everything
  a `def` form makes is one, expansion included - `defonce`, `defmulti`, `declare`, a
  `deftype`'s `->T` and `map->T`, a `defprotocol`'s own var - since each of those
  compiles to a DefExpr the sink saw.

  A `defprotocol`'s METHOD vars are the exception, and they are pruned by a second
  sweep rather than by `prior`: they are interned and never def-ed, so the model
  records nothing to miss, and what says a method is gone is the protocol itself -
  see `protocol-methods-gone`. The sweep runs over the protocols this file defines,
  those it stopped defining included, and it is guarded by var identity the way the
  first one is. A var an explicit `intern` made is still left alone: nothing records
  it and nothing else says it has gone, and `ns-unmap` by hand is the answer for it.

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
  (prune-vars! source prior))

(defn- forget-lib!
  "Take namespace `n` out of the set `require` consults, so that requiring it loads
  it again rather than answering that it is already there.

  A namespace whose file has gone is not loaded, in the only sense the word has
  here: nothing on the classpath defines it. `require` is the one thing that would
  go on saying otherwise - silently, and for the life of the process - and a file
  written back is then a file `require` refuses to read.
  (`clojure.tools.namespace` does the same thing, for the same reason, when it
  drops a deleted file.)

  It is the `ns` form in the file that put the name there, whatever it was that
  loaded the file - a `require`, a `load`, this model's own reload - so taking it
  out is undoing what the file did rather than second-guessing whoever loaded it.

  The namespace object itself is left standing, with whatever it still maps. What
  goes is decided a definition at a time, each because the model says the source
  stopped making it; `remove-ns` decides nothing - it would take the namespace's
  aliases, its imports and every var an `intern` made in it, none of which the model
  speaks for."
  [n]
  (dosync (commute @#'clojure.core/*loaded-libs* disj n))
  nil)

(defn- drop-deleted-file!
  "Drop file `source`, whose file the disk no longer has: its forms leave the model,
  and with `prune` its definitions leave the process.

  The model side is unconditional - it is a record of what was read out of files,
  and a file that cannot be read is not something it can go on answering for. A
  `definition` pointing into a file an editor cannot open is worse than no answer,
  and a reload that leaves it there leaves it there for good, since nothing will
  ever flag a gone file as changed.

  The process side is what `prune` asks for, and it is the same pruning a reloaded
  file gets, with the whole file playing the part of the deleted def: every var the
  file defined is one no live form defines now, so all of them go, wherever they are
  mapped. Their namespaces stop being loaded libs - see `forget-lib!` - unless some
  other file still defines them, which a file that shared a namespace with this one
  does.

  The order is the ClojureScript side's, and for its reason: the definitions of a
  file that is gone are taken away BEFORE the stale files are loaded, so that a file
  still using one of them says so, rather than compiling clean against a definition
  from a file nobody can open."
  [source prune]
  (let [nss   (file-namespaces source)
        prior (when prune (file-def-var-snapshot @model source))]
    (retract-file! source)
    (when prune
      (doseq [n nss :when (empty? (ns-forms n))] (forget-lib! n))
      (prune-vars! source prior))
    nil))

(def ^:dynamic *reload-progress*
  "Where a reload says what it is doing while it does it, or nil.

  A function of one map. reload-files! calls it before each pass and before each
  file; stale-reload! calls it for the files it drops as gone. The maps are:

    {:event :plan    :pass n :files [source ...]}   about to load these, in this order
    {:event :loading :pass n :file source :nth i :of n}
    {:event :deleted :files [source ...]}           these are gone and are being dropped

  clojure.cljs.analysis reports a ClojureScript reload through this same var and
  adds :dialect :cljs to its own events, because half of such a reload is Clojure
  macro files loaded here - so a watcher that bound two vars would see half of one
  reload in each, in no particular order relative to the other half. One stream,
  in the order things happen; an event with no :dialect came from this side.

  Nil by default, and called for its effect: a reload that nobody is watching costs
  nothing, and what a watcher does with an event is none of this namespace's
  business. A caller that wants the events printed binds it to something that
  prints - which is what a REPL does, so that a reload of forty files is forty lines
  arriving as they happen rather than one vector at the end.

  WHY THE EVENTS ARE NOT JUST THE RETURN VALUE. reload-files! already answers the
  order it loaded, and that answer arrives when the loading has finished - which is
  exactly the moment it stops being useful. What a person wants from a reload that
  takes twenty seconds is to see it moving, and what they want from one that never
  comes back is the name of the file it is inside; both are questions about the
  middle, and only something called from the middle can answer them.

  Dynamic, so that the binding belongs to the thread doing the reload. Two REPLs
  reloading at once are two threads, each printing into its own connection, and a
  root binding would send both to whichever was set last.

  Exceptions out of it are not caught. It is the caller's own function, called on
  the caller's own thread, and a reload that failed because the thing watching it
  threw is a failure worth seeing rather than swallowing."
  nil)

(defn- told!
  "Tell *reload-progress* about `event`, if anything is listening."
  [event]
  (when-let [f *reload-progress*] (f event))
  nil)

(defn- topo-respected?
  "True when `order` already loads every file after all its deps (per dep-fn).
  Deps outside `order` are ignored - they were not reloaded, so they are current."
  [order dep-fn]
  (let [idx (zipmap order (range))]
    (every? (fn [x] (every? (fn [y] (or (nil? (idx y)) (< (idx y) (idx x))))
                            (dep-fn x)))
            order)))

(defn reload-files!
  "Reload `files` (classpath-relative source paths) via load-file! in dependency
  (topological) order - a file before the files that re-expand its macros, before
  the files that re-resolve the classes its defs generate, and before the files that
  refer to the vars it defines - and optionally prune vanished vars
  (:prune true). Returns the
  final reload order (a vector of source paths). stale-reload! is this over
  stale-files; clojure.cljs.analysis calls it over the macro files a ClojureScript
  compile depends on.

  Fail-fast, like require: if a file fails to compile, load-file! re-throws and the
  reload stops there (files later in the order, and the second pass, do not run).
  This is intentional - it surfaces the error immediately. No staleness is lost:
  load-file! advances a file's mtime baseline only on a successful load, so the
  failed file and any not yet reached stay stale (see changed-files) and are retried
  on the next stale-reload! call.

  THE ORDER IS OVER MORE THAN THE STALE CASCADE IS. What is stale is a question
  about compile-time coupling alone (`file-compile-graph`), because a file that just
  calls a var re-resolves it at run time and needs no reload. What ORDER to load in
  is not: a var that does not exist yet is resolved at compile time and fails there,
  so a plain var reference between two files that are BOTH being reloaded does
  constrain them. `file-var-graph` supplies those edges, for the ordering only - no
  extra file is loaded because of one.

  Two-pass, to handle a dependency introduced by the very edit being reloaded. The
  first-pass order comes from the pre-reload graph, which cannot yet know an edge
  only this edit adds (file A newly requires and expands a macro from file B, or
  newly implements a protocol of B's): A could be ordered before B and expand B's
  stale macro, or be compiled against the interface B is about to generate again.
  Pass 1 reloads in that best-guess order, which recompiles every edited file and so
  completes the graph. We then recompute the order; if pass 1 already respected it
  (the common case) we are done at no extra cost, otherwise we reload once more in
  the corrected order. Two passes always suffice: after pass 1 the on-disk source is
  fixed and every edited file analysed, so the recomputed graph - and its order - is
  stable.

  THE ORDER IS PART MODEL AND PART DISK, for one reason. The model's graphs are
  built from what the compiler recorded the last time these files were loaded, so
  they hold every edge the OLD sources had and none that the edit introduces - and
  an edit that first reaches into a file the editing file never touched before is
  the one whose order matters most, since the definition it has come for was not
  there before. So the `ns` forms of the new sources are read as well
  (`file-require-graph`), which is where a reach like that is declared.

  Limitation: what is read off the disk is the `ns` form, so a dependency taken
  without one - a `require` called at run time, a fully-qualified name in a file
  that never mentions the namespace at the top - is not in the order unless the old
  sources already had it. The reader is also asked for one form and not for a
  judgment: a file it cannot read contributes no edges rather than an error, and is
  left to the compiler to complain about a moment later."
  [files & {:keys [prune]}]
  (let [dep-fn  (fn [g] (fn [s] (get g s #{})))
        reload! (fn [pass order]
                  ;; Announced before the first file rather than a file at a time,
                  ;; because the order is the half nobody can work out: what needs
                  ;; compiling is not what was edited, and it is known here, now,
                  ;; before any of it has cost anything.
                  (told! {:event :plan :pass pass :files order})
                  (let [n (count order)]
                    (doseq [[i source] (map-indexed vector order)]
                      ;; BEFORE the file and not after it. A file that never
                      ;; finishes compiling is the one worth naming, and a line
                      ;; printed after a load names every file except that one.
                      (told! {:event :loading :pass pass :file source
                              :nth (inc i) :of n})
                      ;; Snapshot the file's def-vars (with their Var identities) BEFORE
                      ;; load-file! retracts them, so prune can tell which def forms
                      ;; vanished - and preserve any re-created afresh (see prune-file!).
                      (let [prior (when prune (file-def-var-snapshot @model source))]
                        (load-file! source)
                        (when prune (prune-file! source prior))))))
        stale   (set files)
        ;; Read once, before anything is loaded: the sources on disk are the new
        ;; ones from here until the reload is over, so the answer cannot change
        ;; under it, and reading them again for the second pass would only cost.
        reqs    (file-require-graph @model stale)
        graph   (fn []
                  (let [m @model]
                    (merge-with into
                                (file-compile-graph m)
                                (file-var-graph m stale)
                                reqs)))
        order1  (topo-order stale (dep-fn (graph)))]
    (reload! 1 order1)
    ;; Pass 1 read every edited source, so the graph now holds the edges the edit
    ;; added - macro, class and var alike; re-derive the order from it.
    (let [df (dep-fn (graph))]
      (if (topo-respected? order1 df)
        order1
        (let [order2 (topo-order stale df)]
          (reload! 2 order2)
          order2)))))

(defn stale-reload!
  "Stale reload (design §9.2): reload-files! over the stale set (stale-files -
  changed files + their transitive compile-time dependents, the files that expand
  their macros and the files that name the classes their defs generate), in
  dependency order, optionally pruning vanished vars (:prune true). Returns
  the final reload order (a vector of source paths). Fail-fast, two-pass - see
  reload-files!.

  And the files that are gone are dropped first (deleted-files, drop-deleted-file!).
  A deleted file cannot be reloaded, so it is in neither the answer nor the set that
  is loaded - it never seeds the cascade, and `stale-files` takes it back out when
  another file's edit reaches it as a dependent, which is what a branch switch does:
  the files that expanded its macros are left holding an expansion of a macro
  nothing defines, which is what their source now says and what they will say the
  next time anything compiles them. What a gone file defined stops resolving
  with :prune, before the stale files are loaded, so one of them still using it
  fails where it uses it rather than compiling clean against a file nobody can open.

  Both sets are read before anything is dropped or loaded, since dropping a file
  changes the macro graph the order comes from."
  [& {:keys [prune]}]
  (let [deleted (deleted-files)
        ;; The one reading of the disk both answers come from: what is gone is what
        ;; is dropped, and it is also what must not be in what is loaded.
        stale   (stale-files (changed-files) deleted)]
    (when (seq deleted) (told! {:event :deleted :files (vec (sort deleted))}))
    (doseq [source (sort deleted)] (drop-deleted-file! source prune))
    (reload-files! stale :prune prune)))

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
