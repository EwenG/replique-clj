;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "Reading ClojureScript source with the vendored reader.

  The reader needs no ClojureScript-specific fork. Everything that resolves a
  symbol while reading - auto-resolved keywords (::kw, ::alias/kw), namespaced
  map literals (#::alias{}), and syntax-quote - already routes through
  clojure.lang.LispReader$Resolver when *reader-resolver* is bound, an extension
  point upstream added for exactly this purpose. WorldResolver below implements it
  against a NamespaceWorld, so those forms resolve in the ClojureScript symbol
  table rather than the JVM's.

  read-forms adds the three things the fork made switchable: the platform feature
  (:cljs instead of :clj, so reader conditionals take the right branch), source
  positions (recorded without an analysis sink), and #= disabled. See
  doc/cljs-compiler.md.

  Reading only. Nothing here evaluates, analyses, or interns: the forms come back
  as data with source spans attached, and it is the caller's job to advance
  *current-ns* as it processes each (ns ...) form."}
  clojure.cljs.reader
  (:require [clojure.cljs.env :as env])
  (:import [clojure.lang Compiler LispReader LispReader$Resolver
            LineNumberingPushbackReader Namespace NamespaceWorld Symbol Var]
           [java.io Reader StringReader]))

;; --- #js ------------------------------------------------------------------

(defrecord JSValue [val])

(defn read-js
  "Data reader for #js. Wraps the form rather than building anything: what
  #js [1 2] and #js {:a 1} become is the emitter's decision, not the reader's."
  [form]
  (->JSValue form))

;; --- resolution -----------------------------------------------------------

(deftype WorldResolver [^NamespaceWorld world current-ns]
  LispReader$Resolver

  ;; Never nil: LispReader dereferences this without a null check when reading
  ;; #::{...} (LispReader.java:783).
  (currentNS [_]
    @current-ns)

  ;; ClojureScript has no host classes, so a symbol is never a class name. Returning
  ;; nil here is what makes the reader fall through to alias resolution for Foo/bar
  ;; and leave js/Date alone.
  (resolveClass [_ _sym]
    nil)

  (resolveAlias [_ sym]
    (when-let [^Namespace ns (.find world ^Symbol @current-ns)]
      (when-let [^Namespace target (.lookupAlias ns sym)]
        (.getName target))))

  ;; A ClojureScript var is a root-unbound Var interned in a namespace of that world:
  ;; identity plus metadata, never invoked. Mappings cover both interned and
  ;; referred vars, so this resolves either.
  (resolveVar [_ sym]
    (when-let [^Namespace ns (.find world ^Symbol @current-ns)]
      (let [m (.getMapping ns sym)]
        (when (instance? Var m)
          (let [^Var v m]
            (Symbol/intern (str (.getName (.ns v))) (str (.sym v)))))))))

(defn resolver
  "A LispReader$Resolver resolving in `cenv`'s ClojureScript world, against
  whichever namespace `cenv` names at the moment each form is read."
  ^LispReader$Resolver [cenv]
  (->WorldResolver (:world cenv) (:current-ns cenv)))

;; --- reading --------------------------------------------------------------

(def ^:private reader-resolver-var
  "clojure.core/*reader-resolver* is interned by RT, not def'd in core.clj, so it
  has no reader syntax of its own here."
  (resolve 'clojure.core/*reader-resolver*))

(def ^:private cljs-data-readers
  (assoc default-data-readers 'js #'read-js))

(defn with-cljs-reader*
  "Invoke `thunk` with the vendored reader configured to read ClojureScript in
  `cenv`, resolving against whichever namespace `cenv` names.

  Four bindings, three of them the switches the fork added:
    *reader-resolver*   resolution goes to the ClojureScript world, not the JVM's
    PLATFORM_FEATURE    :cljs, replacing :clj, so #?(:clj a :cljs b) yields b
    RECORD_POSITIONS    spans on symbols/keywords/collections, with no sink
    *read-eval*         false - #= evaluates JVM code and has no place here"
  [cenv thunk]
  (with-bindings* {reader-resolver-var    (resolver cenv)
                   LispReader/PLATFORM_FEATURE :cljs
                   Compiler/RECORD_POSITIONS   true
                   #'*read-eval*          false
                   #'*data-readers*       cljs-data-readers}
    thunk))

(def ^:private EOF (Object.))

(defn read-forms
  "Every top-level form of ClojureScript source `src` (a string or Reader), read in
  `cenv`.

  The current namespace is read before each form, so a caller processing forms as
  it goes can env/set-current-ns! on an (ns ...) and have the rest of the file
  resolve correctly. Reading a whole file up front leaves every form resolved
  against the namespace that was current when reading started - fine for a
  single-namespace file, wrong for one that switches."
  [cenv src]
  (let [rdr  (LineNumberingPushbackReader.
              (if (string? src) (StringReader. ^String src) ^Reader src))
        opts {:read-cond :allow :eof EOF}]
    (with-cljs-reader* cenv
      (fn []
        (loop [forms []]
          (let [form (read opts rdr)]
            (if (identical? form EOF)
              forms
              (recur (conj forms form)))))))))
