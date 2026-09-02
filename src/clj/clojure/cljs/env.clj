;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The ClojureScript compilation environment: two worlds and a cursor.

  ClojureScript is compiled by two languages at once. Its vars are ClojureScript
  and exist only as a symbol table; its macros are Clojure functions that run, on
  the JVM, at compile time. A namespace therefore has two sets of requires, and a
  symbol means different things depending on which side is asking.

  So a compile environment is:

    :world        a NamespaceWorld of ClojureScript namespaces holding
                  root-unbound Vars - the target's symbol table
    :macro-world  a NamespaceWorld of per-ClojureScript-namespace *views* onto
                  the JVM: aliases point at real loaded clojure.lang.Namespace
                  objects (:require-macros) and mappings hold real macro Vars
                  (:refer-macros / :use-macros / :rename-macros)
    :current-ns   an atom naming the namespace being compiled

  The macro world holds views, not namespaces of its own: nothing is ever interned
  into it, and every alias and mapping in it points into NamespaceWorld/DEFAULT,
  where macros actually live. That is the whole of the two-world arrangement -
  cljs.analyzer keeps the same information in nested maps under [::namespaces ns
  :require-macros], and resolves it against clojure.lang.Namespace at the end
  anyway (analyzer.cljc:4203, .findInternedVar on a JVM namespace).

  Populated here by hand. The (ns ...) special form owns this in the real front
  end, along with the rules that do not belong at this level - :refer-clojure
  :exclude, and the implicit \"a .cljs file may have a same-named .clj macro
  file\" self-require. See doc/cljs-compiler.md M3."}
  clojure.cljs.env
  (:import [clojure.lang Namespace NamespaceWorld Symbol Var]))

(def default-macro-ns-rewrites
  "Macro namespaces ClojureScript renames on the way through: clojure.core macros
  are cljs.core macros. Applied to the namespace part of a qualified symbol and to
  an alias's target, matching cljs.analyzer/get-expander-ns."
  '{clojure.core cljs.core
    clojure.repl cljs.repl})

(defrecord CompileEnv [^NamespaceWorld world
                       ^NamespaceWorld macro-world
                       current-ns
                       core-macros
                       macro-ns-rewrites])

(defn compile-env
  "A fresh compile environment.

    :ns                 namespace to start in, default 'cljs.user
    :core-macros        namespace consulted for any unqualified macro not referred
                        in - ClojureScript's is cljs.core. Loaded here, so a name
                        that does not exist fails now rather than as a silent
                        non-expansion later. Defaults to nil rather than 'cljs.core
                        because cljs.core is not vendored until M5.
    :macro-ns-rewrites  see default-macro-ns-rewrites"
  (^CompileEnv [] (compile-env nil))
  (^CompileEnv [{:keys [ns core-macros macro-ns-rewrites]
                 :or   {ns 'cljs.user
                        macro-ns-rewrites default-macro-ns-rewrites}}]
   (when core-macros
     (require core-macros))
   (->CompileEnv (NamespaceWorld.) (NamespaceWorld.) (atom ns)
                 core-macros macro-ns-rewrites)))

(defn current-ns
  "Symbol naming the namespace being compiled."
  ^Symbol [^CompileEnv cenv]
  @(:current-ns cenv))

(defn set-current-ns!
  "Move the cursor. A driver calls this as it processes each (ns ...) form; the
  reader's resolver and macro lookup both read it per form."
  [^CompileEnv cenv sym]
  (reset! (:current-ns cenv) sym)
  sym)

(defn cljs-ns
  "The ClojureScript namespace `sym`, created if absent. Its vars are
  root-unbound: a symbol table, never invoked."
  (^Namespace [^CompileEnv cenv] (cljs-ns cenv (current-ns cenv)))
  (^Namespace [^CompileEnv cenv sym] (.findOrCreate ^NamespaceWorld (:world cenv) sym)))

(defn macro-view
  "The macro-side view of ClojureScript namespace `sym`, created if absent - what
  that namespace can see of the JVM."
  (^Namespace [^CompileEnv cenv] (macro-view cenv (current-ns cenv)))
  (^Namespace [^CompileEnv cenv sym] (.findOrCreate ^NamespaceWorld (:macro-world cenv) sym)))

(defn require-macros!
  "Make the JVM namespace `jvm-ns` visible as macros to ClojureScript namespace
  `cljs-ns`, loading it first. `:as` adds an alias, `:refer` a collection of macro
  names to map directly. The hand-built form of (:require-macros ...) /
  (:refer-macros ...) until the ns special form exists.

  Refers are checked here: a name that is not an interned macro in `jvm-ns` throws
  now rather than silently failing to expand later."
  [^CompileEnv cenv cljs-ns jvm-ns & {:keys [as refer]}]
  (require jvm-ns)
  (let [^Namespace view (macro-view cenv cljs-ns)
        ^Namespace jns  (or (find-ns jvm-ns)
                            (throw (ex-info (str "No such macro namespace: " jvm-ns)
                                            {:ns jvm-ns})))]
    (when as
      (.addAlias view (symbol (name as)) jns))
    (doseq [sym refer]
      (let [v (.findInternedVar jns sym)]
        (when-not (and v (.isMacro ^Var v))
          (throw (ex-info (str jvm-ns "/" sym
                               (if v " is not a macro" " does not exist"))
                          {:ns jvm-ns :sym sym})))
        (.refer view sym v)))
    view))

;; --- the analysis environment handed to macros as &env ---------------------

(defn analysis-env
  "A fresh &env for the namespace `cenv` is currently in.

  ClojureScript's shape, minus what does not exist yet. :ns is a map so the usual
  (:name (:ns &env)) reads correctly; cljs.core's macros reach for (:locals &env),
  (:def-emits-var &env), (:async &env) and, at one site, (-> &env :ns :defs).
  Since we own the vendored core.cljc (doc/cljs-compiler.md §4.4), that last one is
  adaptable rather than binding."
  [^CompileEnv cenv]
  {:ns      {:name (current-ns cenv)}
   :locals  {}
   :context :statement})

(defn with-locals
  "Add locals to an &env. A local hides a macro of the same name, so this is not
  cosmetic. The value shape is minimal until the analyzer defines it."
  [env syms]
  (update env :locals into (map (fn [s] [s {:name s :op :local}])) syms))
