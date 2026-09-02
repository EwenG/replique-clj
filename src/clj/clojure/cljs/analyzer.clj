;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "ClojureScript form -> AST.

  The AST is a tree of maps with an :op, mirroring cljs.analyzer's node shapes so
  that analysing the same form both ways and diffing is a usable oracle
  (doc/cljs-compiler.md §6). Mirrored: :op names, the structural keys (:test
  /:then/:else, :bindings/:body, :statements/:ret, :segs/:args) and :children.
  Not mirrored: everything tag inference produces - :tag, :inferred-ret-tag,
  :numeric, :jsdoc - which §7 defers, and which would make every diff noisy.

  Deliberately partial. This is the M2 seed: enough to take one expression all the
  way to running JavaScript. analyze throws, naming what it saw, on anything not
  yet handled, rather than guessing - the special forms arrive one at a time, each
  with the oracle behind it.

  Two jobs beyond shape. Locals are renamed here, not in the emitter: every
  binding gets a name unique within its top-level form, because the emitter
  flattens nested scopes into one JavaScript scope (see clojure.cljs.emitter) and
  two `x`es would collide. The names stay Clojure symbols; munging them into legal
  JavaScript is the emitter's job.

  And macroexpansion runs here, so an analyzed form has already been through the
  two macro worlds (clojure.cljs.macroexpand)."}
  clojure.cljs.analyzer
  (:require [clojure.cljs.macroexpand :as mx]))

(def ^:dynamic *local-counter*
  "Per-top-level-form counter making local names unique. Bound by analyze-top, so
  the same form always analyses to the same names - the emitted JavaScript is
  reproducible, which matters more for testing than pretty names do."
  nil)

(defn- unique-local
  "A name for `sym` that no other binding in this top-level form will take."
  [sym]
  (symbol (str (name sym) "__" (swap! *local-counter* inc))))

(declare analyze)

;; --- literals ---------------------------------------------------------------

(defn- const-node [env form]
  {:op :const :val form :form form :env env :children []})

;; --- special forms ----------------------------------------------------------

(defn- parse-if [cenv env form]
  (let [[_ test then else] form]
    (when (< (count form) 3)
      (throw (ex-info "Too few arguments to if" {:form form})))
    (when (> (count form) 4)
      (throw (ex-info "Too many arguments to if" {:form form})))
    {:op :if :form form :env env
     :test (analyze cenv env test)
     :then (analyze cenv env then)
     :else (analyze cenv env else)
     :children [:test :then :else]}))

(defn- parse-do [cenv env form]
  (let [exprs (rest form)
        stmts (butlast exprs)
        ret   (last exprs)]
    {:op :do :form form :env env
     :statements (mapv #(analyze cenv env %) stmts)
     :ret (if (seq exprs) (analyze cenv env ret) (const-node env nil))
     :children [:statements :ret]}))

(defn- parse-let [cenv env form]
  (let [[_ bindings & body] form]
    (when-not (and (vector? bindings) (even? (count bindings)))
      (throw (ex-info "let* requires a vector of an even number of forms"
                      {:form form})))
    (loop [pairs (partition 2 bindings), env env, nodes []]
      (if-let [[sym init] (first pairs)]
        (do
          (when-not (simple-symbol? sym)
            (throw (ex-info (str "Bad binding form: " sym) {:form form})))
          (let [init-node (analyze cenv env init)
                js-name   (unique-local sym)
                node      {:op :binding :name sym :js-name js-name :local :let
                           :init init-node :form sym :env env :children [:init]}]
            (recur (rest pairs)
                   ;; each init sees the bindings before it, not itself
                   (assoc-in env [:locals sym] node)
                   (conj nodes node))))
        {:op :let :form form :env env
         :bindings nodes
         :body (parse-do cenv env (cons 'do body))
         :children [:bindings :body]}))))

(defn- parse-js
  "(js* \"~{} + ~{}\" a b) - the escape hatch into raw JavaScript, and the reason
  this seed needs no core library to compute anything."
  [cenv env form]
  (let [[_ tmpl & args] form]
    (when-not (string? tmpl)
      (throw (ex-info "js* requires a string template" {:form form})))
    {:op :js :form form :env env
     :segs (vec (.split ^String tmpl "~\\{\\}" -1))
     :args (mapv #(analyze cenv env %) args)
     :children [:args]}))

(defn- binding-node [env sym local-kind]
  (when-not (simple-symbol? sym)
    (throw (ex-info (str "Bad binding form: " sym) {:sym sym})))
  {:op :binding :name sym :js-name (unique-local sym) :local local-kind
   :form sym :env env :children []})

(defn- parse-fn-method
  "One ([params] body...) of an fn*. The rest parameter, if any, is the last entry
  of :params - :fixed-arity counts the ones before it, exactly as cljs.analyzer
  does, so arity dispatch reads off the node without re-scanning the params."
  [cenv env form]
  (let [[params & body] form]
    (when-not (vector? params)
      (throw (ex-info "fn* method requires a parameter vector" {:form form})))
    (let [amp       (.indexOf ^java.util.List params '&)
          variadic? (not (neg? amp))
          _         (when (and variadic? (not= amp (- (count params) 2)))
                      (throw (ex-info "& must be followed by exactly one parameter"
                                      {:form form})))
          fixed     (if variadic? (subvec params 0 amp) params)
          rest-sym  (when variadic? (peek params))
          bindings  (mapv #(binding-node env % :arg) (cond-> fixed rest-sym (conj rest-sym)))
          env'      (update env :locals into (map (juxt :name identity)) bindings)]
      {:op :fn-method :form form :env env
       :params bindings
       :fixed-arity (count fixed)
       :variadic? variadic?
       :body (parse-do cenv env' (cons 'do body))
       :children [:params :body]})))

(defn- parse-fn [cenv env form]
  (let [more     (rest form)
        fn-name  (when (simple-symbol? (first more)) (first more))
        more     (if fn-name (rest more) more)
        ;; (fn* [x] body) is sugar for (fn* ([x] body))
        method-forms (if (vector? (first more)) (list more) more)
        ;; the name is in scope inside the methods, so a self-call resolves
        name-b   (when fn-name (binding-node env fn-name :fn))
        env'     (cond-> env name-b (assoc-in [:locals fn-name] name-b))
        methods  (mapv #(parse-fn-method cenv env' %) method-forms)]
    (when (empty? methods)
      (throw (ex-info "fn* requires at least one method" {:form form})))
    (when (< 1 (count (filter :variadic? methods)))
      (throw (ex-info "fn* can have only one variadic method" {:form form})))
    (let [arities (map :fixed-arity methods)]
      (when-not (apply distinct? arities)
        (throw (ex-info "fn* methods cannot have the same arity" {:form form}))))
    (cond-> {:op :fn :form form :env env
             :methods methods
             :variadic? (boolean (some :variadic? methods))
             :max-fixed-arity (apply max (map :fixed-arity methods))
             :children [:methods]}
      name-b (assoc :name name-b :local name-b :children [:local :methods]))))

(defn- parse-invoke [cenv env form]
  {:op :invoke :form form :env env
   :fn (analyze cenv env (first form))
   :args (mapv #(analyze cenv env %) (rest form))
   :children [:fn :args]})

(def ^:private parsers
  {'if parse-if, 'do parse-do, 'let* parse-let, 'js* parse-js, 'fn* parse-fn})

;; --- entry ------------------------------------------------------------------

(defn- unsupported [form what]
  (throw (ex-info (str "Not implemented yet: " what
                       ". This analyzer handles " (pr-str (sort (keys parsers)))
                       ", function application, locals and literals.")
                  {:form form})))

(defn- analyze-symbol [cenv env sym]
  (if-let [b (get-in env [:locals sym])]
    {:op :local :name sym :js-name (:js-name b) :local (:local b)
     :form sym :env env :children []}
    (unsupported sym (str "the symbol " sym " is not a local"))))

(defn- analyze-seq [cenv env form]
  (let [form' (mx/macroexpand-1 cenv env form)]
    (if-not (identical? form form')
      (analyze cenv env form')
      (let [op (first form)]
        (if-let [parse (get parsers op)]
          (parse cenv env form)
          ;; anything else in head position is a function call. An unresolvable
          ;; head symbol fails in analyze-symbol, which says so precisely.
          (parse-invoke cenv env form))))))

(defn analyze
  "AST for `form` in `env`. Macroexpands first, so callers hand in source."
  [cenv env form]
  (cond
    (seq? form)    (if (seq form) (analyze-seq cenv env form) (const-node env form))
    (symbol? form) (analyze-symbol cenv env form)
    (or (nil? form) (number? form) (string? form)
        (boolean? form) (keyword? form)) (const-node env form)
    :else (unsupported form (str "a " (.getSimpleName (class form)) " literal"))))

(defn analyze-top
  "Analyze one top-level form, with a fresh local-name counter."
  [cenv env form]
  (binding [*local-counter* (atom 0)]
    (analyze cenv env form)))
