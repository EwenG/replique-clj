;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "In-memory semantic model populated by the compiler's analysis sink.

  Layer 0 of the analysis feature: captures var definitions and var usages
  across namespaces. Install the sink with run-analysis (or manually via
  push-thread-bindings on clojure.lang.Compiler/ANALYSIS_SINK) and any
  compilation it triggers (load, require, eval) populates the model. Query it
  with find-usages and definition.

  See doc/analysis-and-reload.md for the full design."
      :author "replique-clj"}
    clojure.analysis
  (:import [clojure.lang IAnalysisSink Compiler Var]))

;; model:
;;   :usages  {target-var #{ {:from-ns :source :line :column :end-line :end-column} ... }}
;;   :defs    {var         {:source :line :column :end-line :end-column} }
;;   :locals  {binding-id  {:ns :name :source :line :column ... :uses #{spans}} }
;;   :keyword-usages {kw   #{ {:from-ns :source :line :column ...} } }
;;   :class-usages   {class #{ {:from-ns :source :line :column ...} } }
;;   :macro-deps     {ns-sym #{macro-var}}   compile-time dependency edges (§9)
;;
;; Note: :locals is keyed by the compiler's LocalBinding identity and is not
;; yet lifecycle-managed (generation clearing is design §7 / Layer 5), so
;; reset-model! between analysis runs during long sessions.
(def ^:private empty-model
  {:usages {} :defs {} :locals {} :keyword-usages {} :class-usages {} :macro-deps {}})
(defonce ^:private model (atom empty-model))

(defn- span [source line column end-line end-column]
  (cond-> {:source source :line line :column column}
    (nat-int? end-line)   (assoc :end-line end-line)
    (nat-int? end-column) (assoc :end-column end-column)))

(deftype AnalysisSink []
  IAnalysisSink
  (varUsage [_ target from-ns source line column end-line end-column]
    (swap! model update-in [:usages target] (fnil conj #{})
           (assoc (span source line column end-line end-column) :from-ns from-ns))
    nil)
  (varDef [_ v source line column end-line end-column]
    (swap! model assoc-in [:defs v] (span source line column end-line end-column))
    nil)
  (localDef [_ binding name ns source line column end-line end-column]
    (swap! model update-in [:locals binding]
           (fn [cur]
             (merge (span source line column end-line end-column)
                    {:ns ns :name name :uses (get cur :uses #{})})))
    nil)
  (localUsage [_ binding ns source line column end-line end-column]
    (swap! model update-in [:locals binding :uses] (fnil conj #{})
           (assoc (span source line column end-line end-column) :ns ns))
    nil)
  (keywordUsage [_ kw from-ns source line column end-line end-column]
    (swap! model update-in [:keyword-usages kw] (fnil conj #{})
           (assoc (span source line column end-line end-column) :from-ns from-ns))
    nil)
  (classUsage [_ c from-ns source line column end-line end-column]
    (swap! model update-in [:class-usages c] (fnil conj #{})
           (assoc (span source line column end-line end-column) :from-ns from-ns))
    nil)
  (macroExpansion [_ macro from-ns source line column end-line end-column]
    (swap! model
           (fn [m]
             (-> m
                 (update-in [:usages macro] (fnil conj #{})
                            (assoc (span source line column end-line end-column)
                                   :from-ns from-ns :macro true))
                 (update-in [:macro-deps (ns-name from-ns)] (fnil conj #{}) macro))))
    nil))

(defn reset-model!
  "Clear the model. Cold-load driver: start from empty (see design §8)."
  []
  (reset! model empty-model))

(defn run-analysis
  "Invoke thunk with the analysis sink installed on this thread, so any
  compilation it triggers (load, require, eval) populates the model."
  [thunk]
  (push-thread-bindings {Compiler/ANALYSIS_SINK (->AnalysisSink)})
  (try (thunk) (finally (pop-thread-bindings))))

(defn find-usages
  "Usage sites recorded for var v: a set of {:from-ns :source :line :column}."
  [^Var v]
  (get-in @model [:usages v]))

(defn definition
  "Definition site recorded for var v: {:source :line :column}, or nil."
  [^Var v]
  (get-in @model [:defs v]))

(defn find-keyword-usages
  "Occurrence sites recorded for keyword kw: a set of
  {:from-ns :source :line :column :end-line :end-column}. Auto-resolved
  keywords are indexed fully-qualified, so pass e.g. (keyword \"my.ns\" \"x\")."
  [kw]
  (get-in @model [:keyword-usages kw]))

(defn macro-deps
  "Compile-time macro dependency edges. With no arg, the whole map
  {ns-sym #{macro-var}}; with a namespace symbol, the set of macro vars that
  namespace expanded. Drives macro-aware stale reload (design §9)."
  ([] (:macro-deps @model))
  ([ns-sym] (get-in @model [:macro-deps ns-sym] #{})))

(defn find-class-usages
  "Occurrence sites recorded for class c (a java.lang.Class): a set of
  {:from-ns :source :line :column :end-line :end-column}."
  [c]
  (get-in @model [:class-usages c]))

(defn unused-locals
  "Source-written local bindings that have no recorded reference. Optionally
  restrict to a namespace (a symbol). Each result is the binding's def site
  plus :name and :ns."
  ([] (unused-locals nil))
  ([ns-sym]
   (for [[_ info] (:locals @model)
         :when (empty? (:uses info))
         :when (or (nil? ns-sym) (= ns-sym (ns-name (:ns info))))]
     (dissoc info :uses))))

;; --- Requires / imports (design §4 Layer 2: read from live namespace state,
;; combined with the usage model, rather than parsing ns forms) -------------

(defn- default-imports
  "The java.lang.* classes every namespace auto-imports; excluded from
  unused-import so only user :imports are considered."
  []
  (set (vals (ns-imports (create-ns (gensym "clojure.analysis._blank"))))))

(defn ns-referenced-namespaces
  "Set of namespace-name symbols whose vars or (namespaced) keywords are
  referenced from ns-sym, per the model."
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
  "Aliases established in ns-sym (via :as / :as-alias) whose target namespace
  has no var or namespaced-keyword reference from ns-sym. Returns {alias ns-sym}."
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
  (let [defaults (default-imports)
        used? (fn [c] (some #(= ns-sym (some-> (:from-ns %) ns-name)) (find-class-usages c)))]
    (into {} (for [[sym c] (ns-imports ns-sym)
                   :when (and (not (contains? defaults c)) (not (used? c)))]
               [sym c]))))

(defn snapshot
  "The whole model, for inspection/tests."
  []
  @model)
