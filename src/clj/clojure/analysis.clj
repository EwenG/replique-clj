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
;;   :usages  {target-var #{ {:from-ns :source :line :column} ... }}
;;   :defs    {var         {:source :line :column} }
(defonce ^:private model (atom {:usages {} :defs {}}))

(deftype AnalysisSink []
  IAnalysisSink
  (varUsage [_ target from-ns source line column]
    (swap! model update-in [:usages target] (fnil conj #{})
           {:from-ns from-ns :source source :line line :column column})
    nil)
  (varDef [_ v source line column]
    (swap! model assoc-in [:defs v] {:source source :line line :column column})
    nil))

(defn reset-model!
  "Clear the model. Cold-load driver: start from empty (see design §8)."
  []
  (reset! model {:usages {} :defs {}}))

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

(defn snapshot
  "The whole model, for inspection/tests."
  []
  @model)
