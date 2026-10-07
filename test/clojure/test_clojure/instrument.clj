;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns clojure.test-clojure.instrument
  "Tests for `Compiler/INSTRUMENT`: code compiled to be stepped through says what
  each form it was written with evaluated to, and that each fn was entered - and
  otherwise computes what it always did.

  Each test reads its code with positions on, as a client does, compiles it with
  INSTRUMENT bound to a site function that numbers the sites and a hook that
  records what it is told, and checks both the value and the record."
  (:use clojure.test)
  (:import [clojure.lang Compiler LineNumberingPushbackReader]))

(declare inst-f inst-t inst-m inst-p inst-c inst-r inst-s inst-n)

(def ^:private sites (atom {}))
(def ^:private told (atom []))

(defn hook
  "What instrumented code calls, recording what it says."
  ([id] (swap! told conj [:enter (get-in @sites [id :outermost])]))
  ([id v] (swap! told conj [(get-in @sites [id :text]) v])))

(defn- site [{:keys [form] :as s}]
  (let [id (count @sites)]
    (swap! sites assoc id (assoc (dissoc s :form) :text (pr-str form)))
    id))

(defn- read-with-positions [s]
  (with-bindings {Compiler/RECORD_POSITIONS true}
    (read (LineNumberingPushbackReader. (java.io.StringReader. s)))))

(defn- instrumented-eval
  "Evaluate the code S, compiled to be stepped through."
  [s]
  (let [form (read-with-positions s)]
    (with-bindings {Compiler/INSTRUMENT {:site site :hook #'hook}}
      (binding [*ns* (the-ns 'clojure.test-clojure.instrument)]
        (eval form)))))

(defn- told-of
  "What running F told the hook, with what F returned."
  [f]
  (reset! told [])
  (let [v (f)]
    [v @told]))

(use-fixtures :each (fn [t] (reset! sites {}) (reset! told []) (t)))

(deftest a-form-says-what-it-evaluated-to-in-the-order-it-did
  (instrumented-eval "(defn inst-f [m]
                        (let [x (inc (:a m))]
                          (when (pos? x) (assoc m :x x))))")
  (is (= [{:a 1 :x 2}
          [[:enter true]
           ["(:a m)" 1]
           ["(inc (:a m))" 2]
           ["(pos? x)" true]
           ["(assoc m :x x)" {:a 1 :x 2}]
           ["(when (pos? x) (assoc m :x x))" {:a 1 :x 2}]
           ["(let [x (inc (:a m))] (when (pos? x) (assoc m :x x)))" {:a 1 :x 2}]]]
         (told-of #(inst-f {:a 1})))))

(deftest what-a-threading-macro-rebuilt-is-the-step-written
  (instrumented-eval "(defn inst-t [m] (-> m (assoc :b 1) (update :b inc)))")
  (is (= [{:b 2}
          [[:enter true]
           ["(assoc m :b 1)" {:b 1}]
           ["(update (assoc m :b 1) :b inc)" {:b 2}]]]
         (told-of #(inst-t {})))))

(deftest a-fn-inside-says-it-is-not-the-outermost
  (instrumented-eval "(defn inst-m [xs] (mapv (fn [x] (* x 2)) xs))")
  (let [[v said] (told-of #(inst-m [1 2]))]
    (is (= [2 4] v))
    ;; the fn is a value of no interest, and not reported
    (is (= [[:enter true] [:enter false] ["(* x 2)" 2] [:enter false] ["(* x 2)" 4]
            ["(mapv (fn [x] (* x 2)) xs)" [2 4]]]
           said))))

(deftest primitives-stay-primitive
  (instrumented-eval "(defn inst-p ^long [^long n]
                        (loop [i 0 acc 0]
                          (if (< i n) (recur (inc i) (+ acc i)) acc)))")
  (let [[v said] (told-of #(inst-p 3))]
    (is (= 3 v))
    (is (= [["(< i n)" true] ["(inc i)" 1] ["(+ acc i)" 0]]
           (take 3 (rest said))))
    ;; the arithmetic of the loop is still on longs: no boxing warning, and the
    ;; method still takes and returns a long
    (is (some #(= Long/TYPE (.getReturnType ^java.lang.reflect.Method %))
              (.getMethods (class inst-p))))))

(deftest try-catch-and-finally
  (instrumented-eval "(defn inst-c [s]
                        (try (Long/parseLong s)
                             (catch Exception e (str \"bad \" (.getMessage e)))
                             (finally (count s))))")
  (is (= 12 (inst-c "12")))
  (let [[v said] (told-of #(inst-c "x"))]
    (is (= "bad For input string: \"x\"" v))
    (is (= [[:enter true]
            ["(.getMessage e)" "For input string: \"x\""]
            ["(str \"bad \" (.getMessage e))" v]
            ["(count s)" 1]]
           (butlast said)))))

(deftest what-has-no-value-to-report-is-left-alone
  (instrumented-eval "(defn inst-r [n] (if (pos? n) (recur (dec n)) (throw (ex-info \"done\" {}))))")
  (let [said (second (told-of #(try (inst-r 1) (catch Exception _ :thrown))))]
    ;; the exception is a value, the throw is not
    (is (= [:enter "(pos? n)" "(dec n)" :enter "(pos? n)" "(ex-info \"done\" {})"]
           (map first said))))
  (testing "nor what set! assigns to, which has to stay a field"
    (instrumented-eval "(deftype InstBox [^:unsynchronized-mutable v]
                          clojure.lang.IDeref (deref [_] v)
                          clojure.lang.IFn (invoke [this x] (set! v x) this))")
    (let [box (binding [*ns* (the-ns 'clojure.test-clojure.instrument)]
                (eval '(InstBox. 1)))]
      (is (= 5 @(box 5))))))

(deftest a-form-evaluated-at-the-top-is-entered
  (let [[v said] (told-of #(instrumented-eval "(let [a (atom 0)] (swap! a inc) @a)"))]
    (is (= 1 v))
    (is (= [:enter true] (first said)))
    (is (= ["(swap! a inc)" 1] (nth said 2)))))

(deftest a-site-has-the-span-it-was-written-with
  (instrumented-eval "(defn inst-s [x]\n  (inc x))")
  (is (= {:kind :value :line 2 :column 3 :end-line 2 :end-column 10}
         (select-keys (some #(when (= "(inc x)" (:text %)) %) (vals @sites))
                      [:kind :line :column :end-line :end-column]))))

(deftest without-instrument-nothing-is-said
  (binding [*ns* (the-ns 'clojure.test-clojure.instrument)]
    (eval (read-with-positions "(defn inst-n [x] (inc x))")))
  (is (= [2 []] (told-of #(inst-n 1)))))
