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

(declare inst-f inst-t inst-m inst-p inst-c inst-r inst-s inst-n
         inst-a inst-q inst-k inst-kp inst-l inst-lc inst-lu inst-ld inst-w inst-wf
         inst-d inst-df inst-b inst-h inst-x1 inst-x2 inst-x3 inst-x4 inst-x5 inst-x6 inst-x7)

(def ^:private sites (atom {}))
(def ^:private told (atom []))

(defn hook
  "What instrumented code calls, recording what it says."
  ([id] (swap! told conj [:enter (get-in @sites [id :outermost])]))
  ([id v] (swap! told conj [(get-in @sites [id :text]) v])))

(defn enter
  "What instrumented code calls on entering a fn, when there is an :enter."
  [id args]
  (swap! told conj [:enter (get-in @sites [id :outermost]) args]))

(def ^:private calls (atom 0))

(defn enter-call
  "What instrumented code calls on entering a fn, when there is an :exit too:
  the call it answers is the one it is told is over."
  [id args]
  (let [n (swap! calls inc)]
    (swap! told conj [:enter n])
    n))

(defn exit
  "What instrumented code calls once a call is over, when there is an :exit."
  [n]
  (swap! told conj [:exit n]))

;; What the hook was told by number - the very objects
(def ^:private ids (atom []))

(defn id-hook
  "A hook keeping the numbers it is told, as they are."
  ([id] (swap! ids conj id))
  ([id v] (swap! ids conj id)))

(declare switching)

(defn- switched [id & _] (swap! told conj [:switched id]))

(defn- switching-first
  "A hook that, told anything, has the Var it is the function of hold another."
  [id & _]
  (swap! told conj [:first id])
  (alter-var-root #'switching (constantly switched)))

(def switching switching-first)

(defn- site [{:keys [form] :as s}]
  (let [id (count @sites)]
    (swap! sites assoc id (assoc (dissoc s :form) :text (pr-str form)))
    id))

(defn- read-with-positions [s]
  (with-bindings {Compiler/RECORD_POSITIONS true}
    (read (LineNumberingPushbackReader. (java.io.StringReader. s)))))

(defn- instrumented-eval
  "Evaluate the code S, compiled to be stepped through - telling `enter' the
  args of the fns it enters, WITH-ARGS, and the hook what its LOCALS are
  bound to."
  [s & {:keys [with-args locals with-exit] the-hook :hook :or {the-hook #'hook}}]
  (let [form (read-with-positions s)]
    (with-bindings {Compiler/INSTRUMENT (cond-> {:site site :hook the-hook}
                                          with-args (assoc :enter #'enter)
                                          locals (assoc :locals true)
                                          with-exit (assoc :enter #'enter-call :exit #'exit))}
      (binding [*ns* (the-ns 'clojure.test-clojure.instrument)]
        (eval form)))))

(defn- told-of
  "What running F told the hook, with what F returned."
  [f]
  (reset! told [])
  (let [v (f)]
    [v @told]))

(use-fixtures :each (fn [t] (reset! sites {}) (reset! told []) (reset! calls 0) (t)))

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
    ;; and a recur to the top of the fn is not another entry
    (is (= [:enter "(pos? n)" "(dec n)" "(pos? n)" "(ex-info \"done\" {})"]
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

(deftest a-fn-entered-says-what-it-was-called-with
  (instrumented-eval "(defn inst-a [a {:keys [b]} & more] (+ a b (count more)))"
                     :with-args true)
  (let [[v said] (told-of #(inst-a 1 {:b 2} 3 4))]
    (is (= 5 v))
    (is (= [:enter true [1 {:b 2} '(3 4)]] (first said))))
  (testing "and the site says the params it was written with"
    (let [params (some #(when (= :enter (:kind %)) (:params %)) (vals @sites))]
      (is (= 4 (count params)))
      (is (= '[a & more] [(first params) (nth params 2) (nth params 3)])))))

(deftest a-primitive-arg-is-said-boxed
  (instrumented-eval "(defn inst-q ^double [^long n ^double d] (* n d))" :with-args true)
  (let [[v said] (told-of #(inst-q 3 1.5))]
    (is (= 4.5 v))
    (is (= [:enter true [3 1.5]] (first said))))
  (is (some #(= Double/TYPE (.getReturnType ^java.lang.reflect.Method %))
            (.getMethods (class inst-q)))))

(deftest a-recur-to-the-top-is-the-same-call
  (instrumented-eval "(defn inst-k [n] (if (pos? n) (recur (dec n)) n))" :with-args true)
  (is (= [[2]]
         (keep #(when (= :enter (first %)) (nth % 2)) (second (told-of #(inst-k 2))))))
  (testing "of a fn taking primitives"
    (instrumented-eval "(defn inst-kp ^long [^long n] (if (pos? n) (recur (dec n)) n))"
                       :with-args true)
    (is (= [[2]]
           (keep #(when (= :enter (first %)) (nth % 2)) (second (told-of #(inst-kp 2))))))))

(deftest an-arg-is-said-before-it-is-cleared
  (instrumented-eval "(defn inst-l [xs] (count xs))" :with-args true)
  (is (= [:enter true [[1 2]]] (first (second (told-of #(inst-l [1 2])))))))

(deftest a-form-evaluated-at-the-top-is-entered-with-no-args
  (is (= [:enter true []]
         (first (second (told-of #(instrumented-eval "(inc 1)" :with-args true)))))))

(deftest a-local-says-what-it-is-bound-to
  (instrumented-eval "(defn inst-lc [m xs]
                        (let [{:keys [a]} m
                              n (count xs)]
                          (doseq [x xs] (inc x))
                          (loop [i 0 acc []]
                            (if (< i 2) (recur (inc i) (conj acc i)) acc))
                          (dotimes [j 2] j)
                          (+ a n)))"
                     :locals true)
  (let [[v said] (told-of #(inst-lc {:a 1} [10 20]))
        locals (filter (fn [[text]] (contains? #{"a" "n" "x" "i" "acc" "j"} text)) said)]
    (is (= 3 v))
    (testing "a let's once, a destructured name too, and a loop's at the top of each time round, the last one too"
      (is (= [["a" 1] ["n" 2] ["x" 10] ["x" 20]
              ["i" 0] ["acc" []] ["i" 1] ["acc" [0]] ["i" 2] ["acc" [0 1]]
              ["j" 0] ["j" 1] ["j" 2]]
             locals)))
    (testing "a local site is the name, with its span"
      (is (every? #(and (= :local (:kind %)) (:line %) (:end-column %))
                  (filter #(#{"a" "n" "x" "i" "acc" "j"} (:text %)) (vals @sites)))))
    (testing "and nothing a macro named is one"
      (is (every? #(#{"a" "n" "x" "i" "acc" "j"} (:text %))
                  (filter #(= :local (:kind %)) (vals @sites)))))))

(deftest a-local-is-said-whatever-it-is
  (instrumented-eval "(defn inst-lu ^long [^long k]
                        (let [p (* k 2)
                              d (double k)
                              unused (inc k)]
                          (loop [q 0.5] (if (< q 1.0) (recur (+ q 0.5)) (+ p (long q))))))"
                     :locals true)
  (let [[v said] (told-of #(inst-lu 3))]
    (is (= 7 v))
    (is (= [["p" 6] ["d" 3.0] ["unused" 4] ["q" 0.5] ["q" 1.0]]
           (filter (fn [[text]] (contains? #{"p" "d" "unused" "q"} text)) said)))))

(defn- load-with-positions
  "Load the code S, read with positions on - as a file a form requires."
  [s]
  (with-bindings {Compiler/RECORD_POSITIONS true}
    (load-string s)))

(deftest a-file-loaded-is-not-the-form-that-loads-it
  (instrumented-eval "(load-with-positions \"(defn inst-ld [x] (inc x))\")")
  (is (= [2 []] (told-of #(inst-ld 1))))
  ;; the sites of the form that loads it only
  (is (every? #(re-find #"^\(\[\] \(load-with-positions|^\(load-with-positions" (:text %))
              (vals @sites))))

(deftest the-fn-a-try-as-a-value-is-wrapped-in-is-not-entered
  (instrumented-eval "(defn inst-w [n] (let [v (try (inc n) (catch Exception e 2))] v))")
  (is (= [2 [[:enter true]
             ["(inc n)" 2]
             ["(try (inc n) (catch Exception e 2))" 2]
             ["(let [v (try (inc n) (catch Exception e 2))] v)" 2]]]
         (told-of #(inst-w 1))))
  (is (= 1 (count (filter #(= :enter (:kind %)) (vals @sites)))))
  (testing "and a fn inside it is still inside the fn around it"
    (instrumented-eval "(defn inst-wf [] (let [f (try (fn [x] x))] (f 1)))")
    (is (= [[:enter true] [:enter false]]
           (filter #(= :enter (first %)) (second (told-of inst-wf))))))
  (testing "nor is it a definition's call"
    (let [[_ said] (told-of #(instrumented-eval "(def inst-d (try (inc 1) (catch Exception e 0)))"))]
      (is (= 2 inst-d))
      (is (= [["(inc 1)" 2] ["(try (inc 1) (catch Exception e 0))" 2]] said)))
    (testing "whose fn, there, is the outermost"
      (instrumented-eval "(def inst-df (loop [] (fn [x] (inc x))))")
      (is (= [2 [[:enter true] ["(inc x)" 2]]] (told-of #(inst-df 1)))))))

(defn- calls-told
  "What running F told of the calls it entered and exited, with what F
  returned - or what it threw."
  [f]
  (reset! told [])
  (let [v (try (f) (catch Exception e (ex-message e)))]
    [v (filterv #(#{:enter :exit} (first %)) @told)]))

(deftest a-call-says-it-is-over
  (instrumented-eval "(defn inst-x1 [x] x)" :with-exit true)
  (is (= [1 [[:enter 1] [:exit 1]]] (calls-told #(inst-x1 1))) "with no form to have a value")
  (testing "by a throw too"
    (instrumented-eval "(defn inst-x2 [x] (inc (throw (ex-info \"no\" {}))))" :with-exit true)
    (is (= ["no" [[:enter 2] [:exit 2]]] (calls-told #(inst-x2 1)))))
  (testing "once, a recur to the top being the same call"
    (instrumented-eval "(defn inst-x3 [n] (if (pos? n) (recur (dec n)) :done))" :with-exit true)
    (is (= [:done [[:enter 3] [:exit 3]]] (calls-told #(inst-x3 3)))))
  (testing "after what a try inside it caught"
    (instrumented-eval "(defn inst-x4 [] (try (inst-x2 1) (catch Exception _ :caught)))" :with-exit true)
    (is (= [:caught [[:enter 4] [:enter 5] [:exit 5] [:exit 4]]] (calls-told inst-x4)))
    (is (= "(try (inst-x2 1) (catch Exception _ :caught))" (first (last (butlast @told))))
        "its value before the call is over"))
  (testing "taking and returning primitives"
    (instrumented-eval "(defn inst-x5 ^long [^long x] (inc x))" :with-exit true)
    (is (= [2 [[:enter 6] [:exit 6]]] (calls-told #(inst-x5 1)))))
  (testing "before the fn it made is called"
    (instrumented-eval "(defn inst-x6 [g] (fn [x] (g x)))" :with-exit true)
    (let [[f said] (calls-told #(inst-x6 inc))]
      (is (= [[:enter 7] [:exit 7]] said))
      (is (= [2 [[:enter 8] [:exit 8]]] (calls-told #(f 1))))))
  (testing "evaluated at the top"
    (is (= [3 [[:enter 9] [:exit 9]]]
           (calls-told #(instrumented-eval "(let [a 1] (+ a 2))" :with-exit true)))))
  (testing "a definition's own"
    (instrumented-eval "(defn inst-x7 ([] (inst-x7 1)) ([x] (* 2 x)))" :with-exit true)
    (is (= [2 [[:enter 10] [:enter 11] [:exit 11] [:exit 10]]] (calls-told inst-x7)))))

(deftest a-site-number-is-boxed-once
  ;; past the numbers Long caches
  (reset! sites (zipmap (range 200) (repeat {})))
  (reset! ids [])
  (instrumented-eval "(defn inst-b [x] (inc x))" :hook #'id-hook)
  (inst-b 1)
  (inst-b 2)
  (let [[a b :as all] (partition 2 @ids)]
    (is (= 2 (count all)))
    (is (every? #(> % 127) (apply concat all)))
    (is (every? true? (map identical? a b)))))

(deftest the-hook-is-read-once-a-call
  (alter-var-root #'switching (constantly switching-first))
  (instrumented-eval "(defn inst-h [x] (inc (inc x)))" :hook #'switching)
  (let [[v said] (told-of #(inst-h 1))]
    (is (= 3 v))
    (testing "the function it was when the call started, to its end"
      (is (= [:first :first :first] (map first said)))))
  (testing "and the one it is when the next starts"
    (is (= [:switched :switched :switched] (map first (second (told-of #(inst-h 1))))))))
