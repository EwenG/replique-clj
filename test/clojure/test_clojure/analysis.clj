;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns clojure.test-clojure.analysis
  "Tests for `clojure.analysis`: the model the compiler's analysis sink fills, the
  query indexes derived from it, and the staleness / reload machinery on top.

  Everything here goes through the real compiler loading real files. The sink
  records what the compiler compiles and nothing else, so there is no way to
  exercise any of it from a model value written by hand - a test that built one
  would be testing its own idea of the shape rather than the thing that produces
  it. So each test writes the files it needs into a temporary directory that is on
  the classpath for the length of this namespace, loads them, and asks the queries.

  Two pieces of global state are touched and put back: the model (one atom, reset
  before and after every test) and the thread's context class loader (see
  `classpath-root!`). Namespaces a test's files define are removed afterwards, as
  is everything it wrote."
  (:use clojure.test)
  (:require [clojure.analysis :as an]
            [clojure.java.io :as io]
            [clojure.string :as str]))

;; --- the classpath root the probe files live in ----------------------------

(def ^:private root
  "The temporary directory tests write their files into, as a `File`."
  (atom nil))

(def ^:private loaders
  "The class loaders `root` was added to - the ones a test adds more to when it puts
  something else on the classpath (a jar). Each searches its own URLs in the order
  they were added, so anything added later is searched after `root`, which is what
  lets a test write a file that shadows a jar entry."
  (atom []))

(defn- on-the-classpath!
  "Put `url` on the classpath, wherever `root` was put."
  [^java.net.URL url]
  (doseq [^clojure.lang.DynamicClassLoader cl @loaders] (.addURL cl url))
  nil)

(defn- classpath-root!
  "Create the directory the probe files live in and put it on the classpath.

  Two loaders are told about it, because which one answers depends on how the
  tests are being run. `io/resource` and `load` go through `RT.baseLoader`, which
  is the loader bound by the innermost `eval` - and a whole `run-tests` call is one
  `eval`, so adding the directory there is what makes the files visible to a suite
  run, for that run only. Evaluated a test at a time at a REPL, each test is its
  own `eval` with its own such loader and they share only the thread's context
  loader, the root every one of them is built on top of - so a durable loader
  installed there is what makes a test work when run by hand. Neither alone covers
  both. Returns [dir loaders]."
  []
  (let [dir     (.toFile (java.nio.file.Files/createTempDirectory
                          "clojure-analysis-test"
                          (make-array java.nio.file.attribute.FileAttribute 0)))
        url     (.toURL (.toURI dir))
        thread  (Thread/currentThread)
        durable (clojure.lang.DynamicClassLoader. (.getContextClassLoader thread))
        base    (clojure.lang.RT/baseLoader)]
    (.addURL durable url)
    (.setContextClassLoader thread durable)
    (when (instance? clojure.lang.DynamicClassLoader base)
      (.addURL ^clojure.lang.DynamicClassLoader base url))
    [dir (cond-> [durable]
           (instance? clojure.lang.DynamicClassLoader base) (conj base))]))

(defn- deleted-tree!
  "Delete `f`, and everything under it if it is a directory."
  [^java.io.File f]
  (when (.isDirectory f)
    (doseq [c (.listFiles f)] (deleted-tree! c)))
  (.delete f)
  nil)

(defn- with-a-classpath-root
  "Fixture: a temporary directory on the classpath for the whole namespace."
  [f]
  (let [was (.getContextClassLoader (Thread/currentThread))
        [dir cls] (classpath-root!)]
    (reset! root dir)
    (reset! loaders cls)
    (try
      (f)
      (finally
        (an/reset-model!)
        (.setContextClassLoader (Thread/currentThread) was)
        (deleted-tree! dir)
        (reset! root nil)
        (reset! loaders [])))))

(def ^:private written
  "The source paths the running test has written. The fixture uses them to tell a
  namespace one of its own files defined from one a file of its happened to load:
  a probe namespace is named after the directory its file was written into, so its
  first segment is the first segment of a written path. Removing a real library
  because a probe was the first thing to require it would be a poor trade for
  tidiness."
  (atom #{}))

(def trace
  "The files loaded so far, in order, as recorded by `loaded!`. Public because the
  probe files call into it."
  (atom []))

(defn loaded!
  "Note that the file holding this call has just been loaded. A probe file that
  cares about load order calls this at its top level; the reload machinery is
  mostly about the order things are loaded in and how often, and that is not
  visible in the model afterwards - only in what actually ran."
  [name]
  (swap! trace conj name)
  nil)

(defn- with-a-clean-slate
  "Fixture: an empty model, an empty load trace, and afterwards no trace of the
  test left anywhere - its files deleted, and every namespace one of its own files
  defined (see `written`) removed from the registry, and from the loaded-libs set
  so that a later `require` of a name one of them happened to use would really load
  it rather than find the dead entry and do nothing."
  [f]
  (let [before (set (map ns-name (all-ns)))]
    (an/reset-model!)
    (reset! trace [])
    (reset! written #{})
    (try
      (f)
      (finally
        (let [dirs  (set (map #(first (str/split % #"/")) @written))
              mine? #(contains? dirs (first (str/split (str %) #"\.")))]
          (doseq [n (filter mine? (remove before (map ns-name (all-ns))))]
            (remove-ns n)
            (dosync (alter @#'clojure.core/*loaded-libs* disj n))))
        (an/reset-model!)
        (doseq [c (.listFiles ^java.io.File @root)] (deleted-tree! c))))))

(use-fixtures :once with-a-classpath-root)
(use-fixtures :each with-a-clean-slate)

;; --- writing, reading and loading probe files ------------------------------

(def ^:private clock
  "Source mtimes are stamped, not taken from the clock: a test writes a file and
  asks whether it is changed in the same millisecond, which on a filesystem whose
  timestamps are that coarse would answer no. Each write gets a distinct time,
  well into the future, so `changed-files` sees an edit for what it is."
  (atom 0))

(defn- written!
  "Write `lines` as the classpath resource `source` (e.g. \"probe/a.clj\") and
  return `source` - the same path the compiler records, so it reads as the thing
  the queries are asked about."
  [source & lines]
  (let [f (io/file @root source)]
    (.mkdirs (.getParentFile f))
    (spit f (str (str/join "\n" lines) "\n"))
    (.setLastModified f (+ (System/currentTimeMillis) (* 10000 (long (swap! clock inc)))))
    (swap! written conj source)
    source))

(defn- deleted!
  "Delete the file behind `source`. Returns `source`."
  [source]
  (.delete (io/file @root source))
  source)

(defn- text-at
  "The source text `span` covers, read back off disk. A span is only right if it
  picks out the name it is about, and that is a fact about the file, so the test
  asks the file rather than another part of the model. Every span asked about here
  is a name, and a name is on one line; a span that is not says so rather than
  quietly handing back the wrong line's worth of text."
  [{:keys [source line column end-line end-column]}]
  (when-not (= line end-line)
    (throw (ex-info "text-at: span covers more than one line"
                    {:source source :line line :end-line end-line})))
  (-> (slurp (io/file @root source))
      (str/split-lines)
      (nth (dec line))
      (subs (dec column) (dec end-column))))

(defn- analysed!
  "Load `sources` cold, under the sink, in the order given. Returns nil."
  [& sources]
  (an/run-analysis #(doseq [s sources] (load (str "/" (str/replace s #"\.clj$" "")))))
  nil)

;; --- what the sink records -------------------------------------------------

(deftest what-a-loaded-file-records
  (let [source (written! "records/a.clj"
                         "(ns records.a)"
                         "(def answer 42)"
                         "(defmacro twice [x] (list 'do x x))"
                         "(defn ask [n]"
                         "  (twice (str n))"
                         "  (+ n answer))"
                         "(def tag ::tag)"
                         "(def buffer (StringBuilder.))")]
    (analysed! source)
    (testing "every top-level def, and only those"
      (is (= '#{records.a/answer records.a/twice records.a/ask records.a/tag records.a/buffer}
             (set (keys (:defs (an/snapshot)))))))
    (testing "a def's span picks out the name being defined"
      (is (= "answer" (text-at (an/definition 'records.a/answer))))
      (is (= 2 (:line (an/definition 'records.a/answer)))))
    (testing "a var used from the same file"
      (let [uses (an/find-usages 'records.a/answer)]
        (is (= 1 (count uses)))
        (is (= "answer" (text-at (first uses))))
        (is (= 6 (:line (first uses))))
        (is (= 'records.a (ns-name (:from-ns (first uses)))))
        (is (nil? (:macro (first uses))))))
    (testing "a macro call is marked as one"
      (let [uses (an/find-usages 'records.a/twice)]
        (is (= 1 (count uses)))
        (is (= "twice" (text-at (first uses))))
        (is (true? (:macro (first uses))))))
    (testing "an auto-resolved keyword is recorded fully qualified"
      (let [uses (an/find-keyword-usages (keyword "records.a" "tag"))]
        (is (= 1 (count uses)))
        (is (= "::tag" (text-at (first uses))))))
    (testing "a class is recorded by name, and found by name or by Class"
      (let [uses (an/find-class-usages StringBuilder)]
        (is (= 1 (count uses)))
        (is (= "StringBuilder" (text-at (first uses))))
        (is (= uses
               (an/find-class-usages 'java.lang.StringBuilder)
               (an/find-class-usages "java.lang.StringBuilder")))))
    (testing "a local binding, with its uses"
      (let [locals (vals (:locals (an/snapshot)))
            n      (first (filter #(= "n" (:name %)) locals))]
        (is (some? n))
        (is (= "n" (text-at n)))
        (is (= #{5 6} (set (map :line (:uses n)))))))
    (testing "which namespaces the file defines, and which forms belong to it"
      (is (= '#{records.a} (an/file-namespaces source)))
      (is (= 6 (count (an/file-forms source))))
      (is (= (an/file-forms source) (an/ns-forms 'records.a))))))

(deftest a-second-analysis-of-a-file-replaces-the-first
  (let [source (written! "again/a.clj"
                         "(ns again.a)"
                         "(def x 1)"
                         "(def y x)")]
    (analysed! source)
    (let [fids (an/file-forms source)]
      (an/load-file! source)
      (testing "the file's forms are replaced, not added to"
        (is (= 3 (count (an/file-forms source))))
        (is (empty? (filter fids (an/file-forms source)))))
      (testing "and its facts are recorded once, not twice"
        (is (= 1 (count (an/find-usages 'again.a/x))))))))

(deftest a-def-deleted-from-a-file-stops-being-defined
  (let [source (written! "deleted/a.clj"
                         "(ns deleted.a)"
                         "(def x 1)"
                         "(def y 2)")]
    (analysed! source)
    (is (some? (an/definition 'deleted.a/y)))
    (written! "deleted/a.clj"
              "(ns deleted.a)"
              "(def x 1)")
    (an/load-file! source)
    (testing "the var the deleted form defined has no definition left"
      (is (nil? (an/definition 'deleted.a/y))))
    (testing "and the one it still defines is untouched"
      (is (some? (an/definition 'deleted.a/x)))
      (is (= 2 (count (an/file-forms source)))))))

(deftest a-var-defined-twice-keeps-the-later-definition
  (let [source (written! "twice/a.clj"
                         "(ns twice.a)"
                         "(def x 1)"
                         "(def x 2)")]
    (analysed! source)
    (is (= 3 (:line (an/definition 'twice.a/x))))))

(deftest a-file-that-defines-two-namespaces-is-one-reload-unit
  (let [source (written! "twons/a.clj"
                         "(ns twons.a)"
                         "(def x 1)"
                         "(ns twons.b)"
                         "(def y 2)")]
    (analysed! source)
    (is (= '#{twons.a twons.b} (an/file-namespaces source)))
    (testing "reloading the file re-analyses both of its namespaces"
      (an/load-file! source)
      (is (= '#{twons.a twons.b} (an/file-namespaces source)))
      (is (some? (an/definition 'twons.a/x)))
      (is (some? (an/definition 'twons.b/y))))))

(deftest a-file-that-fails-to-compile-keeps-the-forms-it-had
  (let [source (written! "failing/a.clj"
                         "(ns failing.a)"
                         "(def keep-me 1)")]
    (analysed! source)
    (written! "failing/a.clj"
              "(ns failing.a)"
              "(def keep-me 1)"
              "(def broken (no-such-function))")
    (is (thrown? Exception (an/load-file! source)))
    (testing "the file that threw keeps every fact it had"
      (is (some? (an/definition 'failing.a/keep-me)))
      (is (= 2 (count (an/file-forms source))))
      (is (nil? (an/definition 'failing.a/broken))))
    (testing "and stays stale, so the next reload retries it"
      (is (contains? (an/changed-files) source)))))

(deftest a-file-loaded-on-the-way-to-a-failure-is-kept
  (let [good (written! "partial/good.clj"
                       "(ns partial.good)"
                       "(def x 1)")
        bad  (written! "partial/bad.clj"
                       "(ns partial.bad (:require [partial.good]))"
                       "(def y (no-such-function))")]
    (is (thrown? Exception (an/load-file! bad)))
    (testing "the file that loaded to completion is in the model"
      (is (some? (an/definition 'partial.good/x)))
      (is (seq (an/file-forms good))))
    (testing "the one that threw is not"
      (is (empty? (an/file-forms bad))))))

(deftest retracting-a-file-leaves-other-files-usages-of-its-vars
  (let [a (written! "retract/a.clj"
                    "(ns retract.a)"
                    "(def x 1)")
        b (written! "retract/b.clj"
                    "(ns retract.b (:require [retract.a]))"
                    "(def y retract.a/x)")]
    (analysed! a b)
    (is (some? (an/definition 'retract.a/x)))
    (is (= 1 (count (an/find-usages 'retract.a/x))))
    (an/retract-file! a)
    (testing "the retracted file's definitions are gone"
      (is (nil? (an/definition 'retract.a/x)))
      (is (empty? (an/file-forms a))))
    (testing "but another file's usages of them are not"
      (is (= 1 (count (an/find-usages 'retract.a/x))))
      (is (= b (:source (first (an/find-usages 'retract.a/x))))))))

(deftest a-query-never-answers-from-a-model-that-has-moved-on
  (let [source (written! "cache/a.clj"
                         "(ns cache.a)"
                         "(def x 1)")]
    (analysed! source)
    ;; Ask first, so the derived indexes are built and cached; the point of the
    ;; test is that the next answer comes from the new forms and not from that
    ;; cache, which is keyed on the identity of the forms map.
    (is (some? (an/definition 'cache.a/x)))
    (an/retract-file! source)
    (is (nil? (an/definition 'cache.a/x)))))

(deftest nothing-is-recorded-without-the-sink
  (let [source (written! "nosink/a.clj"
                         "(ns nosink.a)"
                         "(def x 1)")]
    (testing "a plain load records nothing - only an analysed one does"
      (load "/nosink/a")
      (is (empty? (:forms (an/snapshot))))
      (is (nil? (an/definition 'nosink.a/x))))
    (testing "and neither does an eval with no file around it, sink or no sink:
              there is no form to attribute a fact to, and one filed anyway could
              never be dropped again"
      (an/run-analysis #(eval '(+ 1 1)))
      (is (empty? (:forms (an/snapshot)))))
    (analysed! source)
    (is (some? (an/definition 'nosink.a/x)))))

(deftest load-file!-refuses-anything-that-is-not-a-source-path
  (let [source (written! "refuse/a.clj"
                         "(ns refuse.a)"
                         "(def x 1)")]
    (analysed! source)
    (testing "an absolute file path - what an editor has, and must translate"
      (is (thrown? clojure.lang.ExceptionInfo
                   (an/load-file! (.getPath (io/file @root source))))))
    (testing "a resource path with a leading slash - what `load` takes"
      (is (thrown? clojure.lang.ExceptionInfo (an/load-file! (str "/" source)))))
    (testing "a path nothing on the classpath answers to"
      (is (thrown? clojure.lang.ExceptionInfo (an/load-file! "refuse/gone.clj"))))
    (testing "something that is not a path at all"
      (is (thrown? clojure.lang.ExceptionInfo (an/load-file! 'refuse/a.clj))))
    (testing "and the model is untouched by any of them"
      (is (= 2 (count (an/file-forms source)))))))

;; --- what has changed on disk ----------------------------------------------

(deftest a-file-edited-after-it-was-loaded-is-changed
  (let [source (written! "edited/a.clj"
                         "(ns edited.a)"
                         "(def x 1)")]
    (analysed! source)
    (testing "a file just analysed is its own baseline"
      (is (empty? (an/changed-files))))
    (written! "edited/a.clj"
              "(ns edited.a)"
              "(def x 2)")
    (is (= #{source} (an/changed-files)))
    (testing "and reloading it re-baselines it"
      (an/load-file! source)
      (is (empty? (an/changed-files))))))

(deftest an-analysis-baselines-only-the-files-it-compiled
  (let [a (written! "onlymine/a.clj" "(ns onlymine.a)" "(def x 1)")
        b (written! "onlymine/b.clj" "(ns onlymine.b)" "(def y 1)")]
    (analysed! a b)
    (written! "onlymine/a.clj" "(ns onlymine.a)" "(def x 2)")
    (written! "onlymine/b.clj" "(ns onlymine.b)" "(def y 2)")
    (is (= #{a b} (an/changed-files)))
    (an/load-file! a)
    (testing "the file that was not reloaded keeps its pending edit"
      (is (= #{b} (an/changed-files))))
    (testing "and snapshot-mtimes! is how you clear them all at once"
      (an/snapshot-mtimes!)
      (is (empty? (an/changed-files))))))

(deftest a-file-that-is-gone-is-not-changed-and-one-that-comes-back-is
  (let [source (written! "vanishing/a.clj"
                         "(ns vanishing.a)"
                         "(def x 1)")]
    (analysed! source)
    (deleted! source)
    (testing "a file that no longer resolves is not flagged - reloading it could
              only fail"
      (is (empty? (an/changed-files))))
    (testing "but one that comes back is, however long it was away: whether
              nothing answers to a name is never settled"
      (written! "vanishing/a.clj"
                "(ns vanishing.a)"
                "(def x 7)")
      (is (= #{source} (an/changed-files)))
      (an/stale-reload!)
      (is (= 7 @(resolve 'vanishing.a/x)))
      (is (empty? (an/changed-files))))))

(deftest a-load-with-no-file-behind-it-asks-the-classpath-nothing
  ;; load-string, load-reader, and anything else that reaches the compiler with no
  ;; source path: the facts are recorded under a nil source, and asking the
  ;; classpath about a nil is not a question, so nothing here goes near it.
  (an/run-analysis #(load-string "(ns nofile.a) (def x 1)"))
  (is (contains? (:source->forms (an/snapshot)) nil))
  (is (some? (an/definition 'nofile.a/x)))
  (is (empty? (an/changed-files)))
  (is (empty? (an/stale-files)))
  ;; No file was written, so the fixture has no way to know this namespace was one
  ;; of ours.
  (remove-ns 'nofile.a))

(defn- jar-on-the-classpath!
  "Write a jar holding `entries` ({entry-path source-text}) and put it on the
  classpath behind `root`, which was added first and so answers first. A file
  written into `root` afterwards therefore shadows the jar's entry of the same
  name - the one way a source already resolved can come to resolve somewhere else,
  and what the whole non-files cache turns on."
  [name entries]
  (let [f (io/file @root (str name ".jar"))]
    (with-open [out (java.util.jar.JarOutputStream. (java.io.FileOutputStream. f))]
      (doseq [[entry text] entries]
        (.putNextEntry out (java.util.jar.JarEntry. ^String entry))
        (.write out (.getBytes ^String text "UTF-8"))
        (.closeEntry out)))
    (on-the-classpath! (.toURL (.toURI f)))
    f))

(deftest a-source-a-jar-answers-to-is-not-watched-until-the-classpath-is-read-again
  (jar-on-the-classpath! "library" {"jarred/library.clj" "(ns jarred.library)\n(def value 2)\n"})
  (let [user (written! "jarred/user.clj"
                       "(ns jarred.user (:require [jarred.library]))"
                       "(def got jarred.library/value)")]
    (analysed! user)
    (is (= 2 @(resolve 'jarred.user/got)))
    (testing "the jar's own file is analysed like any other"
      (is (contains? (:source->forms (an/snapshot)) "jarred/library.clj"))
      (is (some? (an/definition 'jarred.library/value))))
    (testing "and is not changed - this is also what fills the skip set"
      (is (empty? (an/changed-files))))
    (written! "jarred/library.clj"
              "(ns jarred.library)"
              "(def value 10)")
    (testing "a file written over it, earlier on the classpath, is not seen"
      (is (empty? (an/changed-files))))
    (testing "until the classpath is read again"
      (an/classpath-changed!)
      (is (= #{"jarred/library.clj"} (an/changed-files))))
    (testing "and then it reloads from the file that now answers"
      (is (= ["jarred/library.clj"] (an/stale-reload!)))
      (is (= 10 @(resolve 'jarred.library/value)))
      (is (empty? (an/changed-files))))))

;; --- the macro graph, and what an edit makes stale --------------------------

(defn- macro-graph
  "The forward file macro graph for the current model.

  Reaching into a private is deliberate here. The graph is the thing these tests
  are about, nothing public exposes it, and the one public thing it shapes - the
  order `stale-reload!` loads files in - is only wrong for some graphs and some
  hash orders, so a test that went through the front door would pass by luck as
  often as by correctness."
  []
  (#'an/file-macro-graph @@#'an/model))

(deftest an-edit-makes-the-files-that-expand-its-macros-stale-too
  (let [m (written! "cascade/m.clj"
                    "(ns cascade.m)"
                    "(defmacro plus [x] (list '+ x 1))")
        a (written! "cascade/a.clj"
                    "(ns cascade.a (:require [cascade.m]))"
                    "(defmacro twice [x] (list '* 2 x))"
                    "(def am (cascade.m/plus 1))")
        c (written! "cascade/c.clj"
                    "(ns cascade.c (:require [cascade.a]))"
                    "(def cm (cascade.a/twice 3))")
        r (written! "cascade/r.clj"
                    "(ns cascade.r (:require [cascade.a]))"
                    "(def rv cascade.a/am)")]
    (analysed! m a c r)
    (testing "the graph has an edge per file that expanded another file's macro"
      (is (= {a #{m} c #{a}} (macro-graph))))
    (testing "and the macros a namespace expanded are visible as such"
      (is (contains? (an/macro-deps 'cascade.a) 'cascade.m/plus))
      (is (contains? (an/macro-deps) 'cascade.c)))
    (written! "cascade/m.clj"
              "(ns cascade.m)"
              "(defmacro plus [x] (list '+ x 100))")
    (testing "editing the macro file makes it, and its macro dependents, stale"
      (is (= #{m} (an/changed-files)))
      (is (= #{m a c} (an/stale-files))))
    (testing "the file that only calls a function of a stale file is not stale -
              a var re-resolves at runtime and needs no recompile"
      (is (not (contains? (an/stale-files) r))))
    (testing "and the same question can be asked about an edit that has not
              happened yet"
      (is (= #{m a c} (an/stale-files #{m})))
      (is (= #{a c} (an/stale-files #{a}))))))

(deftest a-file-that-expands-its-own-macro-is-not-its-own-dependent
  (let [m (written! "selfedge/m.clj"
                    "(ns selfedge.m)"
                    "(defmacro plus [x] (list '+ x 1))"
                    "(def mine (plus 1))")
        a (written! "selfedge/a.clj"
                    "(ns selfedge.a (:require [selfedge.m]))"
                    "(def theirs (selfedge.m/plus 1))")]
    (analysed! m a)
    ;; A self-edge would leave topo-order with no file it could place first, so it
    ;; would give up and load them in whatever order the set came out in.
    (is (= {a #{m}} (macro-graph)))))

(deftest a-macro-dependency-orders-a-reload
  (testing "a file's macro dependencies are loaded before it"
    (is (= ["m" "a" "c"] (#'an/topo-order ["c" "a" "m"] {"a" #{"m"} "c" #{"a"}}))))
  (testing "a dependency that is not being reloaded is already current, so it
            places no constraint"
    (is (= ["a"] (#'an/topo-order ["a"] {"a" #{"elsewhere"}}))))
  (testing "a cycle is broken rather than hung on"
    (let [order (#'an/topo-order ["a" "b"] {"a" #{"b"} "b" #{"a"}})]
      (is (= #{"a" "b"} (set order)))
      (is (= 2 (count order)))))
  (testing "and an order can say whether it already respects a graph"
    (is (true? (#'an/topo-respected? ["m" "a"] {"a" #{"m"}})))
    (is (false? (#'an/topo-respected? ["a" "m"] {"a" #{"m"}})))
    (is (true? (#'an/topo-respected? ["a"] {"a" #{"elsewhere"}})))))

(deftest a-stale-reload-loads-macro-files-before-the-files-that-expand-them
  (let [m (written! "order/m.clj"
                    "(ns order.m)"
                    "(clojure.test-clojure.analysis/loaded! 'm)"
                    "(defmacro value [] 1)")
        a (written! "order/a.clj"
                    "(ns order.a (:require [order.m]))"
                    "(clojure.test-clojure.analysis/loaded! 'a)"
                    "(def v (order.m/value))")]
    (analysed! m a)
    (written! "order/m.clj"
              "(ns order.m)"
              "(clojure.test-clojure.analysis/loaded! 'm)"
              "(defmacro value [] 42)")
    (written! "order/a.clj"
              "(ns order.a (:require [order.m]))"
              "(clojure.test-clojure.analysis/loaded! 'a)"
              "(def v (order.m/value))")
    (reset! trace [])
    (testing "the order it reports is the order it used"
      (is (= [m a] (an/stale-reload!)))
      (is (= '[m a] @trace)))
    (testing "one pass, because the first order already held"
      (is (= 2 (count @trace))))
    (testing "and the dependent file was compiled against the new macro"
      (is (= 42 @(resolve 'order.a/v))))))

(deftest a-macro-dependency-an-edit-adds-takes-a-second-pass
  ;; The first-pass order comes from the graph as it was BEFORE the edit, which
  ;; cannot know an edge the edit itself adds. Here the edit turns the dependency
  ;; round: y expanded x's macro, and now x expands y's. The old graph says load x
  ;; first, so pass 1 compiles x against the ymac that is still in memory - the old
  ;; one. Only the second pass, ordered by the graph pass 1 completed, gets it right.
  (let [x (written! "pass/x.clj"
                    "(ns pass.x)"
                    "(clojure.test-clojure.analysis/loaded! 'x)"
                    "(defmacro xmac [] :x-old)")
        y (written! "pass/y.clj"
                    "(ns pass.y (:require [pass.x]))"
                    "(clojure.test-clojure.analysis/loaded! 'y)"
                    "(defmacro ymac [] :y-old)"
                    "(def from-x (pass.x/xmac))")]
    (analysed! y)
    (is (= {y #{x}} (macro-graph)))
    (written! "pass/x.clj"
              "(ns pass.x (:require [pass.y]))"
              "(clojure.test-clojure.analysis/loaded! 'x)"
              "(defmacro xmac [] :x-new)"
              "(def from-y (pass.y/ymac))")
    (written! "pass/y.clj"
              "(ns pass.y)"
              "(clojure.test-clojure.analysis/loaded! 'y)"
              "(defmacro ymac [] :y-new)")
    (reset! trace [])
    (let [order (an/stale-reload!)]
      (testing "the order it reports is the corrected one"
        (is (= [y x] order)))
      (testing "and both passes really ran, the second in the new order"
        (is (= '[x y y x] @trace)))
      (testing "so the file that expands the new macro has the new expansion"
        (is (= :y-new @(resolve 'pass.x/from-y))))
      (testing "and nothing is left stale"
        (is (empty? (an/changed-files)))))))

(deftest a-stale-reload-stops-at-the-first-file-that-will-not-compile
  (let [m (written! "failfast/m.clj"
                    "(ns failfast.m)"
                    "(clojure.test-clojure.analysis/loaded! 'm)"
                    "(defmacro mv [] 1)")
        a (written! "failfast/a.clj"
                    "(ns failfast.a (:require [failfast.m]))"
                    "(clojure.test-clojure.analysis/loaded! 'a)"
                    "(defmacro av [] 2)"
                    "(def x (failfast.m/mv))")
        b (written! "failfast/b.clj"
                    "(ns failfast.b (:require [failfast.a]))"
                    "(clojure.test-clojure.analysis/loaded! 'b)"
                    "(def y (failfast.a/av))")]
    (analysed! m a b)
    (is (= {a #{m} b #{a}} (macro-graph)))
    (written! "failfast/m.clj"
              "(ns failfast.m)"
              "(clojure.test-clojure.analysis/loaded! 'm)"
              "(defmacro mv [] 10)")
    (written! "failfast/a.clj"
              "(ns failfast.a (:require [failfast.m]))"
              "(clojure.test-clojure.analysis/loaded! 'a)"
              "(defmacro av [] 2)"
              "(def x (failfast.m/mv))"
              "(def boom (no-such-function))")
    (written! "failfast/b.clj"
              "(ns failfast.b (:require [failfast.a]))"
              "(clojure.test-clojure.analysis/loaded! 'b)"
              "(def y (failfast.a/av))")
    (reset! trace [])
    (is (thrown? Exception (an/stale-reload!)))
    (testing "it stopped where it threw - nothing after that was loaded"
      (is (= '[m a] @trace)))
    (testing "the model keeps the file that threw as it was: its frame never
              committed, so the forms the failed load did compile are not in it"
      ;; The running namespace is another matter, and is half the new file - `load`
      ;; ran every form before the one that threw, and `def` interns its var before
      ;; it compiles the init. That is what the compiler left behind and the model
      ;; does not pretend otherwise; it just does not RECORD a file it never
      ;; finished reading.
      (is (= 4 (count (an/file-forms a))))
      (is (nil? (an/definition 'failfast.a/boom))))
    (testing "and no staleness was lost: the failed file and the one never
              reached are still waiting, the one that succeeded is not"
      (is (= #{a b} (an/changed-files))))))

;; --- pruning vars whose def is gone ----------------------------------------

(defn- model
  "The current model value. `file-def-var-snapshot` takes the model it is to read
  rather than reading the atom itself, and the atom is private, so a caller from
  outside has to reach in for it like this."
  []
  @@#'an/model)

(deftest a-var-whose-def-vanished-is-unmapped
  (let [a (written! "prune/a.clj"
                    "(ns prune.a)"
                    "(def stays 1)"
                    "(def gone 2)")]
    (analysed! a)
    (is (= '#{prune.a/stays prune.a/gone} (set (keys (an/file-def-var-snapshot (model) a)))))
    (written! "prune/a.clj"
              "(ns prune.a)"
              "(def stays 1)")
    (an/stale-reload! :prune true)
    (testing "reloading cannot remove a var whose def is gone, so prune does"
      (is (nil? (ns-resolve 'prune.a 'gone))))
    (testing "and the var the file still defines is left alone"
      (is (some? (ns-resolve 'prune.a 'stays))))))

(deftest a-var-that-moved-to-another-file-is-not-pruned
  (let [a (written! "moved/a.clj"
                    "(ns moved.shared)"
                    "(def stays 1)"
                    "(def moves 2)")
        b (written! "moved/b.clj"
                    "(ns moved.shared)"
                    "(def other 3)")]
    (analysed! a b)
    (written! "moved/a.clj"
              "(ns moved.shared)"
              "(def stays 1)")
    (written! "moved/b.clj"
              "(ns moved.shared)"
              "(def other 3)"
              "(def moves 2)")
    ;; Reload the file it moved TO first, which is the case prune is documented to
    ;; survive. By the time the file it moved FROM is reloaded, the def the model
    ;; records for the var is the one in the new file - the later form wins - so the
    ;; var is no longer even among the old file's defs, let alone a candidate.
    (let [prior-b (an/file-def-var-snapshot (model) b)]
      (an/load-file! b)
      (an/prune-file! b prior-b))
    (let [prior-a (an/file-def-var-snapshot (model) a)]
      (is (not (contains? prior-a 'moved.shared/moves)))
      (an/load-file! a)
      (is (= [] (an/prune-file! a prior-a))))
    (is (= 2 @(ns-resolve 'moved.shared 'moves)))
    (is (= 1 @(ns-resolve 'moved.shared 'stays)))))

(deftest a-var-re-created-under-a-fresh-identity-is-left-alone
  (let [a (written! "fresh/a.clj"
                    "(ns fresh.a)"
                    "(def gone 1)")]
    (analysed! a)
    (let [prior (an/file-def-var-snapshot (model) a)]
      (written! "fresh/a.clj"
                "(ns fresh.a)")
      (an/load-file! a)
      ;; Vars are keyed by name, so the model cannot tell these apart; the Var
      ;; object can. Something re-made this one after the def was deleted, and
      ;; destroying it would destroy something nobody asked to be destroyed.
      (ns-unmap 'fresh.a 'gone)
      (intern 'fresh.a 'gone 99)
      (is (= [] (an/prune-file! a prior)))
      (is (= 99 @(ns-resolve 'fresh.a 'gone))))))

(deftest a-var-that-was-never-a-def-is-not-pruned
  (let [a (written! "interned/a.clj"
                    "(ns interned.a)"
                    "(def real 1)"
                    "(intern *ns* 'made 2)")]
    (analysed! a)
    (written! "interned/a.clj"
              "(ns interned.a)")
    (an/stale-reload! :prune true)
    (testing "the def that vanished is pruned"
      (is (nil? (ns-resolve 'interned.a 'real))))
    (testing "but a var no def form ever made is not a candidate - which is what
              keeps a protocol's method vars alive"
      (is (some? (ns-resolve 'interned.a 'made))))))

(deftest pruning-a-var-that-is-still-referenced-warns-and-prunes-anyway
  (let [a (written! "warn/a.clj"
                    "(ns warn.a)"
                    "(def gone 1)")
        b (written! "warn/b.clj"
                    "(ns warn.b (:require [warn.a]))"
                    "(def uses warn.a/gone)")]
    (analysed! a b)
    (let [prior (an/file-def-var-snapshot (model) a)
          err   (java.io.StringWriter.)]
      (written! "warn/a.clj"
                "(ns warn.a)")
      (an/load-file! a)
      (is (= '[warn.a/gone] (binding [*err* err] (an/prune-file! a prior))))
      (testing "a reflective use could not have been seen, so it warns"
        (is (re-find #"warn\.a/gone" (str err)))
        (is (re-find #"warn\.b" (str err))))
      (testing "and prunes regardless"
        (is (nil? (ns-resolve 'warn.a 'gone)))))))

(deftest prune-file!-refuses-a-file-the-model-knows-nothing-about
  ;; Only valid right after a load of that file. On a file that was never
  ;; analysed every var in `prior` would look deleted, and prune would unmap
  ;; a whole namespace on the strength of having no idea about it.
  (is (thrown? clojure.lang.ExceptionInfo (an/prune-file! "never/analysed.clj" {}))))

;; --- the lints, which read live namespace state against the model ----------

(deftest a-local-nothing-refers-to-is-unused
  (let [a (written! "locals/a.clj"
                    "(ns locals.a)"
                    "(defn f [used unused] used)"
                    "(defn g [] (let [x 1 y 2] x))")]
    (analysed! a)
    (is (= #{"unused" "y"} (set (map :name (an/unused-locals)))))
    (is (= #{"unused" "y"} (set (map :name (an/unused-locals 'locals.a)))))
    (is (empty? (an/unused-locals 'locals.nothing)))
    (testing "and it is reported at its binding site"
      (let [y (first (filter #(= "y" (:name %)) (an/unused-locals)))]
        (is (= "y" (text-at y)))
        (is (= 3 (:line y)))))))

(deftest an-alias-a-refer-and-an-import-nothing-uses-are-unused
  (let [a (written! "lints/a.clj"
                    "(ns lints.a"
                    "  (:require [clojure.string :as str :refer [blank? trim]]"
                    "            [clojure.walk :as walk])"
                    "  (:import (java.util ArrayList Date)))"
                    "(def s (str/upper-case \"x\"))"
                    "(def b (blank? \"y\"))"
                    "(def l (ArrayList.))")]
    (analysed! a)
    (testing "which namespaces the file really reaches into"
      (is (contains? (an/ns-referenced-namespaces 'lints.a) 'clojure.string))
      (is (not (contains? (an/ns-referenced-namespaces 'lints.a) 'clojure.walk))))
    (is (= '{walk clojure.walk} (an/unused-aliases 'lints.a)))
    (is (= {'trim (resolve 'clojure.string/trim)} (an/unused-refers 'lints.a)))
    (is (= {'Date java.util.Date} (an/unused-imports 'lints.a)))))

(deftest the-file-a-source-names
  (let [a (written! "onfile/a.clj"
                    "(ns onfile.a)"
                    "(def x 1)")]
    (analysed! a)
    (is (= (.getCanonicalFile (io/file @root a))
           (.getCanonicalFile (an/source->file a))))
    (is (nil? (an/source->file "onfile/nothing.clj")))))
