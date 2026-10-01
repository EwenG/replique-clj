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

(deftest keywords-in-code-the-program-does-not-run
  (let [_ (written! "records/k.cljc"
                    "(ns records.k)"
                    "#_(def k0 :top-discard)"
                    "(def k1 [1 #_:nested-discard 2])"
                    "(def k2 #?(:clj :clj-branch :cljs :cljs-branch))")]
    (an/run-analysis #(load "/records/k"))
    (testing "a #_ discard is still written in the file, at the top level or nested"
      (is (= [2] (map :line (an/find-keyword-usages :top-discard))))
      (is (= [3] (map :line (an/find-keyword-usages :nested-discard)))))
    (testing "the branch of a reader conditional this platform does not take is not"
      (is (= [4] (map :line (an/find-keyword-usages :clj-branch))))
      (is (empty? (an/find-keyword-usages :cljs-branch))))))

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

(deftest a-var-quote-is-a-usage-of-the-var
  ;; #'a/b is a reference to the var, written where it is written - and the one
  ;; the compiler would otherwise miss, because (var b) resolves in
  ;; TheVarExpr$Parser and never reaches analyzeSymbol. What is behind it in real
  ;; code is alter-var-root, add-watch, a with-redefs, and binding - whose
  ;; expansion var-izes the very symbol the source wrote.
  (let [target (written! "vq/t.clj"
                         "(ns vq.t)"
                         "(def ^:dynamic *flag* true)"
                         "(defn f [] 1)"
                         "(defmacro m [] 1)")
        uses   (written! "vq/u.clj"
                         "(ns vq.u"
                         "  (:require [vq.t :as t]))"
                         "(def plain t/f)"
                         "(alter-var-root #'vq.t/*flag* (constantly false))"
                         "(alter-var-root #'t/f (constantly (fn [] 2)))"
                         "(defn g [] (binding [t/*flag* false] (t/f)))"
                         "(def macro-var #'t/m)"
                         "(def quoted 'vq.t/f)"
                         "(defmacro conjured [] (list 'var (symbol \"vq.t\" \"f\")))"
                         "(def by-a-macro (conjured))")]
    (analysed! target uses)
    (testing "the span is the symbol's, so the #' in front of it stays put"
      (let [flag (sort-by :line (an/find-usages 'vq.t/*flag*))]
        (is (= ["vq.t/*flag*" "t/*flag*"] (mapv text-at flag)))
        (is (= [4 6] (mapv :line flag)))
        (is (every? #(= 'vq.u (ns-name (:from-ns %))) flag))))
    (testing "written under an alias or in full, it is the same var"
      (let [f (sort-by :line (an/find-usages 'vq.t/f))]
        (is (= ["t/f" "t/f" "t/f"] (mapv text-at f)))
        (is (= [3 5 6] (mapv :line f)))))
    (testing "a macro can be var-quoted where it cannot be called for its value"
      (let [m (an/find-usages 'vq.t/m)]
        (is (= 1 (count m)))
        (is (= "t/m" (text-at (first m))))))
    (testing "and a QUOTED symbol is still not a usage: it is data, and what it
    names is decided, if ever, at run time"
      (is (not-any? #(= 8 (:line %)) (an/find-usages 'vq.t/f))))
    (testing "nor is a var-quote a macro CONJURED, which is written in nobody's
    file: the symbol carries no reader position, and recording it would put a
    place-to-go at the line of whatever expanded it"
      (is (not-any? #(= 10 (:line %)) (an/find-usages 'vq.t/f))))
    (testing "the def of the macro that defines a name is not a usage of it
    either - defmacro's own expansion var-quotes the name twice"
      (let [m (an/find-usages 'vq.t/m)]
        (is (= [7] (mapv :line m)))))))

(deftest a-name-that-ends-its-line-ends-where-it-ends
  (let [source (written! "eol/a.clj"
                         "(ns eol.a)"
                         "(def target 1)"
                         "(def at-eol"
                         "  target"
                         "  )"
                         "(def in-a-vector [target"
                         "                  2])"
                         "(def mid-line (+ target 1))"
                         "(def tagged [^:hint target"
                         "             2])")]
    (analysed! source)
    (testing "a span ends just past the name it is about, whether or not the name
              is the last thing on its line. The reader ends a token by reading one
              character too many and putting it back, and by the time it puts a
              newline back it has counted the line - so the end has to be taken
              from what stayed read, not from where the reader stands"
      (let [uses (sort-by :line (an/find-usages 'eol.a/target))]
        (is (= [4 6 8 9] (mapv :line uses)))
        (is (= [4 6 8 9] (mapv :end-line uses)))
        (is (= #{"target"} (set (map text-at uses))))))))

(deftest what-an-ns-form-names-is-where-the-name-is-written
  (let [_ (written! "declared/lib.clj"
                    "(ns declared.lib)"
                    "(defn twice [x] (* 2 x))"
                    "(defn thrice [x] x)"
                    "(defn only-named [x] x)"
                    "(defn renamed [x] x)"
                    "(defn all-of-them [x] x)")
        _ (written! "declared/deep.clj"
                    "(ns declared.deep)"
                    "(defn under-a-prefix [x] x)")
        source (written! "declared/a.clj"
                         "(ns declared.a"
                         "  (:refer-clojure :exclude [second])"
                         "  (:require [declared.lib :as lib :refer [twice thrice renamed]"
                         "                          :rename {renamed local-name}]"
                         "            [declared [deep :refer [under-a-prefix]]])"
                         "  (:use [declared.lib :only [only-named]])"
                         "  (:import [java.io File StringWriter]"
                         "           java.util.Date))"
                         "(defn run [] (+ (twice 1) (lib/thrice 2)))"
                         "(def f (File. \"x\"))")
        ;; on its own, because a :refer-clojure :only leaves the file without
        ;; defn or +, so a file with a body cannot have one
        only (written! "declared/b.clj"
                       "(ns declared.b"
                       "  (:refer-clojure :only [first]))")]
    (analysed! source only)
    (letfn [(declared [qsym]
              (->> (an/find-usages qsym)
                   (filter :declaration)
                   (map (juxt :line :column :declaration text-at))
                   (sort-by first)
                   vec))
            (imported [c]
              (->> (an/find-class-usages c)
                   (filter :declaration)
                   (map (juxt :line :declaration text-at))
                   (sort-by first)
                   vec))]
      (testing "a :refer names the var, and the span is the name in the spec -
      which is what a rename has to replace and the one mention of it no analysis
      of code can reach: the ns form hands its specs on quoted"
        (is (= [[3 43 :refer "twice"]] (declared 'declared.lib/twice))))
      (testing "and it is one list with the uses, so where-is-this-used answers
      the ns form along with the call sites"
        (is (= [[3 :refer] [9 nil]]
               (sort-by first (map (juxt :line :declaration)
                                   (an/find-usages 'declared.lib/thrice))))))
      (testing "a :use's :only is the same fact written the other way"
        (is (= [[6 30 :refer "only-named"]] (declared 'declared.lib/only-named))))
      (testing "a :rename names the var by its key - the name being replaced -
      and not by the value, which no var is called. Both places it is written are
      places, and both have to be rewritten together"
        (is (= [[3 56 :refer "renamed"] [4 36 :refer "renamed"]]
               (declared 'declared.lib/renamed))))
      (testing "a prefix list is walked the way a require walks it"
        (is (= [[5 37 :refer "under-a-prefix"]] (declared 'declared.deep/under-a-prefix))))
      (testing ":refer-clojure names vars of clojure.core, the one clause that
      writes a namespace nowhere in itself"
        (is (= [[2 26 :refer "first"]] (declared 'clojure.core/first))))
      (testing "an :exclude is not one: it names what this namespace will NOT be
      writing, which is the opposite of a place the name is written"
        (is (= [] (declared 'clojure.core/second))))
      (testing "a require that refers nothing names nothing: what it writes is the
      namespace, and that is a different question"
        (is (= [] (declared 'declared.lib/all-of-them))))
      (testing "an :import names the class, at the short name under a package spec
      and over the whole of a name written in full"
        (is (= [[7 21 :import "File"] [10 9 nil nil]]
               (sort-by first (map (juxt :line :column :declaration
                                         #(when (:declaration %) (text-at %)))
                                   (an/find-class-usages java.io.File)))))
        (is (= [[7 :import "StringWriter"]] (imported java.io.StringWriter)))
        (is (= [[8 :import "java.util.Date"]] (imported java.util.Date))))
      (testing "and none of them is a USE, so the lints that ask what a namespace
      does not need still answer - a refer kept alive by its own :refer would be a
      refer nothing could ever report"
        ;; `thrice' is the one worth reading twice: it IS used, and through the
        ;; alias, so the refer that names it is doing nothing and taking it out
        ;; would change nothing. A refer is about how a name is spelled, which is
        ;; why the answer is by the spelling and not by whether the var is used.
        (is (= {'only-named (resolve 'declared.lib/only-named)
                'under-a-prefix (resolve 'declared.deep/under-a-prefix)
                'local-name (resolve 'declared.lib/renamed)
                'thrice (resolve 'declared.lib/thrice)}
               (an/unused-refers 'declared.a)))
        (is (not (contains? (an/unused-refers 'declared.a) 'twice))
            "and `twice', which the body writes short, is not one")
        (is (= {'StringWriter java.io.StringWriter, 'Date java.util.Date}
               (an/unused-imports 'declared.a)))))))

(deftest a-type-that-implements-a-protocol-is-a-usage-of-it
  (let [a (written! "implements/a.clj"
                    "(ns implements.a)"
                    "(defprotocol P"
                    "  (kept [this])"
                    "  (other [this]))")
        b (written! "implements/b.clj"
                    "(ns implements.b (:require [implements.a :as a]))"
                    "(defn call [x] (a/kept x))"
                    "(deftype T [v]"
                    "  a/P"
                    "  (kept [this] v)"
                    "  (other [this] v))"
                    "(defrecord R [v]"
                    "  a/P"
                    "  (kept [this] v)"
                    "  (other [this] v))"
                    "(def made"
                    "  (reify a/P"
                    "    (kept [this] 1)"
                    "    (other [this] 2)))"
                    "(extend-type String"
                    "  a/P"
                    "  (kept [this] 3)"
                    "  (other [this] 4))"
                    "(def in-one-line (reify a/P (kept [this] 5) (other [this] 6)))")]
    (analysed! a b)
    (testing "a deftype, a defrecord and a reify name the interface the protocol
              generated by the time the compiler sees it, and the occurrence is
              recorded where the protocol is written"
      (let [uses (an/find-class-usages (:on-interface @(ns-resolve 'implements.a 'P)))]
        (is (= #{4 8 12 19} (set (map :line uses))))
        (is (= #{3 10 25} (set (map :column uses))))
        (is (= '#{implements.b} (set (map #(ns-name (:from-ns %)) uses))))
        (testing "and every one of them picks out the name, the four that end
                  their line included"
          (is (= #{"a/P"} (set (map text-at uses)))))))
    (testing "and asking where the protocol is used answers those together with
              the code that extends it, which names the var itself"
      (is (= #{4 8 12 16 19} (set (map :line (an/find-usages 'implements.a/P))))))
    (testing "while a method answers its call sites: what implements a method is
              the form that implements its protocol, and a type need not implement
              every method it could"
      (is (= #{2} (set (map :line (an/find-usages 'implements.a/kept)))))
      (is (empty? (an/find-usages 'implements.a/other))))))

(deftest the-interfaces-a-macro-named-are-not-usages
  (let [a (written! "written/a.clj"
                    "(ns written.a)"
                    "(deftype Ran []"
                    "  Runnable"
                    "  (run [this] nil))"
                    "(defrecord Rec [v])"
                    "(def made (reify Runnable (run [this] nil)))")]
    (analysed! a)
    (testing "an interface the source names is recorded, wherever it names it"
      (let [uses (an/find-class-usages Runnable)]
        (is (= #{3 6} (set (map :line uses))))
        (is (= "Runnable" (text-at (first (filter #(= 6 (:line %)) uses)))))))
    (testing "and the ones the expansion added are not: nobody wrote them, no
              position points at them, and a file listing them as its own uses
              would be a file nobody could read"
      (is (empty? (an/find-class-usages 'clojure.lang.IObj)))
      (is (empty? (an/find-class-usages 'clojure.lang.IRecord)))
      (is (empty? (an/find-class-usages 'java.util.Map))))))

(deftest a-proxy-names-the-classes-it-proxies
  ;; `proxy' is the sharpest case of a name a macro eats: it RESOLVES its base
  ;; classes while it expands and returns a form naming only the class it generated,
  ;; so no class reference the source wrote is ever analysed. Without the hook in its
  ;; body an import nothing but a proxy uses reads as unused - and that is the bad
  ;; direction, since taking the import out stops the file compiling.
  (let [a (written! "proxied/a.clj"
                    "(ns proxied.a (:import [java.util.concurrent Callable]"
                    "                       [java.io File]))"
                    "(def called (proxy [Callable] [] (call [] 1)))"
                    ;; a class vector a macro made up: nobody wrote that name here
                    "(defmacro made []"
                    "  (list 'proxy [(symbol \"java.lang.Runnable\")] [] '(run [] nil)))"
                    "(def ran (made))")]
    (analysed! a)
    (testing "the class a proxy names is used where the proxy names it"
      (let [uses (an/find-class-usages java.util.concurrent.Callable)]
        (is (= #{1 3} (set (map :line uses)))
            "line 1 being the :import that declares it, line 3 the proxy")
        (is (= "Callable" (text-at (first (filter #(= 3 (:line %)) uses)))))))
    (testing "so an import nothing but a proxy uses is not unused, and one nothing
              uses at all still is"
      (is (= {'File java.io.File} (an/unused-imports 'proxied.a))))
    (testing "and the one a macro made up is nobody's: no position points at it"
      (is (empty? (an/find-class-usages Runnable))))))

(deftest a-read-a-macro-left-nowhere-is-still-a-read
  ;; The capture rule says a usage is recorded WHERE THE NAME IS WRITTEN, and a
  ;; macro can destroy that without touching the reference: `with-meta' on a form it
  ;; was handed replaces the reader's position wholesale. clojure.core/vswap! does
  ;; it to its volatile, and every logging macro that tags an exception does it to
  ;; the exception. What is left is a read with no place - which is exactly what
  ;; unused-binding asks about, and no place is needed to answer it.
  (let [m (written! "nowhere/m.clj"
                    "(ns nowhere.m)"
                    "(defmacro tagged [x] (with-meta x {:tag 'Object}))")
        a (written! "nowhere/a.clj"
                    "(ns nowhere.a (:require [nowhere.m :as m]))"
                    "(defn read-through-a-macro [through] (m/tagged through))"
                    "(defn read-plainly [plain] plain)"
                    "(defn never-read [unread] :ok)")]
    (analysed! m a)
    (testing "a binding read only through a macro that replaced the metadata is read"
      (is (= #{"unread"} (set (map :name (an/unused-locals 'nowhere.a))))))
    (testing "and the read is still no place: there is nothing in the file to point
              at, so the binding is all find-local-usages has to give"
      (is (= [[2 29 :binding]]
             (->> (an/find-local-usages a 2 29) (map (juxt :line :column :declaration))
                  sort vec))))
    (testing "while a read that IS somewhere is still a place"
      (is (= [[3 21 :binding] [3 28 nil]]
             (->> (an/find-local-usages a 3 21) (map (juxt :line :column :declaration))
                  sort vec))))))

(deftest a-require-is-used-by-how-the-source-spells-it
  ;; Whether a require is needed is a question about SPELLING. A name reaching the
  ;; compiler as `lib/f' resolves only because this namespace has that alias, so the
  ;; alias is holding it up whatever else happened to the form on the way; one
  ;; reaching it as `spelled.lib/f' needs nothing of the ns form - and that is also
  ;; what macroexpansion leaves behind, since syntax-quote qualifies what it names.
  (let [lib (written! "spelled/lib.clj"
                      "(ns spelled.lib)"
                      "(defn f [x] x)")
        m   (written! "spelled/m.clj"
                      "(ns spelled.m (:require [spelled.lib :as l] [clojure.walk]))"
                      "(defmacro calls-lib [x] `(l/f ~x))"
                      "(defmacro rebuilt [& body]"
                      "  (clojure.walk/postwalk"
                      "   #(if (instance? clojure.lang.IObj %) (with-meta % nil) %)"
                      "   (cons 'do body)))")
        ;; the alias is written here, and then the macro rebuilds the body it was
        ;; given without the reader's metadata - what a core.async `go' does
        a   (written! "spelled/a.clj"
                      "(ns spelled.a (:require [spelled.lib :as lib]"
                      "                        [spelled.m :as m]))"
                      "(defn run [x] (m/rebuilt (lib/f x)))")
        ;; and here the namespace is named nowhere at all - only the macro's body
        ;; names it, and names it in full
        b   (written! "spelled/b.clj"
                      "(ns spelled.b (:require [spelled.lib :as lib]"
                      "                        [spelled.m :as m]))"
                      "(defn run [x] (m/calls-lib x))")]
    (analysed! lib m a b)
    (testing "an alias named through a macro that left the name nowhere is used"
      (is (= {} (an/unused-aliases 'spelled.a))))
    (testing "and a macro's own body naming the namespace in full does not make its
              caller's alias used - the caller never wrote it"
      (is (= {'lib 'spelled.lib} (an/unused-aliases 'spelled.b))))
    (testing "what is nowhere is nowhere, and find-usages answers only the places"
      (is (= #{[m 2 27]}
             (set (map (juxt :source :line :column) (an/find-usages 'spelled.lib/f))))
          "the macro's own body, which is a syntax-quoted reference the reader caught"))))

(deftest a-var-of-its-own-namespace-left-nowhere-in-full-is-still-a-reference
  ;; What a core.async `go' does to the vars of its body: each one comes back as a
  ;; fresh symbol spelled in full, with no position. Spelled in full, it says
  ;; nothing of the ns form - but named in its own namespace, it is still the only
  ;; trace that a private helper is called at all.
  (let [m (written! "selfref/m.clj"
                    "(ns selfref.m (:require [clojure.walk]))"
                    "(defmacro requalified [& body]"
                    "  (clojure.walk/postwalk"
                    "   #(if-let [v (and (symbol? %) (resolve %))]"
                    "      (if (var? v)"
                    "        (let [mt (meta v)]"
                    "          (symbol (str (ns-name (:ns mt))) (str (:name mt))))"
                    "        %)"
                    "      %)"
                    "   (cons 'do body)))")
        lib (written! "selfref/lib.clj"
                      "(ns selfref.lib)"
                      "(defn f [x] x)")
        a (written! "selfref/a.clj"
                    "(ns selfref.a (:require [selfref.m :as m] [selfref.lib :as lib]))"
                    "(defn- helper [x] x)"
                    "(defn run [x] (m/requalified (helper (lib/f x))))")]
    (analysed! m lib a)
    (testing "the var of its own namespace is a reference, at the form it is in"
      (is (= [['selfref.a/helper 3 1]]
             (mapv (juxt :var :line :column)
                   (filter #(= 'selfref.a/helper (:var %)) (:refs (an/file-facts a)))))))
    (testing "and one of another namespace, spelled in full, is still not kept"
      (is (empty? (filter #(= 'selfref.lib/f (:var %)) (:refs (an/file-facts a))))))
    (testing "and it is still no place"
      (is (empty? (an/find-usages 'selfref.a/helper))))))

(deftest an-alias-is-used-where-the-text-spells-it
  ;; The two the compiler cannot answer for, because what the file wrote never
  ;; reaches it as what the file wrote: a symbol a macro EATS at expansion time, and
  ;; one a macro re-emits FULLY QUALIFIED - which is what core.async's `go' does to
  ;; every name in its body. Both are the alias doing its job all the same: take the
  ;; :as out and the file stops reading. Only the reader ever saw it; see the sink's
  ;; qualifierUsage.
  (let [lib  (written! "spelt/lib.clj"
                       "(ns spelt.lib)"
                       "(defn f [x] x)")
        m    (written! "spelt/m.clj"
                       "(ns spelt.m (:require [clojure.walk]))"
                       ;; eats it: what it is given is read and nothing of it emitted
                       "(defmacro eaten [sym] (name sym))"
                       ;; re-emits it in full, as a `go' block does
                       "(defmacro requalified [& body]"
                       "  (clojure.walk/postwalk"
                       "   #(if-let [v (and (symbol? %) (namespace %) (resolve %))]"
                       "      (let [mt (meta v)]"
                       "        (symbol (str (ns-name (:ns mt))) (str (:name mt))))"
                       "      %)"
                       "   (cons 'do body)))")
        eats (written! "spelt/a.clj"
                       "(ns spelt.a (:require [spelt.lib :as lib] [spelt.m :as m]))"
                       "(def what (m/eaten lib/f))")
        reqs (written! "spelt/b.clj"
                       "(ns spelt.b (:require [spelt.lib :as lib] [spelt.m :as m]))"
                       "(defn run [x] (m/requalified (lib/f x)))")
        full (written! "spelt/c.clj"
                       "(ns spelt.c (:require [spelt.lib :as lib] [spelt.m :as m]))"
                       "(def what (m/eaten spelt.lib/f))")
        gone (written! "spelt/d.clj"
                       "(ns spelt.d (:require [spelt.lib :as lib]))"
                       "(defn run [x] #_(lib/f x) x)")
        rich (written! "spelt/e.clj"
                       "(ns spelt.e (:require [spelt.lib :as lib]))"
                       "(comment (lib/f 1))")]
    (analysed! lib m eats reqs full gone rich)
    (testing "a symbol a macro ate is written where it is written"
      (is (= {} (an/unused-aliases 'spelt.a))))
    (testing "and so is one a macro handed back in full"
      (is (= {} (an/unused-aliases 'spelt.b))))
    (testing "but writing the namespace is not writing the alias"
      (is (= {'lib 'spelt.lib} (an/unused-aliases 'spelt.c))
          "the require is needed and the :as is not - two questions, two answers"))
    (testing "a spelling in a #_ is a spelling of code that is gone"
      (is (= {'lib 'spelt.lib} (an/unused-aliases 'spelt.d))))
    (testing "one in a (comment ...) is not: the block is meant to be run"
      (is (= {} (an/unused-aliases 'spelt.e))))))

(deftest a-namespaced-map-or-a-tag-does-not-move-the-form-it-is-in
  ;; Both are read by a reader macro that reads a part of its own form - the
  ;; namespace after #:, the tag after # - and a nested read that called itself
  ;; top-level would report that part as the start of the whole form.
  (let [a (written! "starts/a.clj"
                    "(ns starts.a (:require [starts.a :as self]))"
                    "(def plain 1)"
                    "(def a-nsmap #::self{:k 1})"
                    "(def an-auto-nsmap #::{:k 1})"
                    "(def a-tag #inst \"2020-01-01\")"
                    "(def after 2)")]
    (analysed! a)
    (is (= [[1 1] [2 1] [3 1] [4 1] [5 1] [6 1]]
           (sort (map (juxt :line :column) (:forms (an/file-facts a)))))
        "every form starts where it starts, and none of them in the middle of itself")))

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

(deftest the-query-indexes-are-built-once-per-form-log
  ;; The other half of the bargain the test above tests one side of: the indexes
  ;; are replayed from the whole form log, so every query would pay for the whole
  ;; model if asking twice built them twice. Nothing public exposes the cache, and
  ;; nothing public can tell a hit from a miss - a correct answer is a correct
  ;; answer either way - so the test asks the private for the index itself and
  ;; looks at its identity. The model is deliberately not empty: an empty index is
  ;; built from constants, and would come back identical from a cache that had
  ;; never worked at all.
  (let [source (written! "cachehit/a.clj"
                         "(ns cachehit.a)"
                         "(def x 1)")]
    (analysed! source)
    (let [m @@#'an/model]
      (doseq [k @#'an/index-keys]
        (is (identical? (#'an/index m k) (#'an/index m k))
            (str "second ask for " k " rebuilt it"))))
    (is (seq (:defs (#'an/derived @@#'an/model))))))

(deftest asking-one-index-does-not-build-the-others
  ;; What having a cache EACH is for. They are not wanted at the same times - a
  ;; reload reads `:defs` while it prunes and reads nothing else, and `:usages` and
  ;; `:locals` are the large ones - so one index built is one index built, and the
  ;; rest are still unbuilt behind their own caches. Held as one index they were all
  ;; rebuilt whenever any of them was, and a reload of K files paid for the whole
  ;; model K times.
  ;;
  ;; Read off the caches rather than off a clock, since what is being tested is
  ;; that work did NOT happen and a fast answer is not a claim that it did not.
  (let [source (written! "cacheeach/a.clj"
                         "(ns cacheeach.a)"
                         "(def x (let [y 1] y))")]
    (analysed! source)
    (let [m     @@#'an/model
          built (fn [] (set (for [[k c] @#'an/index-caches
                                  :when (identical? (:forms m) (:forms @c))]
                              k)))]
      ;; a fresh log, so nothing is built for it yet
      (is (empty? (built)))
      (#'an/index m :defs)
      (is (= #{:defs} (built)))
      (#'an/index m :locals)
      (is (= #{:defs :locals} (built)))
      ;; while `derived` is all of them, which is why it is not what a reload asks
      (#'an/derived m)
      (is (= (set @#'an/index-keys) (built))))))

(deftest file-def-vars-answers-what-a-walk-of-the-defs-answered
  ;; `file-def-vars` reads the file's own forms instead of walking every def in the
  ;; model. Same answer, and the case where it could differ is the one pinned here: a
  ;; var two files define belongs to the file whose def WON - the later one - in both
  ;; readings, and is not in the earlier file's answer.
  (let [a (written! "bysource/a.clj"
                    "(ns bysource.a)"
                    "(def only-a 1)"
                    "(def shared 1)")
        b (written! "bysource/b.clj"
                    "(in-ns 'bysource.a)"
                    "(def shared 2)")]
    (analysed! a)
    (is (= '#{bysource.a/only-a bysource.a/shared} (an/file-def-vars @@#'an/model a)))
    (analysed! b)
    (let [m @@#'an/model
          walked (fn [source]
                   (set (for [[k e] (#'an/index m :defs)
                              :when (= source (:source (:span e)))]
                          k)))]
      (is (= '#{bysource.a/only-a} (an/file-def-vars m a)))
      (is (= '#{bysource.a/shared} (an/file-def-vars m b)))
      (doseq [source [a b]]
        (is (= (walked source) (an/file-def-vars m source)))))))

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

(deftest what-has-been-analysed-is-a-question-of-its-own
  (testing "a model with nothing in it has read nothing, and that is not the
            same fact as nothing having changed: the two are one answer apart
            and mean opposite things - one says the program is up to date, the
            other says there is no program here to be out of date"
    (is (empty? (an/analysed-files)))
    (is (empty? (an/changed-files))))
  (let [a (written! "readfiles/a.clj" "(ns readfiles.a)" "(def x 1)")]
    (analysed! a)
    (is (= #{a} (an/analysed-files)))
    (testing "and a file retracted is a file it has not read, which is what
              keeps the two questions the same question"
      (an/retract-file! a)
      (is (empty? (an/analysed-files))))))

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

(deftest a-file-the-disk-no-longer-has-is-dropped-by-a-reload
  (let [a (written! "gone/a.clj"
                    "(ns gone.a)"
                    "(defprotocol P"
                    "  (m [this]))"
                    "(def x 1)")
        b (written! "gone/b.clj"
                    "(ns gone.b"
                    "  (:require [gone.a :as a :refer [x]]))"
                    "(def y (+ x 1))")
        err (java.io.StringWriter.)]
    (analysed! a b)
    (is (= 2 @(resolve 'gone.b/y)))
    (deleted! a)
    (testing "a file that is gone is not a changed file - there is nothing to load
              it from - and this is what names it instead"
      (is (empty? (an/changed-files)))
      (is (= #{a} (an/deleted-files))))
    (testing "so a reload reloads nothing, and says so"
      (is (= [] (binding [*err* err] (an/stale-reload! :prune true)))))
    (testing "and what the file defined stops resolving, where it was defined and
              where another namespace referred it, its protocol's methods with it"
      (is (nil? (ns-resolve 'gone.a 'x)))
      (is (nil? (ns-resolve 'gone.a 'P)))
      (is (nil? (ns-resolve 'gone.a 'm)))
      (is (nil? (ns-resolve 'gone.b 'x))))
    (testing "a var something still uses goes all the same, and says where"
      (is (re-find #"gone\.a/x" (str err)))
      (is (re-find #"gone\.b" (str err))))
    (testing "the model stops answering for a file nobody can open, and stops
              calling it deleted once it has been dropped"
      (is (nil? (an/definition 'gone.a/x)))
      (is (empty? (an/file-forms a)))
      (is (empty? (an/deleted-files))))
    (testing "its namespace stops being a loaded lib, so requiring it says what the
              disk says rather than finding the dead entry and doing nothing"
      (is (not (contains? @@#'clojure.core/*loaded-libs* 'gone.a)))
      (is (thrown? java.io.FileNotFoundException (require 'gone.a))))
    (testing "and the file that is still there is left alone"
      (is (= 2 @(resolve 'gone.b/y)))
      (is (some? (an/definition 'gone.b/y)))
      (is (contains? @@#'clojure.core/*loaded-libs* 'gone.b)))))

(deftest a-file-that-is-gone-is-dropped-only-when-something-asks
  (let [a (written! "notgone/a.clj" "(ns notgone.a)" "(def x 1)")]
    (analysed! a)
    (deleted! a)
    (testing "the model keeps it until a reload runs: a file between two writes
              looks exactly like a file that is gone, and nothing here polls"
      (is (= #{a} (an/deleted-files)))
      (is (some? (an/definition 'notgone.a/x)))
      (is (some? (ns-resolve 'notgone.a 'x))))
    (testing "and one written back before that is a changed file again, which is
              what an editor that saves by writing a new file over the old one
              leaves behind"
      (written! "notgone/a.clj" "(ns notgone.a)" "(def x 7)")
      (is (empty? (an/deleted-files)))
      (is (= [a] (an/stale-reload! :prune true)))
      (is (= 7 @(resolve 'notgone.a/x))))))

(deftest a-file-that-is-gone-is-not-reloaded-because-a-macro-file-it-expands-changed
  ;; ONE EVENT - a checkout that takes a file away and edits a macro file it expands
  ;; from - and the two halves of it meet in `stale-files`. A gone file cannot SEED
  ;; the cascade, and it could be reached by it, which is what a branch switch does;
  ;; what came of that was `load` handed a resource path nothing answers to.
  (let [m (written! "switched/mac.clj"
                    "(ns switched.mac)"
                    "(defmacro two [] 2)")
        u (written! "switched/use.clj"
                    "(ns switched.use"
                    "  (:require [switched.mac :refer [two]]))"
                    "(def y (two))")]
    (analysed! m u)
    (is (= 2 @(resolve 'switched.use/y)))
    (deleted! u)
    (written! "switched/mac.clj"
              "(ns switched.mac)"
              "(defmacro two [] 3)")
    (is (= #{m} (an/changed-files)))
    (is (= #{u} (an/deleted-files)))
    (testing "the gone file expands a macro of the file that changed, and is taken
              back out of what would be loaded all the same: there is nothing to
              load it from"
      (is (= #{m} (an/stale-files))))
    (is (= [m] (an/stale-reload! :prune true)))
    (is (empty? (an/file-forms u)))))

(deftest load-file!-tells-a-path-of-the-wrong-shape-from-a-file-that-is-gone
  (let [a (written! "shape/a.clj" "(ns shape.a)" "(def x 1)")]
    (analysed! a)
    (testing "an absolute path is the editor's to translate, and saying so is the
              whole point of catching it here"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"classpath-relative"
                            (an/load-file! (str (io/file @root a))))))
    (deleted! a)
    (testing "and a path whose shape is the one thing right about it is the other
              refusal: sending the caller to look at their path would send them
              where the answer is not"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"nothing on the classpath"
                            (an/load-file! a))))))

(deftest a-reload-that-drops-a-file-leaves-what-it-does-not-speak-for
  (let [a (written! "keeps/a.clj"
                    "(ns keeps.a)"
                    "(def x 1)")
        b (written! "keeps/b.clj"
                    "(ns keeps.b)"
                    "(def x 2)")]
    (analysed! a b)
    (intern 'keeps.a 'by-hand 3)
    (.addAlias (the-ns 'keeps.a) 'bee (the-ns 'keeps.b))
    (deleted! a)
    (an/stale-reload! :prune true)
    (testing "a var an intern made is left where it is: nothing recorded it, so
              nothing here says it has gone"
      (is (some? (ns-resolve 'keeps.a 'by-hand))))
    (testing "the namespace object is left standing, with its aliases - the file
              is what was dropped, not the namespace"
      (is (some? (find-ns 'keeps.a)))
      (is (= (the-ns 'keeps.b) (get (ns-aliases 'keeps.a) 'bee))))
    (testing "and another namespace's var of the same name is another var"
      (is (= 2 @(ns-resolve 'keeps.b 'x))))))

(deftest a-namespace-another-file-still-defines-stays-loaded
  (let [a (written! "shared/a.clj"
                    "(ns shared.n)"
                    "(def from-a 1)")
        b (written! "shared/b.clj"
                    "(ns shared.n)"
                    "(def from-b 2)")]
    (analysed! a b)
    (deleted! a)
    (an/stale-reload! :prune true)
    (testing "what the gone file defined goes"
      (is (nil? (ns-resolve 'shared.n 'from-a))))
    (testing "but the namespace is still a loaded lib, because a file that is
              still there still defines it - one namespace, two files"
      (is (some? (ns-resolve 'shared.n 'from-b)))
      (is (contains? @@#'clojure.core/*loaded-libs* 'shared.n)))))

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

(deftest a-file-a-jar-answers-to-is-shadowed-rather-than-gone
  (let [source (written! "shadowed/lib.clj"
                         "(ns shadowed.lib)"
                         "(def value 1)")]
    (analysed! source)
    (jar-on-the-classpath! "shadowlib" {"shadowed/lib.clj"
                                        "(ns shadowed.lib)\n(def value 2)\n"})
    (deleted! source)
    (testing "a file a jar has taken over is not a file that is gone: something
              still answers to the name, and what this process holds still came
              from the file"
      (is (empty? (an/deleted-files)))
      (is (= [] (an/stale-reload! :prune true)))
      (is (= 1 @(resolve 'shadowed.lib/value)))
      (is (some? (an/definition 'shadowed.lib/value))))))

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

(defn- class-graph
  "The forward file graph of generated classes for the current model - the other
  half of what the reload walks, and private for `macro-graph`'s reason."
  []
  (#'an/build-file-class-graph @@#'an/model))

(defn- var-graph
  "The forward file graph of var references among `files`, for the current model -
  what orders a reload but does not decide what is in it, and private for
  `macro-graph`'s reason."
  [& files]
  (#'an/file-var-graph @@#'an/model (set files)))

(defn- require-graph
  "The forward file graph of requires among `files`, read off the disk as it is now
  - the ordering edges no model can hold, and private for `macro-graph`'s reason."
  [& files]
  (#'an/file-require-graph @@#'an/model (set files)))

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

(deftest the-macro-graph-is-built-once-per-form-log
  ;; The graph is a pure function of the form log, and the editor's freshness gate
  ;; asks what is stale - hence for the graph - before every find-usages, so it is
  ;; cached on the identity of :forms rather than rebuilt from every macro-dep edge
  ;; in the model on each question. Two things have to hold, and the second is what
  ;; makes the first safe to do: asked twice of an untouched model it is the very
  ;; same map, and asked of a model that has moved on it is a map built from what
  ;; the model now says. The graph is deliberately never empty here - an empty one
  ;; is the constant {}, so a cache that had never worked at all would still hand
  ;; back an identical value for it.
  (let [m (written! "cached/m.clj"
                    "(ns cached.m)"
                    "(defmacro plus [x] (list '+ x 1))")
        a (written! "cached/a.clj"
                    "(ns cached.a (:require [cached.m]))"
                    "(def am (cached.m/plus 1))")
        b (written! "cached/b.clj"
                    "(ns cached.b (:require [cached.m]))"
                    "(def bm (cached.m/plus 2))")]
    (analysed! m a)
    (let [graph (macro-graph)]
      (is (= {a #{m}} graph))
      (is (identical? graph (macro-graph)))
      (testing "a file analysed since is in the graph"
        (analysed! b)
        (is (= {a #{m} b #{m}} (macro-graph)))
        (is (not (identical? graph (macro-graph)))))
      (testing "and a file retracted since is out of it"
        (an/retract-file! b)
        (is (= {a #{m}} (macro-graph)))))))

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
  (testing "and breaking it costs only the cycle: one file of it is placed and the
            rest of the order goes on being an order, rather than every remaining
            file being tipped out in whatever order a set iterates in"
    (is (= ["a" "b" "z"] (#'an/topo-order ["z" "a" "b"]
                                          {"a" #{"b"} "b" #{"a"} "z" #{"a" "b"}}))))
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

(deftest a-var-reference-orders-a-reload-without-widening-it
  ;; The bug this is about: `app` uses a var of `lib`'s, both are edited, and the
  ;; edit moves the definition `app` uses. Nothing here is compile-time coupling -
  ;; no macro is expanded and no generated class is named - so the compile graph has
  ;; nothing to say, and the two were ordered by whatever the set gave up first.
  ;; Half the time that is `app`, which the compiler then reads while `lib` still
  ;; holds the OLD definitions: `No such var`. And since a failed load stays stale
  ;; and the order is the same next time, every retry fails the same way.
  ;;
  ;; Written with no `:require` for it, so that the only thing that can supply the
  ;; edge is what the compiler recorded: `app` resolves the name because `lib` is
  ;; loaded, which is a shape a file of a namespace somebody else required has.
  (let [lib (written! "varorder/lib.clj"
                      "(ns varorder.lib)"
                      "(clojure.test-clojure.analysis/loaded! 'lib)"
                      "(defn old [] :old)")
        app (written! "varorder/app.clj"
                      "(ns varorder.app)"
                      "(clojure.test-clojure.analysis/loaded! 'app)"
                      "(def v (varorder.lib/old))")]
    (analysed! lib app)
    (testing "a plain var reference is no compile-time dependency, and the graphs
              that decide what is stale go on saying so"
      (is (= {} (macro-graph)))
      (is (= {} (class-graph))))
    (testing "and nothing is declared at the top of the file either"
      (is (= {} (require-graph lib app))))
    (testing "but it is a dependency for the purpose of ORDER, and is one there"
      (is (= {app #{lib}} (var-graph lib app))))
    (testing "over the files being reloaded and no others: a file that is not in
              the set cannot be loaded out of order, so it is not an edge"
      (is (= {} (var-graph app))))
    (written! "varorder/lib.clj"
              "(ns varorder.lib)"
              "(clojure.test-clojure.analysis/loaded! 'lib)"
              "(defn fresh [] :fresh)")
    (written! "varorder/app.clj"
              "(ns varorder.app)"
              "(clojure.test-clojure.analysis/loaded! 'app)"
              "(def v (varorder.lib/fresh))")
    (reset! trace [])
    (testing "so the file that defines is loaded before the file that refers"
      (is (= [lib app] (an/stale-reload!)))
      (is (= '[lib app] @trace)))
    (testing "and the reference the edit introduced resolves, where loading the
              other way round would have been No such var"
      (is (= :fresh @(resolve 'varorder.app/v))))
    (testing "one pass, and nothing left stale"
      (is (= 2 (count @trace)))
      (is (empty? (an/changed-files))))))

(deftest the-requires-of-a-file-are-read-off-the-disk-as-it-is-now
  (let [a (written! "readns/a.cljc"
                    ";; a comment, and then the ns form"
                    "(ns readns.a"
                    "  \"What it is for.\""
                    "  {:author \"nobody\"}"
                    "  (:require [readns.b :as b]"
                    "            [readns [c :as c] [d]]"
                    "            #?(:clj readns.e :cljs readns.f))"
                    "  (:use [readns.g :only [x]])"
                    "  (:import [java.util Date]))"
                    "(def v (b/thing))")
        b (written! "readns/b.clj" "(ns readns.b)")
        c (written! "readns/c.clj" "(ns readns.c)")
        d (written! "readns/d.cljc" "(ns readns.d)")
        e (written! "readns/e.clj" "(ns readns.e)")
        f (written! "readns/f.cljs" "(ns readns.f)")
        g (written! "readns/g.clj" "(ns readns.g)")]
    (testing "a docstring, an attribute map and an :import say nothing about
              order; a :require and a :use do, prefix lists and all, and the
              branch of a reader conditional this platform takes is the one read"
      (is (= {a #{b c d e g}} (require-graph a b c d e f g))))
    (testing "a require of something that is not being reloaded is no constraint
              on the order of what is"
      (is (= {} (require-graph a))))
    (testing "and nothing here has been loaded - this is the disk, not the model"
      (is (= {} (macro-graph)))
      (is (empty? (an/file-forms a)))))
  (testing "a file with no ns form is a target like any other and a source of
            nothing, and one that will not read is not an error"
    (let [x (written! "readns/x.clj" "(def not-an-ns 1)")
          y (written! "readns/y.clj" "(ns readns.y (:require [readns.x]))")
          z (written! "readns/z.clj" "(ns readns.z (:require [readns.x])")]
      (is (= {y #{x}} (require-graph x y z))))))

(deftest a-require-an-edit-adds-orders-the-reload-that-carries-it
  ;; The case no model can answer: before the edit these two files have nothing to
  ;; do with each other, so every graph built from what was loaded last time is
  ;; empty, and the order is whatever the set gives up first. Loading the user
  ;; first is silently wrong rather than loudly: its new `:require` finds the
  ;; namespace already loaded and does nothing, so the compiler reads the new file
  ;; against the OLD definitions and says `No such var`.
  (let [d (written! "newreq/d.clj"
                    "(ns newreq.d)"
                    "(clojure.test-clojure.analysis/loaded! 'd)"
                    "(def a 1)")
        u (written! "newreq/u.clj"
                    "(ns newreq.u)"
                    "(clojure.test-clojure.analysis/loaded! 'u)"
                    "(def b 2)")]
    (analysed! d u)
    (testing "nothing the model holds connects them, because nothing did"
      (is (= {} (macro-graph)))
      (is (= {} (class-graph)))
      (is (= {} (var-graph d u)))
      (is (= {} (require-graph d u))))
    (written! "newreq/d.clj"
              "(ns newreq.d)"
              "(clojure.test-clojure.analysis/loaded! 'd)"
              "(defn fresh [] :fresh)")
    (written! "newreq/u.clj"
              "(ns newreq.u (:require [newreq.d]))"
              "(clojure.test-clojure.analysis/loaded! 'u)"
              "(def v (newreq.d/fresh))")
    (testing "the new source of the file that has come looking says where it went"
      (is (= {u #{d}} (require-graph d u))))
    (reset! trace [])
    (testing "so the file that grew the definition is loaded first, in one pass"
      (is (= [d u] (an/stale-reload!)))
      (is (= '[d u] @trace)))
    (testing "and the reference the edit introduced resolves"
      (is (= :fresh @(resolve 'newreq.u/v))))))

(deftest a-var-reference-does-not-put-a-file-in-a-reload
  ;; The other half of the same rule: ordering by var references must not turn into
  ;; reloading by them. A call re-resolves its var every time it runs, so a file that
  ;; only calls into an edited file is already current and is not loaded again.
  (let [d (written! "varcascade/d.clj"
                    "(ns varcascade.d)"
                    "(clojure.test-clojure.analysis/loaded! 'd)"
                    "(defn answer [] 1)")
        u (written! "varcascade/u.clj"
                    "(ns varcascade.u (:require [varcascade.d]))"
                    "(clojure.test-clojure.analysis/loaded! 'u)"
                    "(defn ask [] (varcascade.d/answer))")]
    (analysed! d u)
    (written! "varcascade/d.clj"
              "(ns varcascade.d)"
              "(clojure.test-clojure.analysis/loaded! 'd)"
              "(defn answer [] 2)")
    (is (= #{d} (an/stale-files)))
    (reset! trace [])
    (is (= [d] (an/stale-reload!)))
    (is (= '[d] @trace))
    (testing "and the caller, never reloaded, calls the new definition anyway"
      (is (= 2 ((resolve 'varcascade.u/ask)))))))

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

(deftest an-edit-makes-what-implements-its-protocols-stale-too
  (let [a (written! "iface/a.clj"
                    "(ns iface.a)"
                    "(defprotocol P"
                    "  (greet [this]))")
        b (written! "iface/b.clj"
                    "(ns iface.b (:require [iface.a :as a]))"
                    "(deftype T []"
                    "  a/P"
                    "  (greet [this] \"hello\"))"
                    "(def t (T.))")
        c (written! "iface/c.clj"
                    "(ns iface.c (:require [iface.a :as a]))"
                    "(defn ask [x] (a/greet x))")]
    (analysed! a b c)
    (is (= "hello" ((resolve 'iface.a/greet) @(resolve 'iface.b/t))))
    (written! "iface/a.clj"
              "(ns iface.a)"
              "(defprotocol P"
              "  (greet [this])"
              "  (farewell [this]))")
    (testing "the file that implements the protocol is stale, though nothing in it
              changed and no macro of the edited file reaches it - `deftype` is
              clojure.core's macro, so the only macro edge the type has is to
              clojure.core, and the file whose `defprotocol` generated the
              interface it was compiled against is not in that graph at all"
      (is (= #{a} (an/changed-files)))
      (is (= {b #{a}} (class-graph)))
      (is (contains? (an/stale-files) b)))
    (testing "while the file that only CALLS the protocol's methods is not: a
              method is a var, resolved again every time it runs"
      (is (not (contains? (an/stale-files) c))))
    (testing "and the reload loads the protocol before the type, so the type ends
              up implementing the interface the protocol has now"
      (is (= [a b] (an/stale-reload! :prune true)))
      (is (= "hello" ((resolve 'iface.a/greet) @(resolve 'iface.b/t))))
      (is (= "hello" ((resolve 'iface.c/ask) @(resolve 'iface.b/t)))))))

(deftest a-protocol-implemented-in-its-own-file-is-not-its-own-dependent
  (let [a (written! "ownface/a.clj"
                    "(ns ownface.a)"
                    "(defprotocol P"
                    "  (greet [this]))"
                    "(deftype T []"
                    "  P"
                    "  (greet [this] \"hello\"))")]
    (analysed! a)
    (written! "ownface/a.clj"
              "(ns ownface.a)"
              "(defprotocol P"
              "  (greet [this])"
              "  (farewell [this]))"
              "(deftype T []"
              "  P"
              "  (greet [this] \"hello\")"
              "  (farewell [this] \"bye\"))")
    (testing "a file compiles against its own classes in one pass, so it depends
              on itself for nothing - and a self-edge would leave topo-order with
              no file it could place first"
      (is (= {} (class-graph)))
      (is (= #{a} (an/stale-files)))
      (is (= [a] (an/stale-reload! :prune true))))))

(deftest a-file-that-imports-a-class-does-not-generate-it
  (let [a (written! "imported/a.clj"
                    "(ns imported.a (:import [java.util Date]))"
                    "(defn ->Date [] (Date. 0))")
        b (written! "imported/b.clj"
                    "(ns imported.b (:import [java.util Date]))"
                    "(defn epoch? [^Date d] (zero? (.getTime d)))")]
    (analysed! a b)
    (written! "imported/a.clj"
              "(ns imported.a (:import [java.util Date]))"
              "(defn ->Date [] (Date. 1))")
    (testing "a ->X factory written by hand over an IMPORTED class does not make
              its file the one that generates that class: the class a deftype here
              would have made is called imported.a.Date, and this one is called
              java.util.Date - so the file that names it is left alone"
      (is (= {} (class-graph)))
      (is (= #{a} (an/stale-files))))))

(deftest an-edit-makes-what-names-its-generated-classes-stale-too
  (let [a (written! "genclass/a.clj"
                    "(ns genclass.a)"
                    "(defrecord R [x])")
        b (written! "genclass/b.clj"
                    "(ns genclass.b (:require [genclass.a])"
                    "  (:import [genclass.a R]))"
                    "(defn mine? [x] (instance? R x))")]
    (analysed! a b)
    (is (true? ((resolve 'genclass.b/mine?) (eval '(genclass.a.R. 1)))))
    (written! "genclass/a.clj"
              "(ns genclass.a)"
              "(defrecord R [x y])")
    (testing "a defrecord recompiled is a NEW class of the same name, so the file
              that names it holds a class the rest of the program has stopped
              agreeing with - two classes called genclass.a.R, and an `instance?`
              that answers no"
      (is (contains? (an/stale-files) b)))
    (testing "so it is loaded again, after the file that generates the class"
      (is (= [a b] (an/stale-reload! :prune true)))
      (is (true? ((resolve 'genclass.b/mine?) (eval '(genclass.a.R. 1 2))))))))

(deftest a-class-nothing-in-the-model-defines-owns-no-file
  (let [a (written! "noowner/a.clj"
                    "(ns noowner.a)"
                    "(def epoch (java.util.Date. 0))")
        b (written! "noowner/b.clj"
                    "(ns noowner.b)"
                    "(defn now [] (java.util.Date.))")]
    (analysed! a b)
    (written! "noowner/a.clj"
              "(ns noowner.a)"
              "(def epoch (java.util.Date. 1))")
    (testing "both files name java.util.Date, and neither one defines it - a class
              no reload can generate again is a class nothing can go stale against"
      (is (= #{a} (an/stale-files))))))

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
    (testing "but a var no def form ever made is not a candidate, and nothing
              else says it has gone either - a protocol's methods are swept by
              the protocol that names them, and an intern answers to nobody"
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

(deftest a-method-a-protocol-stopped-naming-is-unmapped
  (let [a (written! "method/a.clj"
                    "(ns method.a)"
                    "(defprotocol P"
                    "  (kept [this])"
                    "  (dropped [this]))")]
    (analysed! a)
    (is (some? (ns-resolve 'method.a 'dropped)))
    (written! "method/a.clj"
              "(ns method.a)"
              "(defprotocol P"
              "  (kept [this]))")
    (is (= ["method/a.clj"] (an/stale-reload! :prune true)))
    (testing "a method var is interned and never def-ed, so no snapshot of the
              file's defs could have held it - what says it is gone is the
              protocol, which has just been re-def-ed without it"
      (is (nil? (ns-resolve 'method.a 'dropped))))
    (testing "and the method it still names is where it was, as is the protocol"
      (is (some? (ns-resolve 'method.a 'kept)))
      (is (some? (ns-resolve 'method.a 'P))))))

(deftest a-deleted-protocol-takes-its-methods-with-it
  (let [a (written! "whole/a.clj"
                    "(ns whole.a)"
                    "(def stays 1)"
                    "(defprotocol P"
                    "  (one [this])"
                    "  (two [this]))")]
    (analysed! a)
    (written! "whole/a.clj"
              "(ns whole.a)"
              "(def stays 1)")
    (an/stale-reload! :prune true)
    (testing "the protocol is an ordinary def and goes with the first sweep; its
              methods are nobody's def and go with it all the same"
      (is (nil? (ns-resolve 'whole.a 'P)))
      (is (nil? (ns-resolve 'whole.a 'one)))
      (is (nil? (ns-resolve 'whole.a 'two))))
    (is (some? (ns-resolve 'whole.a 'stays)))))

(deftest the-methods-of-another-protocol-are-not-swept
  (let [a (written! "twoproto/a.clj"
                    "(ns twoproto.a)"
                    "(defprotocol P"
                    "  (mine [this])"
                    "  (dropped [this]))"
                    "(defprotocol Q"
                    "  (theirs [this]))")]
    (analysed! a)
    (written! "twoproto/a.clj"
              "(ns twoproto.a)"
              "(defprotocol P"
              "  (mine [this]))"
              "(defprotocol Q"
              "  (theirs [this]))")
    (an/stale-reload! :prune true)
    (testing "the sweep is a protocol's own, told by the var its methods point
              at - not everything interned in the namespace that no def explains"
      (is (nil? (ns-resolve 'twoproto.a 'dropped)))
      (is (some? (ns-resolve 'twoproto.a 'mine)))
      (is (some? (ns-resolve 'twoproto.a 'theirs))))))

(deftest a-name-another-namespace-referred-is-unmapped-with-it
  (let [a (written! "referred/a.clj"
                    "(ns referred.a)"
                    "(defprotocol P"
                    "  (kept [this])"
                    "  (dropped [this]))"
                    "(def gone 1)"
                    "(def stays 2)")
        b (written! "referred/b.clj"
                    "(ns referred.b"
                    "  (:require [referred.a :refer [gone stays dropped]"
                    "                        :rename {gone elsewhere}]))")
        c (written! "referred/c.clj"
                    "(ns referred.c)"
                    "(def gone 3)"
                    "(def dropped 4)")]
    (analysed! a b c)
    (is (= (ns-resolve 'referred.a 'gone) (ns-resolve 'referred.b 'elsewhere)))
    (written! "referred/a.clj"
              "(ns referred.a)"
              "(defprotocol P"
              "  (kept [this]))"
              "(def stays 2)")
    (is (= ["referred/a.clj"] (an/stale-reload! :prune true)))
    (testing "a def and a protocol method both go from the namespace that
              defined them"
      (is (nil? (ns-resolve 'referred.a 'gone)))
      (is (nil? (ns-resolve 'referred.a 'dropped))))
    (testing "and from the namespace that referred them, under the name it
              referred them as - which is the name whose code has stopped being
              compilable, so it is the one that has to stop resolving"
      (is (nil? (ns-resolve 'referred.b 'elsewhere)))
      (is (nil? (ns-resolve 'referred.b 'dropped))))
    (testing "while what the file still defines is still referred"
      (is (= (ns-resolve 'referred.a 'stays) (ns-resolve 'referred.b 'stays)))
      (is (some? (ns-resolve 'referred.b 'stays))))
    (testing "and a namespace with vars of its own under the same names keeps
              them: the sweep goes by var identity, never by name"
      (is (some? (ns-resolve 'referred.c 'gone)))
      (is (some? (ns-resolve 'referred.c 'dropped))))))

(deftest pruning-a-protocol-method-that-is-still-called-warns-and-prunes-anyway
  (let [a (written! "warnproto/a.clj"
                    "(ns warnproto.a)"
                    "(defprotocol P"
                    "  (dropped [this]))")
        b (written! "warnproto/b.clj"
                    "(ns warnproto.b (:require [warnproto.a :as a]))"
                    "(defn call [x] (a/dropped x))")]
    (analysed! a b)
    (let [prior (an/file-def-var-snapshot (model) a)
          err   (java.io.StringWriter.)]
      (written! "warnproto/a.clj"
                "(ns warnproto.a)"
                "(defprotocol P)")
      (an/load-file! a)
      (testing "a method is answered among the pruned qsyms"
        (is (= '[warnproto.a/dropped]
               (binding [*err* err] (an/prune-file! a prior)))))
      (testing "and a call on it is warned about, as a def's would be"
        (is (re-find #"warnproto\.a/dropped" (str err)))
        (is (re-find #"warnproto\.b" (str err))))
      (is (nil? (ns-resolve 'warnproto.a 'dropped))))))

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

(deftest a-local-a-macro-binds-twice-is-used-where-either-is
  ;; `loop` destructures in a let outside the loop and again inside it, and only
  ;; the inner binding is read; a macro may do the same with a symbol it was given
  (let [a (written! "twice/a.clj"
                    "(ns twice.a)"
                    "(defn f [xs] (loop [[a & b] xs] (if a (recur b) 0)))"
                    "(defmacro wrap [sym val & body] `(let [~sym nil ~sym ~val] ~@body))"
                    "(defn g [] (wrap v 1 v))"
                    "(defn h [] (loop [[c d] [1 2]] c))")]
    (analysed! a)
    (is (= #{"d"} (set (map :name (an/unused-locals 'twice.a)))))))

(deftest a-protocol-implemented-is-a-protocol-used
  ;; a deftype, a defrecord or a reify names the protocol's interface by the time
  ;; the compiler sees it, and the source still wrote the alias and the refer
  (let [p (written! "impl/p.clj"
                    "(ns impl.p)"
                    "(defprotocol P (m [this]))"
                    "(defprotocol Q (q [this]))"
                    "(defprotocol R (r [this]))")
        a (written! "impl/a.clj"
                    "(ns impl.a (:require [impl.p :as p]))"
                    "(defrecord T [] p/P (m [_] 1))")
        b (written! "impl/b.clj"
                    "(ns impl.b (:require [impl.p :refer [Q R]]))"
                    "(defn f [] (reify Q (q [_] 1)))")]
    (analysed! p a b)
    (is (= {} (an/unused-aliases 'impl.a)))
    (is (= '[R] (keys (an/unused-refers 'impl.b))))))

(deftest a-const-is-used-where-it-is-written
  ;; compiled as its value, which is no reason to forget the source named it
  (let [a (written! "konst/a.clj"
                    "(ns konst.a)"
                    "(def ^:const k 42)"
                    "(def ^:private ^:const c 1)"
                    "(defn f [] (+ c 1))")
        b (written! "konst/b.clj"
                    "(ns konst.b (:require [konst.a :as a]))"
                    "(defn g [] a/k)")]
    (analysed! a b)
    (is (= 1 (count (an/find-usages 'konst.a/c))))
    (is (= 1 (count (an/find-usages 'konst.a/k))))
    (is (= {} (an/unused-aliases 'konst.b)))))

(deftest the-file-a-source-names
  (let [a (written! "onfile/a.clj"
                    "(ns onfile.a)"
                    "(def x 1)")]
    (analysed! a)
    (is (= (.getCanonicalFile (io/file @root a))
           (.getCanonicalFile (an/source->file a))))
    (is (nil? (an/source->file "onfile/nothing.clj")))))

;; --- code the program does not run: #_ and (comment ...) -------------------

(deftest dead-code-is-resolved-for-find-usages
  (let [_ (written! "dead/lib.clj"
                    "(ns dead.lib)"
                    "(defn helper [x] x)"
                    "(defmacro mac [x] x)")
        _ (written! "dead/a.clj"
                    "(ns dead.a (:require [dead.lib :as lib :refer [helper]]))"
                    "#_(lib/helper 1)"
                    "(defn f [helper] #_(helper 2) (lib/helper helper))"
                    "(comment"
                    "  (lib/helper 3)"
                    "  (let [helper 4] (helper))"
                    "  (lib/mac (later))"
                    "  (fn [{:keys [later]}] later)"
                    "  (java.util.ArrayList.)"
                    "  (defn ghost [] 1)"
                    "  undefined-thing"
                    "  (quote (later)))"
                    "(defn later [] 1)")]
    (analysed! "dead/a.clj")
    (testing "a use in a #_ and in a comment is found, marked as dead"
      (let [uses (remove :declaration (an/find-usages 'dead.lib/helper))]
        (is (= [[2 :discard] [3 nil] [5 :comment]]
               (sort-by first (map (juxt :line :dead) uses))))
        (is (every? #(= "lib/helper" (text-at %)) uses))
        (is (every? #(= 'dead.a (ns-name (:from-ns %))) uses))))
    (testing "and the :refer that names it is there too, dead code or not: it is
    what makes lib/helper mean that var and what a rename would have to rewrite"
      (let [decl (filter :declaration (an/find-usages 'dead.lib/helper))]
        (is (= [[1 :refer]] (map (juxt :line :declaration) decl)))
        (is (= "helper" (text-at (first decl))))
        (is (nil? (:dead (first decl))))))
    (testing "a macro in dead code is a macro use, and is not expanded"
      (is (= [[7 true :comment]]
             (map (juxt :line :macro :dead) (an/find-usages 'dead.lib/mac)))))
    (testing "resolved at the end of the file: a def after the comment is found"
      (is (= [7] (map :line (an/find-usages 'dead.a/later)))))
    (testing "a local is not a use: bound in the dead code, or in the live code around it"
      (is (not-any? #(and (:dead %) (#{3 6} (:line %))) (an/find-usages 'dead.lib/helper)))
      (is (not-any? #(#{8 12} (:line %)) (an/find-usages 'dead.a/later))))
    (testing "a class it names, the way the compiler records one"
      (let [uses (an/find-class-usages java.util.ArrayList)]
        (is (= [[9 :comment]] (map (juxt :line :dead) uses)))
        (is (= "java.util.ArrayList" (text-at (first uses))))))
    (testing "nothing in it is defined, nor recorded as a def"
      (is (nil? (an/definition 'dead.a/ghost)))
      (is (nil? (ns-resolve 'dead.a 'ghost))))))

(deftest dead-code-and-the-lints
  (let [_ (written! "deadl/lib.clj"
                    "(ns deadl.lib)"
                    "(defn one [] 1)")
        _ (written! "deadl/other.clj"
                    "(ns deadl.other)"
                    "(defn two [] 2)")
        _ (written! "deadl/a.clj"
                    "(ns deadl.a"
                    "  (:require [deadl.lib :as lib] [deadl.other :as other])"
                    "  (:import [java.util Date UUID]))"
                    "#_(other/two)"
                    "#_(Date.)"
                    "(comment (lib/one) (UUID/randomUUID))")]
    (analysed! "deadl/a.clj")
    (testing "a use in a comment keeps a require; one in a #_ does not"
      (is (= '{other deadl.other} (an/unused-aliases 'deadl.a)))
      (is (= {'Date java.util.Date} (an/unused-imports 'deadl.a))))))

(deftest dead-code-in-the-branch-not-taken-is-not-this-programs
  (let [_ (written! "deadr/a.cljc"
                    "(ns deadr.a)"
                    "(defn f [] 1)"
                    "#?(:cljs [#_(f)] :clj nil)"
                    "#?(:cljs (comment (f)))"
                    "#?(:clj [#_(f)])")]
    (an/run-analysis #(load "/deadr/a"))
    (is (= [[5 :discard]] (map (juxt :line :dead) (an/find-usages 'deadr.a/f))))))

(deftest dead-code-is-not-a-compile-time-dependency
  (let [_ (written! "deadg/lib.clj"
                    "(ns deadg.lib)"
                    "(defmacro m [] 1)"
                    "(defprotocol P (p [x]))")
        a (written! "deadg/a.clj"
                    "(ns deadg.a (:require [deadg.lib :as lib]))"
                    "(comment (lib/m) (deftype T [] lib/P (p [_] 1)) deadg.lib.P)")]
    (analysed! a)
    (is (seq (an/find-usages 'deadg.lib/m)))
    (is (empty? (get (class-graph) a)))
    (is (empty? (get (macro-graph) a)))
    (is (empty? (var-graph a "deadg/lib.clj")))))

(deftest a-syntax-quote-in-the-branch-not-taken-is-not-this-programs
  (let [_ (written! "sqr/a.cljc"
                    "(ns sqr.a)"
                    "(defn f [] 1)"
                    "(defmacro m [] #?(:cljs `(f) :clj `(f)))")]
    (an/run-analysis #(load "/sqr/a"))
    (testing "only the :clj branch's f - the :cljs one is read, and not recorded"
      (is (= [[3 37]] (map (juxt :line :column) (an/find-usages 'sqr.a/f)))))))

(deftest what-the-reader-reports-inside-dead-code-is-dead
  (let [_ (written! "deadq/lib.clj"
                    "(ns deadq.lib)"
                    "(defn g [] 1)")
        _ (written! "deadq/a.clj"
                    "(ns deadq.a (:require [deadq.lib :as lib]))"
                    "(defn f [] 1)"
                    "#_`(f)"
                    "#_ `f"
                    "(comment `(f) #_`(f))"
                    "#_::lib/k"
                    "(def live `f)")]
    (analysed! "deadq/a.clj")
    (testing "a syntax-quote in a #_ or a comment, whose form holds no position"
      (is (= [[3 nil :discard] [4 nil :discard] [5 12 :comment] [5 19 :discard] [7 nil nil]]
             (sort (map (juxt :line #(when (= 5 (:line %)) (:column %)) :dead)
                        (an/find-usages 'deadq.a/f))))))
    (testing "the comment call itself is live code"
      (is (= [nil] (map :dead (an/find-usages 'clojure.core/comment)))))
    (testing "a keyword in a #_ is dead too, and keeps no alias in use"
      (is (= [[6 :discard]] (map (juxt :line :dead)
                                 (an/find-keyword-usages :deadq.lib/k))))
      (is (= '{lib deadq.lib} (an/unused-aliases 'deadq.a))))))

;; --- what the compiler says it has defined ---------------------------------

(defn- defining!
  "Run `thunk` under `defining*` and answer the events it reported, in order."
  [thunk]
  (let [seen (atom [])]
    (an/defining* #(swap! seen conj %) thunk)
    @seen))

(defn- defines
  "The vars `events` say were defined, in order."
  [events]
  (mapv :var (filter #(= :define (:op %)) events)))

(deftest a-def-typed-at-a-prompt-is-reported
  (testing "the case no model can answer: there is no file, so nothing is
            analysed, and a var was defined all the same - which is what somebody
            fixing one function at a prompt does"
    (let [events (binding [*ns* (create-ns 'defd.prompt)]
                   ;; a namespace made by hand refers nothing, and what is being
                   ;; tested is a def and not what resolves in it
                   (refer-clojure)
                   (defining! #(eval '(do (def x 1) (defn f [] 2)))))]
      (try
        (is (= '[defd.prompt/x defd.prompt/f] (defines events)))
        (is (= [{:dialect :clj :op :define :ns 'defd.prompt}]
               (distinct (map #(dissoc % :var :source) events))))
        (testing "and the model is left alone, which is what it is for"
          (is (empty? (:forms (an/snapshot)))))
        (finally (remove-ns 'defd.prompt))))))

(deftest a-file-loaded-reports-every-var-it-defines
  (let [source (written! "defd/a.clj"
                         "(ns defd.a)"
                         "(def x 1)"
                         "(defn f [] 2)")
        events (defining! #(an/load-file! source))]
    (is (= '[defd.a/x defd.a/f] (defines events)))
    (is (= #{'defd.a} (set (map :ns events))))
    (is (= #{source} (set (map :source events))))
    (testing "and the model was filled as it always is: the sink load-file! installs
              is the one that stayed installed, so nothing was analysed twice and
              nothing was analysed less"
      (is (some? (an/definition 'defd.a/x))))))

(deftest a-require-typed-at-a-prompt-reports-without-analysing
  (let [source (written! "defdr/a.clj"
                         "(ns defdr.a)"
                         "(def x 1)")
        events (defining! #(eval '(require 'defdr.a)))]
    (is (= '[defdr.a/x] (defines events)))
    (testing "the sink installed for the reporting has no file and no form stack,
              so the model stays what it is - what was analysed, not the session"
      (is (empty? (:forms (an/snapshot))))
      (is (nil? (an/definition 'defdr.a/x))))
    (testing "and the file is still there to be analysed properly afterwards"
      (analysed! source)
      (is (some? (an/definition 'defdr.a/x))))))

(deftest one-binding-collects-a-whole-evaluation
  (let [_ (written! "defdc/lib.clj"
                    "(ns defdc.lib)"
                    "(def y 1)")
        _ (written! "defdc/a.clj"
                    "(ns defdc.a (:require defdc.lib))"
                    "(def x 1)")
        events (defining! #(an/load-file! "defdc/a.clj"))]
    (testing "a file loaded on the way in is inside the same evaluation and reports
              into the same place, which is what lets one binding round one form
              answer for everything that form turned out to load"
      (is (= '[defdc.lib/y defdc.a/x] (defines events))))))

(deftest nothing-is-reported-where-nothing-is-listening
  (let [source (written! "defdn/a.clj"
                         "(ns defdn.a)"
                         "(def x 1)")]
    (is (nil? an/*defined*) "and the default is to be listening nowhere")
    (testing "an analysis with nothing bound records what it always did"
      (analysed! source)
      (is (some? (an/definition 'defdn.a/x))))))

(deftest a-reload-says-what-it-took-away
  (let [source (written! "defdp/a.clj"
                         "(ns defdp.a)"
                         "(def x 1)"
                         "(def gone 2)")]
    (analysed! source)
    (written! "defdp/a.clj"
              "(ns defdp.a)"
              "(def x 1)")
    (let [events (defining! #(an/stale-reload! :prune true))]
      (testing "the def that is still written is defined again"
        (is (= '[defdp.a/x] (defines events))))
      (testing "and the one that is not is removed - a definition taken away by
                something nobody typed, which is the one a watcher cannot guess"
        (is (= [{:dialect :clj :op :remove :ns 'defdp.a :var 'defdp.a/gone}]
               (filterv #(= :remove (:op %)) events))))
      (testing "and it is said after it has gone, not before"
        (is (nil? (resolve 'defdp.a/gone)))))))

;; --- what a lint is made of ----------------------------------------------------

(deftest a-call-is-recorded-with-how-many-arguments-it-was-given
  (let [source (written! "calls/a.clj"
                         "(ns calls.a)"
                         "(defn f [x] x)"
                         "(defn g [y] (f 1 2) (-> y (f 3)) (map f [y]))")]
    (analysed! source)
    (let [calls (:invokes (an/file-facts source))]
      (testing "a call the source wrote, at the list it wrote, after macroexpansion -
      so the -> call has the argument the macro gave it"
        (is (= [['calls.a/f 2 3 13 "(f 1 2)"]
                ['calls.a/f 2 3 27 "(f 3)"]
                ['clojure.core/map 2 3 34 "(map f [y])"]]
               (mapv (juxt :var :argc :line :column text-at) calls))))
      (testing "and f passed to map is not a call of f"
        (is (= 3 (count calls)))))))

(deftest a-use-says-how-it-was-written
  (let [_ (written! "spelt/u.clj"
                    "(ns spelt.u)"
                    "(defn- secret [] 1)"
                    "(def ^:private ^:dynamic *p* 1)"
                    "(defn join [] 1)")
        source (written! "spelt/a.clj"
                         "(ns spelt.a (:require [spelt.u :as u :refer [join] :rename {join j}]))"
                         "(declare later)"
                         "(defn f [] (u/join) (j) #'u/secret (binding [u/*p* 2] (later)))"
                         "(defn later [] 1)")]
    (analysed! source)
    (let [{:keys [usages defs]} (an/file-facts source)
          uses (filterv #(and (= 3 (:line %)) (not (:macro %))) usages)]
      (testing "the spelling, where it is not the var's own name unqualified"
        (is (= [['spelt.u/join 'u/join] ['spelt.u/join 'j] ['spelt.u/secret 'u/secret]
                ['spelt.u/*p* 'u/*p*] ['spelt.a/later nil]]
               (mapv (juxt :var :written) (sort-by :column uses)))))
      (testing "a #' and a var-ized symbol are through the var special form"
        (is (= '#{spelt.u/secret spelt.u/*p*}
               (set (map :var (filter :var-form uses))))))
      (testing "a declare is a declaration, and the definition is not"
        (is (= [[2 :declare] [4 nil]]
               (mapv (juxt :line :declaration) (filter #(= 'spelt.a/later (:var %)) defs))))))))

(deftest an-ns-form-says-where-its-clauses-are-written
  (let [source (written! "specs/a.clj"
                         "(ns specs.a"
                         "  (:require [clojure.string :as str :refer [join]]"
                         "            (clojure [set :as set]))"
                         "  (:import [java.io File]))"
                         "(defn f [] (str/blank? \"\") (join []) (set/union) File)")]
    (analysed! source)
    (is (= [{:ns 'specs.a
             :requires [{:lib 'clojure.string :clause :require
                         :at {:line 2 :column 14 :end-line 2 :end-column 28}
                         :as 'str :as-at {:line 2 :column 33 :end-line 2 :end-column 36}
                         :refer [['join {:line 2 :column 45 :end-line 2 :end-column 49}]]}
                        {:lib 'clojure.set :clause :require
                         :at {:line 3 :column 23 :end-line 3 :end-column 26}
                         :as 'set :as-at {:line 3 :column 31 :end-line 3 :end-column 34}}]
             :imports [{:name 'File :class "java.io.File"
                        :at {:line 4 :column 21 :end-line 4 :end-column 25}}]}]
           (:ns-specs (an/file-facts source))))))

(deftest a-namespace-is-used-where-an-ns-form-requires-it
  (let [_ (written! "nsused/lib.clj"
                    "(ns nsused.lib)"
                    "(defn f [] 1)")
        a (written! "nsused/a.clj"
                    "(ns nsused.a (:require [nsused.lib :as l]))"
                    "(defn g [] (l/f) (nsused.lib/f))")
        b (written! "nsused/b.clj"
                    "(ns nsused.b"
                    "  (:require (nsused [lib]))"
                    "  (:use nsused.lib))")]
    (analysed! a b)
    (testing "each library an ns form writes, where it writes it, and nothing
    else: nsused.lib/f is a use of f"
      (is (= #{{:source a :line 1 :column 25 :end-line 1 :end-column 35
                :from-ns 'nsused.a :declaration :require}
               {:source b :line 2 :column 22 :end-line 2 :end-column 25
                :from-ns 'nsused.b :declaration :require}
               {:source b :line 3 :column 9 :end-line 3 :end-column 19
                :from-ns 'nsused.b :declaration :use}}
             (an/find-namespace-usages 'nsused.lib))))
    (testing "asked with the namespace itself too"
      (is (= (an/find-namespace-usages 'nsused.lib)
             (an/find-namespace-usages (the-ns 'nsused.lib)))))))

(deftest a-call-of-require-is-a-use-of-the-namespace-it-loads
  (let [_ (written! "reqcall/lib.clj"
                    "(ns reqcall.lib)"
                    "(defn f [] 1)")
        source (written! "reqcall/a.clj"
                         "(ns reqcall.a (:require [clojure.string]))"
                         "(require '[reqcall.lib :as l])"
                         "(defn lazy [] (require 'reqcall.lib) (use '(reqcall [lib])))"
                         "(defn computed [s] (require (symbol s)) (requiring-resolve 'reqcall.lib/f))"
                         "(comment (require '[reqcall.lib :as l2]) (l/f) (requiring-resolve 'reqcall.lib/f))"
                         "#_(use 'reqcall.lib)")]
    (analysed! source)
    (testing "at the top level and in a function body, each marked as a call and
    by the function called; the computed one names nothing, and a
    requiring-resolve is placed at the namespace part of the name it writes"
      (is (= [[2 12 23 :require nil] [3 25 36 :require nil] [3 54 57 :use nil]
              [4 61 72 :requiring-resolve nil]
              [5 21 32 :require :comment] [5 68 79 :requiring-resolve :comment]
              [6 9 20 :use :discard]]
             (sort (map (juxt :line :column :end-column :declaration :dead)
                        (an/find-namespace-usages 'reqcall.lib)))))
      (is (every? :call (an/find-namespace-usages 'reqcall.lib))))
    (testing "and requiring-resolve is a use of the var it names, all of the name,
    spelled as it is written"
      (is (= [[4 61 74 :requiring-resolve nil 'reqcall.lib/f]
              [5 68 81 :requiring-resolve :comment 'reqcall.lib/f]]
             (sort-by first
                      (map (juxt :line :column :end-column :role :dead :written)
                           (filter #(and (= source (:source %)) (:role %))
                                   (an/find-usages 'reqcall.lib/f)))))))
    (testing "the ns form's own requires are reported once, as the ns form's:
    what it expands into is not the source calling require"
      (is (= [[1 26 nil]]
             (->> (an/find-namespace-usages 'clojure.string)
                  (filter #(= source (:source %)))
                  (map (juxt :line :column :call))))))
    (testing "and kept apart from the ns form's clauses"
      (is (= ['clojure.string] (map :lib (mapcat :requires (:ns-specs (an/file-facts source))))))
      (is (= [['reqcall.lib :require] ['reqcall.lib :require] ['reqcall.lib :use]
              ['reqcall.lib :requiring-resolve]
              ['reqcall.lib :require] ['reqcall.lib :requiring-resolve] ['reqcall.lib :use]]
             (map (juxt :lib :clause)
                  (mapcat :requires (:require-calls (an/file-facts source))))))
      (testing "the one call that is its whole top-level form says so"
        (is (= [[2 true]]
               (for [c (:require-calls (an/file-facts source)) :when (:top-level c)]
                 [(:line (:at (first (:requires c)))) true])))))))

(deftest a-defmethod-is-a-use-of-its-multimethod
  (let [source (written! "multi/a.clj"
                         "(ns multi.a)"
                         "(defmulti area :shape)"
                         "(defmethod area :square [{:keys [side]}] (* side side))"
                         "(defn total [xs] (map area xs))"
                         "(comment (defmethod area :circle [_] 0))")]
    (analysed! source)
    (is (= [[3 12 :defmethod nil] [4 23 nil nil] [5 21 :defmethod :comment]]
           (sort (map (juxt :line :column :role :dead) (an/find-usages 'multi.a/area)))))))

(deftest a-keys-destructuring-is-a-use-of-the-keywords-it-binds
  (let [source (written! "destr/a.clj"
                         "(ns destr.a (:require [clojure.string :as s]))"
                         "(defn f [{:keys [id s/other] ::keys [mine] :destr.b/keys [theirs] :strs [nope]}]"
                         "  [id other mine theirs nope])"
                         "(let [{:keys [:written]} {}] written)")]
    (analysed! source)
    (let [at (fn [kw] (sort (map (juxt :line :column :end-column :role)
                                 (filter #(= source (:source %)) (an/find-keyword-usages kw)))))]
      (testing "a symbol of a :keys is the keyword, where the local is written -
      s/other is :s/other, as destructuring reads it, and not an alias"
        (is (= [[2 18 20 :destructuring]] (at :id)))
        (is (= [[2 21 28 :destructuring]] (at :s/other))))
      (testing "::keys and :ns/keys give it their namespace"
        (is (= [[2 38 42 :destructuring]] (at :destr.a/mine)))
        (is (= [[2 59 65 :destructuring]] (at :destr.b/theirs))))
      (testing "a keyword written as one is read as one, once"
        (is (= [[4 15 23 nil]] (at :written))))
      (testing ":strs names strings, not keywords"
        (is (empty? (at :nope)))))))

(deftest a-local-is-found-from-any-place-it-is-written
  (let [source (written! "loc/a.clj"
                         "(ns loc.a)"
                         "(defn f [x y]"
                         "  (let [x (inc x)]"
                         "    (+ x y)))")]
    (analysed! source)
    (let [places (fn [line column]
                   (sort (map (juxt :line :column :declaration)
                              (an/find-local-usages source line column))))]
      (testing "the parameter x, from its binding and from its use"
        (is (= [[2 10 :binding] [3 16 nil]] (places 2 10)))
        (is (= [[2 10 :binding] [3 16 nil]] (places 3 17))))
      (testing "the let's x shadows it"
        (is (= [[3 9 :binding] [4 8 nil]] (places 4 8))))
      (testing "and nowhere a local is written, nothing"
        (is (nil? (an/find-local-usages source 1 1)))))))

(deftest a-java-member-is-used-where-the-compiler-resolved-it
  (let [source (written! "member/a.clj"
                         "(ns member.a (:import [java.util ArrayList]))"
                         "(defn f [^String s ^ArrayList l]"
                         "  [(.length s) (. s length) (String/valueOf 1) String/.trim"
                         "   (.size l) Integer/MAX_VALUE (ArrayList. 3) (.-x (java.awt.Point.))])")]
    (binding [*err* (java.io.StringWriter.)]
      (analysed! source))
    (let [at (fn [c m] (sort (map (juxt :line :column :end-column)
                                  (filter #(= source (:source %)) (an/find-member-usages c m)))))]
      (testing "a method, whichever way it is written, at its name"
        (is (= [[3 6 12] [3 21 27]] (at String "length")))
        (is (= [[3 37 44]] (at "java.lang.String" "valueOf"))))
      (testing "a method value is each method of that name"
        (is (= [[3 56 60]] (at String "trim"))))
      (testing "by the class declaring it"
        (is (= [[4 6 10]] (at java.util.ArrayList "size"))))
      (testing "a field, a constructor"
        (is (= [[4 22 31]] (at Integer "MAX_VALUE")))
        (is (= [[4 33 42]] (at java.util.ArrayList "new")))
        (is (= [[4 50 51]] (at java.awt.Point "x")))
        (is (= [[4 53 67]] (at java.awt.Point "new")))))))

(deftest what-the-compiler-warned-about-is-a-fact-of-the-form
  (let [source (written! "warned/a.clj"
                         "(ns warned.a)"
                         "(set! *warn-on-reflection* true)"
                         "(defn f [x] (.length x))"
                         "(def *earmuffed* 1)")]
    (binding [*err* (java.io.StringWriter.)]
      (analysed! source))
    (is (= [[:reflection 3 13 "reference to field length can't be resolved."]
            [:earmuffed-var-not-dynamic 4 6 "*earmuffed*"]]
           (mapv (juxt :kind :line :column :message) (:warnings (an/file-facts source)))))
    (testing "and goes with the form: the file loaded again without it has none"
      (written! "warned/a.clj"
                "(ns warned.a)"
                "(set! *warn-on-reflection* true)"
                "(defn f [^String x] (.length x))")
      (binding [*err* (java.io.StringWriter.)]
        (an/load-file! source))
      (is (= [] (:warnings (an/file-facts source)))))))

(deftest a-file-that-fails-says-where-and-why-until-it-loads
  (let [source (written! "failed/a.clj"
                         "(ns failed.a)"
                         "(def ok 1)")]
    (analysed! source)
    (is (nil? (an/file-failure source)))
    (written! "failed/a.clj"
              "(ns failed.a)"
              "(def ok 1)"
              "(defn f [] (nope 1))")
    (is (thrown? Exception (an/load-file! source)))
    (let [failure (an/file-failure source)]
      (is (= [3 12] [(:line failure) (:column failure)]))
      (is (str/starts-with? (:message failure) "Unable to resolve symbol: nope"))
      (testing "about the version on disk that failed"
        (is (= (.lastModified (io/file @root source)) (:mtime failure))))
      (testing "and not the version the model is about, which is the one before"
        (is (not= (:mtime failure) (an/file-mtime source)))))
    (written! "failed/a.clj" "(ns failed.a)" "(def ok 2)")
    (an/load-file! source)
    (is (nil? (an/file-failure source)))))

(deftest the-model-says-when-it-has-changed
  (let [before (an/version)
        source (written! "versioned/a.clj" "(ns versioned.a)" "(def x 1)")]
    (is (identical? before (an/version)))
    (analysed! source)
    (is (not (identical? before (an/version))))))
