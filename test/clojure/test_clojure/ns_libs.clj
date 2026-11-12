;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

; Authors: Frantisek Sodomka, Stuart Halloway

(ns clojure.test-clojure.ns-libs
  (:use clojure.test))

; http://clojure.org/namespaces

; in-ns ns create-ns
; alias import intern refer
; all-ns find-ns
; ns-name ns-aliases ns-imports ns-interns ns-map ns-publics ns-refers
; resolve ns-resolve namespace
; ns-unalias ns-unmap remove-ns


; http://clojure.org/libs

; require use
; loaded-libs

(deftest test-alias
	(is (thrown-with-msg? Exception #"No namespace: epicfail found" (alias 'bogus 'epicfail))))
	
(deftest test-require
         (is (thrown? Exception (require :foo)))
         (is (thrown? Exception (require))))

(deftest test-use
         (is (thrown? Exception (use :foo)))
         (is (thrown? Exception (use))))

(deftest reimporting-deftypes
  (let [inst1 (binding [*ns* *ns*]
                (eval '(do (ns exporter)
                           (defrecord ReimportMe [a])
                           (ns importer)
                           (import exporter.ReimportMe)
                           (ReimportMe. 1))))
        inst2 (binding [*ns* *ns*]
                (eval '(do (ns exporter)
                           (defrecord ReimportMe [a b])
                           (ns importer)
                           (import exporter.ReimportMe)
                           (ReimportMe. 1 2))))]
    (testing "you can reimport a changed class and see the changes"
      (is (= [:a] (keys inst1)))
      (is (= [:a :b] (keys inst2))))
    ;fragile tests, please fix
    #_(testing "you cannot import same local name from a different namespace"
      (is (thrown? clojure.lang.Compiler$CompilerException
                  #"ReimportMe already refers to: class exporter.ReimportMe in namespace: importer"
                  (binding [*ns* *ns*]
                    (eval '(do (ns exporter-2)
                               (defrecord ReimportMe [a b])
                               (ns importer)
                               (import exporter-2.ReimportMe)
                               (ReimportMe. 1 2)))))))))

(deftest naming-types
  (testing "you cannot use a name already referred from another namespace"
    (is (thrown-with-msg? IllegalStateException
                          #"String already refers to: class java.lang.String"
                          (definterface String)))
    (is (thrown-with-msg? IllegalStateException
                          #"StringBuffer already refers to: class java.lang.StringBuffer"
                          (deftype StringBuffer [])))
    (is (thrown-with-msg? IllegalStateException
                          #"Integer already refers to: class java.lang.Integer"
                          (defrecord Integer [])))))

(deftest resolution
  (let [s (gensym)]
    (are [result expr] (= result expr)
         #'clojure.core/first (ns-resolve 'clojure.core 'first)
         nil (ns-resolve 'clojure.core s)
         nil (ns-resolve 'clojure.core {'first :local-first} 'first)
         nil (ns-resolve 'clojure.core {'first :local-first} s))))
  
(deftest refer-error-messages
  (let [temp-ns (gensym)]
    (binding [*ns* *ns*]
      (in-ns temp-ns)
      (eval '(def ^{:private true} hidden-var)))
    (testing "referring to something that does not exist"
      (is (thrown-with-msg? IllegalAccessError #"nonexistent-var does not exist"
            (refer temp-ns :only '(nonexistent-var)))))
    (testing "referring to something non-public"
      (is (thrown-with-msg? IllegalAccessError #"hidden-var is not public"
            (refer temp-ns :only '(hidden-var)))))))

(deftest test-defrecord-deftype-err-msg
  (is (thrown-with-cause-msg? clojure.lang.Compiler$CompilerException
                        #"defrecord and deftype fields must be symbols, user\.MyRecord had: :shutdown-fn"
                        (eval '(defrecord MyRecord [:shutdown-fn]))))
  (is (thrown-with-cause-msg? clojure.lang.Compiler$CompilerException
                        #"defrecord and deftype fields must be symbols, user\.MyType had: :key1"
                        (eval '(deftype MyType [:key1])))))

(deftest require-as-alias
  ;; :as-alias does not load
  (require '[not.a.real.ns [foo :as-alias foo]
                           [bar :as-alias bar]])
  (let [aliases (ns-aliases *ns*)
        foo-ns (get aliases 'foo)
        bar-ns (get aliases 'bar)]
    (is (= 'not.a.real.ns.foo (ns-name foo-ns)))
    (is (= 'not.a.real.ns.bar (ns-name bar-ns))))

  (is (= :not.a.real.ns.foo/baz (read-string "::foo/baz")))

  ;; can use :as-alias in use, but load will occur
  (use '[clojure.walk :as-alias e1])
  (is (= 'clojure.walk (ns-name (get (ns-aliases *ns*) 'e1))))
  (is (= :clojure.walk/walk (read-string "::e1/walk")))

  ;; can use both :as and :as-alias
  (require '[clojure.set :as n1 :as-alias n2])
  (let [aliases (ns-aliases *ns*)]
    (is (= 'clojure.set (ns-name (get aliases 'n1))))
    (is (= 'clojure.set (ns-name (get aliases 'n2))))
    (is (= (resolve 'n1/union) #'clojure.set/union))
    (is (= (resolve 'n2/union) #'clojure.set/union))))

(deftest require-as-alias-then-load-later
  ;; alias but don't load
  (require '[clojure.test-clojure.ns-libs-load-later :as-alias alias-now])
  (is (contains? (ns-aliases *ns*) 'alias-now))
  (is (not (nil? (find-ns 'clojure.test-clojure.ns-libs-load-later))))

  ;; not loaded!
  (is (nil? (resolve 'alias-now/example)))

  ;; load
  (require 'clojure.test-clojure.ns-libs-load-later)

  ;; now loaded!
  (is (not (nil? (resolve 'alias-now/example)))))
;; Macro calls are checked against clojure.core.specs where the source is somebody's to
;; fix, and not in a file read out of a jar - see RT.LOADING_JAR_ENTRY. (require x),
;; a symbol where :require belongs, is the call to check with: the ns macro accepts it
;; and the spec does not, which is what broke libraries on 1.9.

(defn- spec-refused? [thunk]
  (try (thunk) false
       (catch Throwable t
         (boolean (some #(re-find #"did not conform to spec" (str (.getMessage ^Throwable %)))
                        (take-while some? (iterate #(.getCause ^Throwable %) t)))))))

(defn- write-jar [^java.io.File jar entries]
  (with-open [out (java.util.jar.JarOutputStream. (java.io.FileOutputStream. jar))]
    (doseq [[path text] entries]
      (.putNextEntry out (java.util.jar.JarEntry. ^String path))
      (.write out (.getBytes ^String text "UTF-8"))
      (.closeEntry out))))

(deftest macro-specs-are-not-checked-in-a-jar
  (let [dir (.toFile (java.nio.file.Files/createTempDirectory
                      "jar-specs" (make-array java.nio.file.attribute.FileAttribute 0)))
        src (java.io.File. dir "src")
        jar (java.io.File. dir "lib.jar")
        bad (fn [ns] (str "(ns " ns " (require clojure.string))\n(def ok true)\n"))
        on-disk (java.io.File. src "jarspec/on_disk.clj")]
    (.mkdirs (.getParentFile on-disk))
    (spit on-disk (bad "jarspec.on-disk"))
    (write-jar jar {"jarspec/in_jar.clj" (bad "jarspec.in-jar")
                    "jarspec/jar_requires_disk.clj"
                    "(ns jarspec.jar-requires-disk (:require jarspec.on-disk))"})
    (let [cl (doto (clojure.lang.DynamicClassLoader. (clojure.lang.RT/baseLoader))
               (.addURL (.toURL (.toURI jar)))
               (.addURL (.toURL (.toURI src))))]
      (with-bindings {clojure.lang.Compiler/LOADER cl}
        (testing "a file out of a jar loads, its macro calls being its author's"
          (require 'jarspec.in-jar)
          (is (true? @(resolve 'jarspec.in-jar/ok))))
        (testing "a file on disk is checked"
          (is (spec-refused? #(require 'jarspec.on-disk))))
        (testing "and so is one a jar's file requires: each load answers for itself"
          (is (spec-refused? #(require 'jarspec.jar-requires-disk))))
        (testing "and a file loaded by its path"
          (is (spec-refused? #(load-file (str on-disk)))))))))
