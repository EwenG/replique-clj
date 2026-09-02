;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "AST -> JavaScript, destination-driven.

  Clojure's `if` is an expression; JavaScript's is a statement. ClojureScript
  resolves that by threading a :context (:expr / :statement / :return) through the
  analyzer and wrapping in an immediately-invoked function whenever an expression
  position needs statements - so (let* [x 1] (if x 1 2)) compiles to

      (function (){var x = (1);
      if(cljs.core.truth_(x)){ return (1); } else { return (2); }
      })()

  We do it the other way round. emit returns TWO things:

      {:stmts [\"...\" ...]   statements that must run first
       :expr  \"...\"}        a JavaScript expression holding the value

  A node emits its children, concatenates their :stmts before its own, and hands
  back an expression. Statements bubble up to the nearest enclosing statement
  position instead of being trapped behind a function boundary, so the same form
  is:

      let x__1 = 1;
      let t__2;
      if (truth_(x__1)) { t__2 = 1; } else { t__2 = 2; }
      // value: t__2

  This is destination-driven code generation. It costs a two-part return value and
  buys back the whole :context mechanism: statement-versus-return is decided once,
  per statement, by whoever consumes the result - not carried through every node.
  It matters more here than in ClojureScript, which leans on :advanced to clean the
  wrappers up afterwards; :optimizations :none is the only output we produce.

  Two consequences to keep in mind. Nested scopes flatten into one JavaScript
  scope, which is why the analyzer makes every local name unique. And an :if whose
  branches need no statements still emits a ternary - the temporary appears only
  when it is actually needed."}
  clojure.cljs.emitter
  (:refer-clojure :exclude [munge]))

;; --- names ------------------------------------------------------------------

(def js-reserved
  "Reserved in JavaScript, so never usable as an emitted name. Separate from
  Compiler.munge's list, which guards against Java keywords (doc/cljs-compiler.md
  §5): the two targets forbid different words and must not share an implementation."
  #{"abstract" "arguments" "await" "boolean" "break" "byte" "case" "catch" "char"
    "class" "const" "continue" "debugger" "default" "delete" "do" "double" "else"
    "enum" "eval" "export" "extends" "false" "final" "finally" "float" "for"
    "function" "goto" "if" "implements" "import" "in" "instanceof" "int"
    "interface" "let" "long" "native" "new" "null" "package" "private"
    "protected" "public" "return" "short" "static" "super" "switch"
    "synchronized" "this" "throw" "throws" "transient" "true" "try" "typeof"
    "var" "void" "volatile" "while" "with" "yield"})

(def char-map
  "cljs.compiler's mapping, so a name munges to what ClojureScript would produce."
  {\- "_" \: "_COLON_" \+ "_PLUS_" \> "_GT_" \< "_LT_" \= "_EQ_" \~ "_TILDE_"
   \! "_BANG_" \@ "_CIRCA_" \# "_SHARP_" \' "_SINGLEQUOTE_" \" "_DOUBLEQUOTE_"
   \% "_PERCENT_" \^ "_CARET_" \& "_AMPERSAND_" \* "_STAR_" \| "_BAR_"
   \{ "_LBRACE_" \} "_RBRACE_" \[ "_LBRACK_" \] "_RBRACK_" \/ "_SLASH_"
   \\ "_BSLASH_" \? "_QMARK_"})

(defn munge
  "A legal JavaScript identifier for `sym`."
  [sym]
  (let [s (apply str (map #(get char-map % %) (str sym)))]
    (if (js-reserved s) (str s "$") s)))

;; --- the destination-driven result ------------------------------------------

(defn- ->result [stmts expr] {:stmts (vec stmts) :expr expr})

(def ^:dynamic *temp-counter* nil)

(defn- temp []
  (str "t__" (swap! *temp-counter* inc)))

(def truth-helper
  "ClojureScript truthiness is not JavaScript's: 0 and \"\" are true, only nil and
  false are false. The one runtime function this seed needs."
  "function truth_(x) { return x !== null && x !== undefined && x !== false; }")

;; --- literals ---------------------------------------------------------------

(defn- emit-const [{:keys [val]}]
  (->result []
            (cond
              (nil? val)     "null"
              (string? val)  (pr-str val)
              (keyword? val) (pr-str (str val))   ; a placeholder until cljs.core
              :else          (pr-str val))))

;; --- emit -------------------------------------------------------------------

(declare emit)

(defn- emit-do [{:keys [statements ret]}]
  (let [stmts (into [] (mapcat (fn [n]
                                 (let [{:keys [stmts expr]} (emit n)]
                                   (conj stmts (str expr ";")))))
                    statements)
        r     (emit ret)]
    (->result (into stmts (:stmts r)) (:expr r))))

(defn- emit-let [{:keys [bindings body]}]
  (let [stmts (into [] (mapcat (fn [{:keys [js-name init]}]
                                 (let [{:keys [stmts expr]} (emit init)]
                                   (conj stmts (str "let " (munge js-name) " = " expr ";")))))
                    bindings)
        r     (emit body)]
    ;; No wrapper: a let's value is its body's value, and the bindings are just
    ;; statements that have to run first.
    (->result (into stmts (:stmts r)) (:expr r))))

(defn- emit-if [{:keys [test then else]}]
  (let [t  (emit test)
        th (emit then)
        el (emit else)
        cond-expr (str "truth_(" (:expr t) ")")]
    (if (and (empty? (:stmts th)) (empty? (:stmts el)))
      ;; both branches are pure expressions - no temporary needed
      (->result (:stmts t) (str "(" cond-expr " ? " (:expr th) " : " (:expr el) ")"))
      (let [v (temp)]
        (->result
         (-> (vec (:stmts t))
             (conj (str "let " v ";"))
             (conj (str "if (" cond-expr ") {"))
             (into (map #(str "  " %)) (conj (vec (:stmts th)) (str v " = " (:expr th) ";")))
             (conj "} else {")
             (into (map #(str "  " %)) (conj (vec (:stmts el)) (str v " = " (:expr el) ";")))
             (conj "}"))
         v)))))

(defn- indent [lines] (mapv #(str "  " %) lines))

(defn- emit-body
  "A function body: its statements, then `return <expr>;`. This is the other
  destination besides an expression - and, with emit-top, the only other one."
  [node]
  (let [{:keys [stmts expr]} (emit node)]
    (conj (vec stmts) (str "return " expr ";"))))

(defn- bind-params
  "Statements binding a method's parameters out of `arguments`, used when several
  arities share one JavaScript function. `from` is the first index to take."
  [params from]
  (into []
        (map-indexed (fn [i {:keys [js-name]}]
                       (str "let " (munge js-name) " = arguments[" (+ from i) "];")))
        (subvec (vec params) from)))

(defn- rest-param
  "The variadic parameter, bound to the arguments past the fixed ones.

  A plain JavaScript array, which is NOT what ClojureScript's rest arguments are -
  there they are a seq, built by cljs.core/array-seq. Provisional until M5 brings
  the core library; everything else about variadic dispatch is real."
  [{:keys [js-name]} fixed-arity]
  (str "let " (munge js-name) " = Array.prototype.slice.call(arguments, "
       fixed-arity ");"))

(defn- emit-method-lines
  "The body of one arity, with its parameters already in scope. `param-from` is
  the first parameter to pull out of `arguments` rather than take as a formal."
  [{:keys [params fixed-arity variadic?] :as method} param-from]
  (cond-> (bind-params (cond-> params variadic? pop) param-from)
    variadic? (conj (rest-param (peek params) fixed-arity))
    true      (into (emit-body (:body method)))))

(defn- emit-fn [{:keys [methods variadic? local]}]
  (let [nm (if local (str " " (munge (:js-name local))) "")]
    (->result
     []
     (if (= 1 (count methods))
       ;; one arity: the parameters are real formals, so the function reads as one
       (let [{:keys [params variadic?]} (first methods)
             formals (cond-> params variadic? pop)]
         (str "(function" nm "(" (clojure.string/join ", " (map #(munge (:js-name %)) formals)) ") {\n"
              (clojure.string/join "\n" (indent (emit-method-lines (first methods) (count formals))))
              "\n})"))
       ;; several arities dispatch on arguments.length; every parameter comes out
       ;; of `arguments`, so the arities cannot disagree about formals
       (let [fixed (remove :variadic? methods)
             var-m (first (filter :variadic? methods))]
         (str "(function" nm "() {\n"
              (clojure.string/join
               "\n"
               (indent
                (-> ["switch (arguments.length) {"]
                    (into (mapcat (fn [m]
                                    (-> [(str "case " (:fixed-arity m) ": {")]
                                        (into (indent (emit-method-lines m 0)))
                                        (conj "}"))))
                          fixed)
                    (into (when var-m
                            (-> [(str "default: if (arguments.length >= " (:fixed-arity var-m) ") {")]
                                (into (indent (emit-method-lines var-m 0)))
                                (conj "}"))))
                    (conj "}")
                    (conj (str "throw new Error(\"Invalid arity: \" + arguments.length);")))))
              "\n})"))))))

(defn- emit-invoke [{:keys [args] :as node}]
  (let [f  (emit (:fn node))
        as (map emit args)]
    (->result (into (vec (:stmts f)) (mapcat :stmts) as)
              (str (:expr f) "(" (clojure.string/join ", " (map :expr as)) ")"))))

(defn- emit-js [{:keys [segs args]}]
  (let [rs (map emit args)]
    (->result (into [] (mapcat :stmts) rs)
              (apply str (interleave segs (concat (map :expr rs) (repeat "")))))))

(defn emit
  "JavaScript for `node`, as {:stmts [...] :expr \"...\"}."
  [node]
  (case (:op node)
    :const (emit-const node)
    :local (->result [] (munge (:js-name node)))
    :do    (emit-do node)
    :let   (emit-let node)
    :if    (emit-if node)
    :js    (emit-js node)
    :fn    (emit-fn node)
    :invoke (emit-invoke node)
    (throw (ex-info (str "No emitter for :op " (:op node)) {:node node}))))

;; --- consuming a result ------------------------------------------------------

(defn emit-top
  "Emit `node` as a top-level unit: the statements it needs, then `f` applied to
  its value expression. `f` is what makes this a statement, a return, or a
  console.log - the one place the statement/expression distinction is decided."
  ([node] (emit-top node #(str % ";")))
  ([node f]
   (binding [*temp-counter* (atom 0)]
     (let [{:keys [stmts expr]} (emit node)]
       (clojure.string/join "\n" (conj (vec stmts) (f expr)))))))
