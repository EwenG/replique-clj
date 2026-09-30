/**
 *   Copyright (c) Rich Hickey. All rights reserved.
 *   The use and distribution terms for this software are covered by the
 *   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
 *   which can be found in the file epl-v10.html at the root of this distribution.
 *   By using this software in any fashion, you are agreeing to be bound by
 * 	 the terms of this license.
 *   You must not remove this notice, or any other, from this software.
 **/

package clojure.lang;

/**
 * Sink for the semantic events the compiler emits during analysis. It is
 * installed by binding {@link Compiler#ANALYSIS_SINK} to a non-null
 * implementation; when the var is unbound (the default), the compiler pays only
 * a null check per potential event and emits nothing, so normal compilation,
 * AOT and REPL use are unaffected.
 *
 * See doc/analysis-and-reload.md for the full design.
 */
public interface IAnalysisSink{

/**
 * Marks the start of loading one source file (design §7.3). Compiler.load is
 * re-entrant - a require/load triggered while evaluating a form calls it again -
 * so these calls nest, and the nesting is exactly the file load stack: every
 * {@link #beginForm} until the matching {@link #endFile} belongs to this file.
 * {@link #endFile} is issued only when the file loads to completion; if loading
 * throws (a compile error), no {@code endFile} fires for that file, so the sink
 * can commit the files that fully loaded and discard the one that did not -
 * matching what the compiler actually left defined. {@code source} is the
 * classpath-relative path the form events also carry.
 */
void beginFile(String source);

/** Marks the successful end of loading the file opened by the matching {@link
 * #beginFile}. Not called if the file's load threw. */
void endFile(String source);

/**
 * Marks the start of analysis of one top-level form (design §7.3). All events
 * emitted until the matching {@link #endForm} belong to this form and are
 * filed under it for retract-and-replace. Calls nest (a top-level {@code (do
 * ...)} evals its children as separate forms); the innermost active form owns
 * the events.
 */
void beginForm(String source, int line, int column);

/**
 * Reports the true start position of the current top-level form, issued by the
 * reader once it commits to the datum - i.e. after skipping any leading
 * whitespace, {@code ;} comment, {@code #_} discard or non-selected
 * reader-conditional branch. {@link #beginForm} opens the form at a pre-scan
 * guess (so read-time events have somewhere to land); this corrects that guess
 * to the form itself, so position-keyed retraction matches on re-eval. May be
 * called more than once while a form is open (once per skipped no-op); the last
 * call - the datum actually returned - wins.
 */
void formStart(int line, int column);

/** Marks the end of the current top-level form (see {@link #beginForm}). */
void endForm();

/**
 * A var reference resolved during analysis. {@code target} is the referenced
 * var, {@code fromNs} the namespace being compiled where the reference occurs.
 * When the reference symbol carries reader positions (Layer 1), the span is
 * precise: {@code line}/{@code column} at the symbol and {@code endLine}/
 * {@code endColumn} just past it. When it does not, positions fall back to the
 * enclosing form's line/column and {@code endLine}/{@code endColumn} are -1.
 *
 * {@code line} -1 says something else again: that the reference is real and is
 * NOWHERE. Being referenced and being written somewhere are two different facts,
 * and a macro destroys the second without touching the first - by rebuilding the
 * body it was given (a {@code go} block) or by replacing a form's metadata
 * ({@code with-meta}, as {@code vswap!} and {@code io.pedestal.log/error} do).
 * The unused-* questions want the first, so it is reported. A sink must keep
 * these out of everything that answers WHERE - find-usages, a rename, a lint's
 * span - and can read {@code written} to tell a spelling this namespace's own
 * {@code ns} form is holding up ({@code str/join}, a bare {@code join}) from one
 * that needs nothing of it ({@code clojure.string/join}, which is what
 * macroexpansion produces).
 *
 * {@code written} is the symbol the source wrote - {@code str/join}, a referred
 * {@code join}, a renamed one - with its reader metadata. It is the one thing
 * about the reference the resolved var no longer says: the alias it went
 * through, and the name it was spelled by.
 *
 * {@code varForm} is true for a reference through the {@code var} special form:
 * a {@code #'name}, or a symbol a macro var-ized ({@code binding} does). It names
 * the var rather than taking its value, which is what makes it legal of a private
 * var of another namespace, and the compiler says so nowhere else.
 */
void varUsage(Var target, Symbol written, boolean varForm, Namespace fromNs, String source,
              int line, int column, int endLine, int endColumn);

/**
 * A var defined by a top-level def form. The defining namespace is
 * {@code var.ns}. Positions follow the same convention as {@link #varUsage}.
 *
 * {@code declared} is true for a def that only declares the name - what {@code
 * declare} expands to, a {@code def} of a name marked {@code :declared}. The
 * mark is on the def's symbol, and gone from the var the moment the definition
 * that follows replaces its metadata, so this is the one moment it can be told.
 */
void varDef(Var var, boolean declared, String source,
            int line, int column, int endLine, int endColumn);

/**
 * A local binding (let/loop/fn param, incl. destructuring) written in source.
 * {@code binding} is an opaque identity token linking this definition to its
 * usages; {@code name} is the binding symbol's name. Only source-written
 * bindings are reported - macro-introduced (gensym) locals carry no reader
 * position and are skipped.
 */
void localDef(Object binding, String name, Namespace ns, String source,
              int line, int column, int endLine, int endColumn);

/**
 * A reference to a local binding, keyed by the same {@code binding} identity
 * token as its {@link #localDef}.
 *
 * {@code line} -1 for a reference that is nowhere, {@link #varUsage}'s meaning
 * and for its reason: the binding is read, and the symbol that reads it carries
 * no position, so no place in the file is its. Whether a binding is read is what
 * unused-binding asks, and it is answerable without a place.
 */
void localUsage(Object binding, Namespace ns, String source,
                int line, int column, int endLine, int endColumn);

/**
 * A keyword occurrence read from source. Keywords have no definition and
 * cannot carry metadata, so the reader emits usages directly. {@code kw} is
 * already fully resolved (auto-resolved {@code ::x}/{@code ::alias/x} arrive
 * namespace-qualified), so occurrences are indexed by identity.
 */
void keywordUsage(Keyword kw, Namespace fromNs, String source,
                  int line, int column, int endLine, int endColumn);

/**
 * A reference to a class resolved during analysis: a bare class value, a
 * constructor ({@code (Foo. ...)}), a static/instance member target, or a
 * type hint. Indexed by the {@code Class} identity. Feeds class find-usages
 * and unused-import.
 */
void classUsage(Class c, Namespace fromNs, String source,
                int line, int column, int endLine, int endColumn);

/**
 * A macro expansion: {@code fromNs} expanded a call to macro var {@code macro}
 * at this position. Always records the compile-time dependency edge fromNs -&gt;
 * macro that drives macro-aware stale reload (design §9). Records a *usage* of
 * the macro (macro calls bypass {@link #varUsage}) only when
 * {@code recordUsage} is true, i.e. the call is source-written - the macro name
 * is textually present at this position. An expansion-introduced macro call (a
 * macro emitting another macro call) passes {@code false}: the edge is still
 * needed, but the usage is captured at the emitting macro's body instead.
 */
void macroExpansion(Var macro, Namespace fromNs, String source,
                    int line, int column, int endLine, int endColumn,
                    boolean recordUsage);

/**
 * An {@code ns} form, handed over whole as it was written, while it is expanding.
 * {@code name} is the namespace it declares.
 *
 * What a sink wants from it is the names its {@code :require} / {@code :use} /
 * {@code :refer-clojure} clauses write in a {@code :refer}, an {@code :only} or a
 * {@code :rename} - the mentions that make a short name mean a var. They are the
 * one place a var's name is written that no analysis of code can reach, and they
 * are unreachable twice over: the specs are handed on as quoted data, so nothing
 * in them is ever resolved as a reference, and a quoted symbol loses its reader
 * position when the form is compiled, so by the time {@code refer} runs there is
 * nothing left to say where the name was written. Expanding is the last moment
 * both facts exist, which is why this is the form rather than a resolved event.
 *
 * Nothing is resolved here: the target namespaces are not loaded yet - the {@code
 * ns} form is what loads them - so a sink reads the names the clauses write and
 * qualifies them itself. Nothing is compiled from the specs either, so no other
 * event reports what they name; {@link #deadForm} hands a form over for the same
 * reason.
 *
 * A sink that records these should mark them for what they are - {@code
 * clojure.analysis} marks the span {@code :declaration :refer} - and leave them out
 * of the unused-* lints: a refer kept alive by its own {@code :refer} would be a
 * refer nothing could ever report.
 *
 * The same goes for the rest of what the clauses write - the library names, their
 * {@code :as} aliases, the classes an {@code :import} names: the namespace they
 * make knows its aliases, refers and imports, and nothing about where the form
 * wrote them. {@code clojure.analysis/ns-specs} reads the form for that.
 *
 * A default method, so a sink with no use for declarations need not implement it.
 */
default void nsForm(Object form, Symbol name, String source){
}

/**
 * A call of {@code clojure.core/require}, {@code clojure.core/use} or {@code
 * clojure.core/requiring-resolve} the source wrote, anywhere - at the top level or
 * in the body of a function - handed over as it was written: {@code fn} is the
 * var's name, {@code fromNs} the namespace the call is compiled in. A
 * requiring-resolve names a var by its quoted name, and loads its namespace.
 *
 * {@link #nsForm}'s reason, for a function: what the call names is quoted, and a
 * quoted symbol's position does not survive the form being compiled - by the time
 * {@code require} runs it is handed a bare symbol. So this fires as the call is
 * analysed, which is before it is run and whether or not it ever is: it is where
 * the source says a library is loaded, not a record of its having been. An {@code
 * ns} form's own expansion into these calls is not reported - the head symbols it
 * builds carry no reader position; {@link #nsForm} has said it already.
 *
 * A default method, for {@link #nsForm}'s reason.
 */
default void requireCall(Object form, Symbol fn, Namespace fromNs, String source){
}

/**
 * A keyword a {@code :keys} destructuring names by the local it binds: {@code
 * {:keys [id]}} is a use of {@code :id} that the source spells {@code id}, and the
 * span is that symbol's. {@code ::keys} and {@code :my.ns/keys} give the keyword
 * their namespace, as destructuring does. A keyword written as one in a {@code
 * :keys} vector is read, and reported, as the keyword it is - {@link
 * #keywordUsage} - and is not reported here too.
 *
 * {@link #nsForm}'s reason: the keyword exists only in the expansion, built from
 * the symbol, and the symbol's position is gone once the form is compiled.
 *
 * A default method, for {@link #nsForm}'s reason.
 */
default void destructuredKeyword(Keyword kw, Namespace fromNs, String source,
                                 int line, int column, int endLine, int endColumn){
}

/**
 * A Java member the source names and the compiler resolved: a method, a field, or
 * a constructor ({@code member} {@code "new"}), keyed by {@code declaring}, the
 * class that declares it. {@code (.length s)} with {@code s} known to be a String
 * is a use of {@code String}'s {@code length}; {@code (.size l)} on a List hint is
 * one of {@code List}'s. A method value, {@code String/valueOf} not called, names
 * every overload of that name, and is reported once per class declaring one.
 *
 * The span is the member's name as written - past a {@code Classname/}, and past
 * the {@code .} or {@code -} in front of it. A call the compiler resolves only by
 * reflection when it runs names no member it can say, and is not reported.
 *
 * A default method, for {@link #nsForm}'s reason.
 */
default void memberUsage(Class declaring, String member, Namespace fromNs, String source,
                         int line, int column, int endLine, int endColumn){
}

/**
 * A class an {@code ns} form names in an {@code :import} - {@link #referUsage}'s
 * fact about a class, and unreachable for one more reason besides: {@code
 * clojure.core/import} turns each spec into the class's full name as a STRING
 * before {@code import*} is ever analysed, so the written name's position exists
 * only while the macro is expanding.
 *
 * The span is the name the spec writes, which under a package spec is the short
 * one: {@code (:import [java.io File])} is positioned at {@code File}, and {@code
 * (:import java.io.File)} over the whole of it. Either way it is what a rename
 * replaces, and {@code c} says which class it named.
 *
 * A default method, for {@link #referUsage}'s reason.
 */
default void importUsage(Class c, Namespace fromNs, String source,
                         int line, int column, int endLine, int endColumn){
}

/**
 * A warning the compiler printed about the form being analysed: {@code kind} is
 * {@code :reflection}, {@code :boxed-math}, {@code :performance} or {@code
 * :earmuffed-var-not-dynamic}, and {@code message} what the printed line says after
 * its position ({@code "call to method foo can't be resolved (target class is
 * unknown)."}) - or, for the last kind, the var's name.
 *
 * Told only when it is printed, so a sink hears what the developer asked to be
 * warned about ({@code *warn-on-reflection*}, {@code *unchecked-math*
 * :warn-on-boxed}) and nothing more. Filed under the form being analysed like any
 * other fact, so a warning goes away with the form that caused it. {@code endLine}
 * and {@code endColumn} are -1 where only the start is known, which is most of them:
 * the compiler knows the line and column of the call.
 *
 * A default method, so a sink with no use for warnings need not implement it.
 */
default void warning(Keyword kind, String message, Namespace ns, String source,
                     int line, int column, int endLine, int endColumn){
}

/**
 * A call of the var {@code target} with {@code argc} arguments, written in source:
 * the var's symbol at the head of the list carries a reader position. The span is
 * the call's - the list as it was written - where the reader gave it one, and the
 * symbol's otherwise. Told after macroexpansion, so {@code (-> x (f 1))} is a call
 * of {@code f} with two arguments at the place {@code (f 1)} is written.
 *
 * What an arity check is made of; the check itself belongs to whoever asks, against
 * the var's {@code :arglists} as they are when it is asked, which is what makes a
 * caller wrong the moment its callee changes and not only when it is compiled again.
 *
 * A default method, so a sink with no use for calls need not implement it.
 */
default void invokeUsage(Var target, int argc, Namespace fromNs, String source,
                         int line, int column, int endLine, int endColumn){
}

/** The {@code kind} of dead code a {@code #_} discard is. */
Keyword DISCARD = Keyword.intern(null, "discard");

/** The {@code kind} of dead code a {@code (comment ...)} call is. */
Keyword COMMENT = Keyword.intern(null, "comment");

/**
 * Code written in the file that the program does not run, handed over whole:
 * the form a {@code #_} discards ({@code kind} {@link #DISCARD}, from the reader,
 * except in the branch of a reader conditional this platform does not take), and
 * a call of {@code clojure.core/comment} ({@link #COMMENT}, from the compiler, as
 * it expands it). Nothing is compiled from it, so no other event reports what it
 * names; a sink that wants to know resolves the symbols in it itself. {@code ns}
 * is the namespace current where the form is written.
 *
 * The span is the stretch of the file that is dead - {@code line}/{@code column}
 * up to, not including, {@code endLine}/{@code endColumn}; all four are -1 when
 * it is not known. It is given apart from the form because the form cannot always
 * carry it: a discarded syntax-quote arrives as its expansion, and a discarded
 * keyword or string holds no metadata. What the reader reports inside the span
 * while reading it (a keyword, a syntax-quoted reference) is dead code too. For a
 * comment the span starts after the {@code comment} symbol, which is a live call.
 *
 * A default method, so a sink with no use for dead code need not implement it.
 */
default void deadForm(Object form, Keyword kind, Namespace ns, String source,
                      int line, int column, int endLine, int endColumn){
}

}
