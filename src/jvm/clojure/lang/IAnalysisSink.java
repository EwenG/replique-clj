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
 * This is Layer 0 of the analysis feature (var definitions and usages only).
 * See doc/analysis-and-reload.md for the full design.
 */
public interface IAnalysisSink{

/**
 * A var reference resolved during analysis. {@code target} is the referenced
 * var, {@code fromNs} the namespace being compiled where the reference occurs.
 * When the reference symbol carries reader positions (Layer 1), the span is
 * precise: {@code line}/{@code column} at the symbol and {@code endLine}/
 * {@code endColumn} just past it. When it does not, positions fall back to the
 * enclosing form's line/column and {@code endLine}/{@code endColumn} are -1.
 */
void varUsage(Var target, Namespace fromNs, String source,
              int line, int column, int endLine, int endColumn);

/**
 * A var defined by a top-level def form. The defining namespace is
 * {@code var.ns}. Positions follow the same convention as {@link #varUsage}.
 */
void varDef(Var var, String source,
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
 * at this position. Records both a usage of the macro (macro calls bypass
 * {@link #varUsage}) and the compile-time dependency edge fromNs -&gt; macro
 * that drives macro-aware stale reload (design §9).
 */
void macroExpansion(Var macro, Namespace fromNs, String source,
                    int line, int column, int endLine, int endColumn);

}
