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

}
