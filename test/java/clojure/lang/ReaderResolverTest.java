package clojure.lang;

import org.junit.jupiter.api.Test;

import java.io.PushbackReader;
import java.io.StringReader;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Differential test for {@code *reader-resolver*} ({@link LispReader.Resolver}). A bound resolver
 * overrides how {@code ::keywords}, {@code #::maps}, and syntax-quoted symbols resolve. Clojure's
 * own suite does not exercise this at all, so the new reader is diffed against the original one
 * ({@link OriginalLispReader}) with the SAME resolver bound to both.
 *
 * <p>The two readers declare distinct Resolver interfaces, so the test resolver implements both;
 * the four methods are identical in signature. Reads go through the static {@code read(PushbackReader
 * , …)} path, which is where each reader picks the resolver up from {@code RT.READER_RESOLVER}.
 */
public class ReaderResolverTest {

  // A deterministic resolver: alias "a" -> aliased.ns, class alias "Str" -> java.lang.String,
  // every other class unresolved, vars land in the resolver's current ns.
  static final class TestResolver implements LispReader.Resolver, OriginalLispReader.Resolver {
    public Symbol currentNS()            { return Symbol.intern("my.current"); }
    public Symbol resolveClass(Symbol s) { return s.getName().equals("Str") ? Symbol.intern("java.lang.String") : null; }
    public Symbol resolveAlias(Symbol s) { return s.getName().equals("a") ? Symbol.intern("aliased.ns") : null; }
    public Symbol resolveVar(Symbol s)   { return Symbol.intern("my.current", s.getName()); }
  }

  private static Object read(String kind, String input) {
    try {
      PushbackReader r = new PushbackReader(new StringReader(input));
      return kind.equals("fork")
          ? LispReader.read(r, false, null, false, null)
          : OriginalLispReader.read(r, false, null, false);
    } catch (Throwable t) {
      return t.getClass().getName() + ": " + t.getMessage();
    }
  }

  private static void assertSameWithResolver(String... inputs) {
    Var.pushThreadBindings(RT.map(RT.READER_RESOLVER, new TestResolver()));
    try {
      for (String in : inputs) {
        Object fork = read("fork", in);
        Object orig = read("orig", in);
        assertEquals(orig, fork, "with *reader-resolver* bound, reading \"" + in + "\"");
      }
    } finally {
      Var.popThreadBindings();
    }
  }

  @Test
  public void autoResolvedKeywords() {
    assertSameWithResolver(
        "::a/foo",     // alias a -> aliased.ns  => :aliased.ns/foo
        "::foo",       // no alias -> currentNS  => :my.current/foo
        "::unknown/x");// unknown alias -> resolver returns null => nil keyword (both same)
  }

  @Test
  public void namespacedMaps() {
    assertSameWithResolver(
        "#::{:x 1}",        // no sym -> currentNS
        "#::a{:x 1 :y 2}",  // alias a -> aliased.ns
        "#::a{:_/bare 1}"); // _ namespace still means unqualified
  }

  @Test
  public void syntaxQuotedSymbols() {
    assertSameWithResolver(
        "`foo",        // resolveVar -> my.current/foo
        "`Str",        // resolveClass -> java.lang.String
        "`a/foo",      // ns is an alias -> aliased.ns/foo
        "`Str/method", // ns is a class alias -> java.lang.String/method
        "`foo.",       // ctor sugar, class unresolved -> stays foo.
        "`.instanceMethod"); // leading-dot names are left alone
    // (auto-gensym `x#` and unquote are resolver-independent -- those branches run before the
    // resolver is consulted -- and RT.nextID() makes their output differ across two reads, so
    // they are covered by the number/symbol fuzz tests, not here.)
  }
}
