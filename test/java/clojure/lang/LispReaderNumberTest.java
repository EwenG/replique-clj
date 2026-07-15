package clojure.lang;

import org.junit.jupiter.api.Test;

import java.io.StringReader;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Verifies the new {@link LispReader}'s number reading against Clojure 1.12.5's original reader
 * ({@link OriginalLispReader}). Every input is checked at several buffer chunk
 * sizes so the tokenizer's refill / compaction / growth paths are exercised too.
 */
public class LispReaderNumberTest {

  private static final int[] CHUNK_SIZES = {1, 2, 3, 7, 4096};

  // Reads one form with LispReader, capturing either the value or the thrown exception.
  private static Object reader2Read(String input, int chunkSize) {
    try {
      return new LispReader(new StringReader(input), chunkSize).read();
    } catch (Throwable t) {
      return t;
    }
  }

  // The oracle: Clojure 1.12.5's original reader, kept verbatim in test scope. Note this must
  // NOT be RT.readString -- in this fork that IS the reader under test, so it would pass vacuously.
  private static Object clojureRead(String input) {
    try {
      return OriginalLispReader.read(
          new java.io.PushbackReader(new StringReader(input)), (Object) null);
    } catch (Throwable t) {
      return t;
    }
  }

  /** Asserts LispReader matches Clojure for `input`, across all chunk sizes. */
  private static void assertMatchesClojure(String input) {
    Object expected = clojureRead(input);
    boolean clojureThrew = expected instanceof Throwable;

    for (int chunk : CHUNK_SIZES) {
      Object actual = reader2Read(input, chunk);

      if (clojureThrew) {
        // LispReader returns its EOF sentinel for a formless top-level input (e.g. a bare
        // comment) where Clojure's read-string throws EOF — an intentional API difference.
        assertTrue(actual instanceof Throwable || actual == LispReader.EOF,
            "Clojure threw " + expected.getClass().getSimpleName()
                + " but LispReader returned " + actual + " for \"" + input + "\" (chunk=" + chunk + ")");
        continue;
      }

      assertFalse(actual instanceof Throwable,
          "Clojure read " + expected + " but LispReader threw " + actual + " for \"" + input + "\" (chunk=" + chunk + ")");
      if (expected == null || actual == null) { // nil
        assertEquals(expected, actual, "nil mismatch for \"" + input + "\" (chunk=" + chunk + ")");
        continue;
      }
      assertEquals(expected.getClass(), actual.getClass(),
          "type mismatch for \"" + input + "\" (chunk=" + chunk + ")");
      if (expected instanceof java.util.regex.Pattern)   // Pattern has no value equals
        assertEquals(((java.util.regex.Pattern) expected).pattern(),
            ((java.util.regex.Pattern) actual).pattern(),
            "regex mismatch for \"" + input + "\" (chunk=" + chunk + ")");
      else
        assertEquals(expected, actual,
            "value mismatch for \"" + input + "\" (chunk=" + chunk + ")");
      assertEquals(clojure.lang.RT.meta(expected), clojure.lang.RT.meta(actual),
          "metadata mismatch for \"" + input + "\" (chunk=" + chunk + ")");
    }
  }

  private static void assertAllMatchClojure(String... inputs) {
    for (String in : inputs) assertMatchesClojure(in);
  }

  @Test
  public void testLongs() {
    assertAllMatchClojure("0", "1", "123", "-123", "+123", "42", "-1", "+1",
        "1000000", "-999", "9223372036854775807", "-9223372036854775808");
  }

  @Test
  public void testBigInts() {
    assertAllMatchClojure("9223372036854775808", "-9223372036854775809",
        "0N", "-0N", "+0N", "10N", "-10N", "123456789012345678901234567890",
        "-123456789012345678901234567890", "99999999999999999999N");
  }

  @Test
  public void testZeroForms() {
    assertAllMatchClojure("0", "-0", "+0", "00", "000", "0N", "-0N");
  }

  @Test
  public void testOctal() {
    assertAllMatchClojure("007", "0777", "010", "-0777", "+010", "0777N",
        "0777777777777777777777", "01777777777777777777777", "02000000000000000000000");
  }

  @Test
  public void testInvalidOctal() {
    // Leading-zero decimals that aren't valid octal are rejected by Clojure.
    assertAllMatchClojure("08", "09", "0778", "019");
  }

  @Test
  public void testHex() {
    assertAllMatchClojure("0x1F", "0X1f", "0xff", "0xffN", "-0xFF", "0x0", "0xdeadbeef",
        "+0x10", "0x7fffffffffffffff", "0x8000000000000000", "0xffffffffffffffff",
        "-0x8000000000000000", "0xG", "0x", "0xffffffffffffffffffN");
  }

  @Test
  public void testRadix() {
    assertAllMatchClojure("2r1010", "16rff", "36rZ", "-2r111", "8r777", "10r123", "2r0");
  }

  @Test
  public void testRadixOutOfRange() {
    assertAllMatchClojure("1r0", "37rZ", "99rZ");
  }

  @Test
  public void testDoubles() {
    assertAllMatchClojure("1.0", "1.", "-1.5", "3.14", "1e3", "1E3", "1.5e-2",
        "1e10", "10.", "-0.0", "0.0", "1.5e+3", "123.456",
        // leading-zero floats: intPat does NOT claim these, so they are doubles
        "0.5", "08.5", "0e3", "00.5", "0.0e0", "-0.25", "+1.5", "0.", "07.0");
  }

  @Test
  public void testBigDecimals() {
    assertAllMatchClojure("1M", "1.5M", "-2.5M", "0M", "3.14159M", "100M", "1e10M");
  }

  @Test
  public void testRatios() {
    assertAllMatchClojure("1/2", "4/2", "6/4", "-3/4", "+3/6", "10/5", "-6/3", "22/7");
  }

  @Test
  public void testRatioDivideByZero() {
    // Clojure throws ArithmeticException; LispReader does too (via Numbers.divide).
    assertMatchesClojure("1/0");
  }

  @Test
  public void testInvalidNumbers() {
    assertAllMatchClojure("1x", "12abc", "1.2.3", "1/2/3", "0xG", "2r2", "1e", "1..0");
  }

  @Test
  public void testNumberFollowedByDelimiter() {
    // LispReader and RT.readString both read a single leading form.
    assertAllMatchClojure("123)", "1 2 3", "42]", "7}", "5;comment", "9 ", "  8  ");
  }

  @Test
  public void testEofReturnsSentinel() throws java.io.IOException {
    assertSame(LispReader.EOF, new LispReader(new StringReader("")).read());
    assertSame(LispReader.EOF, new LispReader(new StringReader("   ")).read());
    assertSame(LispReader.EOF, new LispReader(new StringReader(" , \n ")).read());
  }

  @Test
  public void testFuzzAgainstClojure() {
    // Generate number-ish tokens from a numeric alphabet and diff against Clojure.
    // Only tokens that start like a number (digit, or sign+digit) are in scope.
    char[] alphabet = "0123456789.eExXrRMN/+-abcdefABCDEF".toCharArray();
    java.util.Random rnd = new java.util.Random(20260708L); // fixed seed: reproducible
    int checked = 0;
    for (int t = 0; t < 20000; t++) {
      int len = 1 + rnd.nextInt(8);
      StringBuilder sb = new StringBuilder(len);
      for (int i = 0; i < len; i++) sb.append(alphabet[rnd.nextInt(alphabet.length)]);
      String tok = sb.toString();

      char c0 = tok.charAt(0);
      boolean numberStart = Character.isDigit(c0)
          || ((c0 == '+' || c0 == '-') && tok.length() > 1 && Character.isDigit(tok.charAt(1)));
      if (!numberStart) continue; // Clojure would read a symbol; out of scope

      assertMatchesClojure(tok);
      checked++;
    }
    assertTrue(checked > 500, "expected a meaningful number of fuzz cases, got " + checked);
  }

  @Test
  public void testSymbols() {
    assertAllMatchClojure("foo", "foo-bar", "foo/bar", "clojure.core/x", "+", "-", "/",
        "*", "name", ".", "..", "...", "->", "foo?", "foo!", "*ns*", "a.b.c", "a.b/c-d",
        "foo#", "foo'", "a'b", "foo//", "foo:bar", "a/b/c", "foo/bar/baz",
        "x#y%z", "clojure.string/join", ".5", "-foo", "+foo", "->>", "<=");
  }

  @Test
  public void testKeywords() {
    assertAllMatchClojure(":foo", ":foo/bar", ":a.b/c", ":foo:bar", ":123", ":1a", ":/",
        ":clojure.core/x", ":-", ":+", ":*ns*", ":a/b/c", ":x.y.z/w");
  }

  @Test
  public void testAutoResolvedKeywords() {
    // ::foo resolves against clojure.core/*ns* — same var LispReader and RT.readString read.
    // ::ns/name resolves ns as an ALIAS only, so an unaliased (even real) namespace throws.
    assertAllMatchClojure("::foo", "::bar", "::x",
        "::clojure.core/bar", "::clojure.core/x", "::nope/y", "::foo/bar");
  }

  @Test
  public void testArrayClassSymbols() {
    // Clojure 1.12 array-class syntax: ns/N with N a single 1-9.
    assertAllMatchClojure("int/1", "String/2", "a/8", "java.lang.String/3", "foo/9",
        "a/0", "a/10", "a/8b", "foo/1bar", "&X_/8");
  }

  @Test
  public void testNilTrueFalse() {
    assertAllMatchClojure("nil", "true", "false");
  }

  @Test
  public void testInvalidTokens() {
    assertAllMatchClojure("foo:", "//", ":", "::", ":::", "foo/", "/foo", ":foo/",
        "a::b", "::foo/bar", "::nope/x", "x:");
  }

  @Test
  public void testTokenFollowedByDelimiter() {
    assertAllMatchClojure("foo)", "foo bar", ":kw]", "nil,", "true}", "sym;comment",
        "foo\"str", "a\\b");
  }

  @Test
  public void testStrings() {
    assertAllMatchClojure(
        "\"hello\"", "\"\"", "\"a b c\"", "\"123\"", "\"with,comma\"",
        "\"multi word string\"", "\"tab\tliteral\"", "\"unicodeéhere\"");
  }

  @Test
  public void testStringEscapes() {
    assertAllMatchClojure(
        "\"a\\nb\"", "\"a\\tb\"", "\"a\\rb\"", "\"a\\\\b\"", "\"a\\\"b\"",
        "\"\\b\\f\\n\\r\\t\"", "\"q:\\\"end\"", "\"back:\\\\end\"", "\"\\n\\n\\n\"");
  }

  @Test
  public void testStringUnicodeAndOctal() {
    assertAllMatchClojure(
        "\"\\u0041\"", "\"\\u00e9\"", "\"\\uABCD\"", "\"\\101\"", "\"\\0\"",
        "\"\\377\"", "\"pre\\u0041post\"", "\"\\41x\"", "\"\\7\"");
  }

  @Test
  public void testStringErrors() {
    assertAllMatchClojure(
        "\"unterminated", "\"bad\\xescape\"", "\"\\u12\"", "\"\\uZZZZ\"",
        "\"\\400\"", "\"trailing\\", "\"\\u\"");
  }

  @Test
  public void testCharacters() {
    assertAllMatchClojure(
        "\\a", "\\A", "\\1", "\\(", "\\)", "\\\"", "\\\\", "\\;", "\\/", "\\+", "\\ ");
  }

  @Test
  public void testNamedCharacters() {
    assertAllMatchClojure(
        "\\newline", "\\space", "\\tab", "\\backspace", "\\formfeed", "\\return");
  }

  @Test
  public void testCharacterUnicodeAndOctal() {
    assertAllMatchClojure(
        "\\u0041", "\\u00e9", "\\uABCD", "\\o101", "\\o0", "\\o377", "\\o7");
  }

  @Test
  public void testCharacterErrors() {
    assertAllMatchClojure(
        "\\uD800", "\\u123", "\\uXYZW", "\\o777", "\\o1234", "\\foo", "\\newlin", "\\");
  }

  @Test
  public void testCharacterFollowedByDelimiter() {
    assertAllMatchClojure("\\a)", "\\a b", "\\newline;c", "\\space]", "\\1 2", "\\( x");
  }

  @Test
  public void testLists() {
    assertAllMatchClojure("(1 2 3)", "()", "(a b c)", "( 1  2 )", "(1,2,3)",
        "(+ 1 2)", "(nil true false)", "(())", "(1 (2 (3)))", "(:a :b)", "(1 2 . 3)");
  }

  @Test
  public void testVectors() {
    assertAllMatchClojure("[1 2 3]", "[]", "[a b c]", "[[1] [2]]", "[1,2,3]",
        "[nil true]", "[[[]]]", "[:x :y :z]", "[\"s\" \\c 1]");
  }

  @Test
  public void testMaps() {
    assertAllMatchClojure("{:a 1 :b 2}", "{}", "{\"k\" \"v\"}", "{1 2 3 4}",
        "{:a {:b 1}}", "{:x [1 2]}", "{:a 1, :b 2, :c 3}");
  }

  @Test
  public void testSets() {
    assertAllMatchClojure("#{1 2 3}", "#{}", "#{:a :b}", "#{\"x\" \"y\"}",
        "#{1 [2] :three}", "#{nil true false}");
  }

  @Test
  public void testNestedCollections() {
    assertAllMatchClojure("(1 [2 3] {:x 4})", "[{:a #{1 2}} (3 4)]",
        "{:list (1 2 3) :vec [4 5]}", "(((1)))", "[() [] {} #{}]", "{[1 2] #{3 4}}");
  }

  @Test
  public void testCollectionErrors() {
    assertAllMatchClojure(")", "]", "}", "(1 2", "[1 2", "{:a 1", "#{1 2",
        "(1 ] )", "[1 2 3)", "{:a}", "{:a 1 :a 2}", "#{1 1}", "{:a 1 :b 2 :c}");
  }

  @Test
  public void testComments() {
    assertAllMatchClojure("; comment\n42", "(1 ; c\n 2)", "#! shebang\n7",
        "42 ; trailing", "[1 ;; c\n 2 3]", "; only-first\n(a b)");
  }

  @Test
  public void testDiscard() {
    assertAllMatchClojure("#_ 1 2", "(1 #_2 3)", "[#_#_1 2 3]", "#_(1 2) 99",
        "{:a #_:skip 1}", "#_#_1 2 3", "(#_1)", "[1 #_ ; c\n 2 3]");
  }

  @Test
  public void testQuoteDerefVar() {
    assertAllMatchClojure("'x", "'(1 2 3)", "'foo/bar", "''x", "'nil",
        "@x", "@(atom 1)", "@@x", "#'x", "#'foo/bar", "#'clojure.core/map",
        "(quote x)", "['a @b #'c]");
  }

  @Test
  public void testUnquote() {
    assertAllMatchClojure("~x", "~@x", "~(a b)", "~@(1 2 3)", "[~a ~@b]");
  }

  @Test
  public void testSymbolicValues() {
    assertAllMatchClojure("##Inf", "##-Inf", "##NaN", "## Inf", "##Foo", "##", "##1",
        "[##Inf ##-Inf ##NaN]");
  }

  @Test
  public void testMetadata() {
    assertAllMatchClojure("^:m x", "^{:a 1} x", "^String x", "^\"tag\" x", "^:a ^:b x",
        "^{:a 1 :b 2} (1 2)", "^:kw [1 2]", "^sym {:x 1}", "^:m 5", "^:m :kw");
  }

  @Test
  public void testRegex() {
    // Note: Pattern has no value equals, so patterns are only comparable at top level here.
    assertAllMatchClojure("#\"a.*b\"", "#\"\\d+\"", "#\"\"", "#\"[a-z]+\"",
        "#\"a\\\"b\"", "#\"\\s*\\w+\"", "#\"unterminated");
  }

  @Test
  public void testTaggedLiterals() {
    assertAllMatchClojure("#inst \"2020-01-01\"", "#inst \"2020-01-01T12:34:56\"",
        "#uuid \"550e8400-e29b-41d4-a716-446655440000\"",
        "#foo/bar 42", "#unknown 1", "#inst \"not-a-date\"", "#uuid \"bad\"",
        "(1 #inst \"2020-01-01\" 2)");
  }

  @Test
  public void testNamespacedMaps() {
    assertAllMatchClojure(
        "#:ns{:a 1 :b 2}", "#:ns{:a 1}", "#::{:x 1}", "#:person{:name \"a\" :age 30}",
        "#:ns{}", "#::{}", "#:ns {:a 1}", "#::  {:x 1}", "#:clojure.core{:a 1}", "#:a.b.c{:x 1}",
        // key rewriting rules
        "#:ns{:other/k 1}", "#:ns{:_/k 1}", "#:ns{sym 1}", "#:ns{:a/b 1}", "#:ns{1 2}",
        "#:ns{\"s\" 1}", "#:ns{:_/k 1 :a 2}",
        // nested
        "(1 #:ns{:a 1} 2)", "[#:x{:y 1}]", "#:outer{:a #:inner{:b 1}}",
        // errors
        "#:{}", "#::", "#:ns", "#:ns 5", "#:ns[1 2]", "#: ns {:a 1}", "#:ns/x{:a 1}",
        "#:5{:a 1}", "#::nope{:a 1}", "#:ns{:a 1 :a 2}", "#:ns{:a}");
  }

  @Test
  public void testDispatchErrors() {
    assertAllMatchClojure("#<x>", "#<unreadable>", "#?(:clj 1 :cljs 2)", "#?@(:clj [1])",
        "#$", "# ");
  }

  // Runs `body` with clojure.core/*read-eval* bound to `val`.
  private static Object withReadEval(Object val, java.util.concurrent.Callable<Object> body) {
    return withVar("*read-eval*", val, body);
  }

  // Runs `body` with the named clojure.core dynamic var bound to `val`.
  private static Object withVar(String varName, Object val, java.util.concurrent.Callable<Object> body) {
    clojure.lang.Var v = RT.var("clojure.core", varName);
    clojure.lang.Var.pushThreadBindings(RT.map(v, val));
    try {
      return body.call();
    } catch (Throwable t) {
      return t;
    } finally {
      clojure.lang.Var.popThreadBindings();
    }
  }

  @Test
  public void testDefaultDataReaderFn() {
    // A default-data-reader-fn that tags the (tag, form) pair, matching Clojure's call order.
    clojure.lang.IFn f = new clojure.lang.AFn() {
      @Override public Object invoke(Object tag, Object form) { return RT.map(TAG_KW, tag, FORM_KW, form); }
    };
    for (String s : new String[]{"#foo/bar 42", "#unknown [1 2]"}) {
      Object expected = withVar("*default-data-reader-fn*", f, () -> clojureRead(s));
      for (int chunk : CHUNK_SIZES) {
        Object actual = withVar("*default-data-reader-fn*", f, () -> new LispReader(new StringReader(s), chunk).read());
        assertEquals(expected, actual, "default-data-reader-fn mismatch for \"" + s + "\" (chunk=" + chunk + ")");
      }
    }
    // A registered reader (#inst) wins over the default fn — it is never consulted.
    Object inst = withVar("*default-data-reader-fn*", f, () -> new LispReader(new StringReader("#inst \"2020-01-01\"")).read());
    assertEquals(clojureRead("#inst \"2020-01-01\""), inst, "registered reader should bypass default fn");
    // A dotted tag is a record literal (unsupported): both Clojure and LispReader throw, and the
    // default fn must NOT be invoked (else LispReader would wrongly return a value).
    Object rec = withVar("*default-data-reader-fn*", f, () -> new LispReader(new StringReader("#my.Rec{:a 1}")).read());
    assertTrue(rec instanceof Throwable, "dotted (record) tag must throw, not hit the default fn, but got " + rec);
  }

  private static final clojure.lang.Keyword TAG_KW = clojure.lang.Keyword.intern(null, "tag");
  private static final clojure.lang.Keyword FORM_KW = clojure.lang.Keyword.intern(null, "form");

  @Test
  public void testReadEvalGating() {
    clojure.lang.Keyword unknown = clojure.lang.Keyword.intern(null, "unknown");

    // *read-eval* :unknown disallows all reading, matching LispReader's top-of-read guard.
    for (String s : new String[]{"#=(+ 1 2)", "(+ 1 2)", "42", ":kw"}) {
      Object r = withReadEval(unknown, () -> new LispReader(new StringReader(s)).read());
      assertTrue(r instanceof RuntimeException
              && "Reading disallowed - *read-eval* bound to :unknown".equals(((Throwable) r).getMessage()),
          "expected :unknown read-disallowed for \"" + s + "\" but got " + r);
    }

    // *read-eval* false/nil disables #= with LispReader's exact message; the following form
    // is not read (the guard fires first), so a malformed inner form is irrelevant.
    for (Object falsey : new Object[]{Boolean.FALSE, null}) {
      for (String s : new String[]{"#=(+ 1 2)", "#=junk", "#=x"}) {
        Object r = withReadEval(falsey, () -> new LispReader(new StringReader(s)).read());
        assertTrue(r instanceof RuntimeException
                && "EvalReader not allowed when *read-eval* is false.".equals(((Throwable) r).getMessage()),
            "expected EvalReader-not-allowed for \"" + s + "\" (read-eval=" + falsey + ") but got " + r);
      }
    }

    // With eval enabled, Clojure would evaluate; LispReader intentionally does not (no compiler).
    // Only the #= form differs — ordinary forms still read fine under read-eval true.
    Object plain = withReadEval(Boolean.TRUE, () -> new LispReader(new StringReader("(+ 1 2)")).read());
    assertEquals(clojureRead("(+ 1 2)"), plain, "ordinary form should read under read-eval true");
    Object evalForm = withReadEval(Boolean.TRUE, () -> new LispReader(new StringReader("#=(+ 1 2)")).read());
    assertTrue(evalForm instanceof UnsupportedOperationException,
        "#= with eval enabled should throw UnsupportedOperationException but got " + evalForm);
  }

  // Canonicalizes gensym symbols (p1__N#, foo__N__auto__) by first-appearance order, so two
  // syntax-quote / #() expansions that differ only in the global RT.nextID() counter compare
  // equal. Rebuilds every collection so the comparison is structural. (Broad differential
  // coverage — including the inherently order-nondeterministic set/map-under-nested-quote
  // cases — is done separately against Clojure 1.12.5; these are deterministic regressions.)
  private static Object normGensyms(Object form, java.util.Map<clojure.lang.Symbol, clojure.lang.Symbol> m, int[] ctr) {
    if (form instanceof clojure.lang.Symbol) {
      clojure.lang.Symbol s = (clojure.lang.Symbol) form;
      String nm = s.getName();
      if (nm.matches(".*__\\d+__auto__") || nm.matches(".*__\\d+#")) {
        clojure.lang.Symbol canon = m.get(s);
        if (canon == null) {
          canon = clojure.lang.Symbol.intern(s.getNamespace(), nm.replaceAll("__\\d+", "__G" + (++ctr[0])));
          m.put(s, canon);
        }
        return canon;
      }
      return s;
    }
    if (form instanceof clojure.lang.IPersistentVector) {
      clojure.lang.IPersistentVector v = (clojure.lang.IPersistentVector) form;
      java.util.ArrayList<Object> out = new java.util.ArrayList<>();
      for (int i = 0; i < v.count(); i++) out.add(normGensyms(v.nth(i), m, ctr));
      return clojure.lang.LazilyPersistentVector.create(out);
    }
    if (form instanceof clojure.lang.IPersistentMap) {
      java.util.ArrayList<Object> kvs = new java.util.ArrayList<>();
      for (clojure.lang.ISeq s = RT.seq(form); s != null; s = s.next()) {
        clojure.lang.IMapEntry e = (clojure.lang.IMapEntry) s.first();
        kvs.add(normGensyms(e.key(), m, ctr));
        kvs.add(normGensyms(e.val(), m, ctr));
      }
      return RT.map(kvs.toArray());
    }
    if (form instanceof clojure.lang.IPersistentSet) {
      java.util.ArrayList<Object> es = new java.util.ArrayList<>();
      for (clojure.lang.ISeq s = RT.seq(form); s != null; s = s.next()) es.add(normGensyms(s.first(), m, ctr));
      return clojure.lang.PersistentHashSet.create(es);
    }
    if (form instanceof clojure.lang.ISeq || form instanceof clojure.lang.IPersistentList) {
      java.util.ArrayList<Object> out = new java.util.ArrayList<>();
      for (clojure.lang.ISeq s = RT.seq(form); s != null; s = s.next()) out.add(normGensyms(s.first(), m, ctr));
      return out.isEmpty() ? clojure.lang.PersistentList.EMPTY : clojure.lang.PersistentList.create(out);
    }
    return form;
  }

  // Asserts LispReader matches Clojure for a syntax-quote / #() form, modulo gensym numbering.
  private static void assertGensymMatch(String input) {
    Object expected = clojureRead(input);
    boolean threw = expected instanceof Throwable;
    for (int chunk : CHUNK_SIZES) {
      Object actual = reader2Read(input, chunk);
      if (threw) {
        assertTrue(actual instanceof Throwable,
            "Clojure threw but LispReader returned " + actual + " for \"" + input + "\" (chunk=" + chunk + ")");
        continue;
      }
      assertFalse(actual instanceof Throwable,
          "Clojure read " + expected + " but LispReader threw " + actual + " for \"" + input + "\" (chunk=" + chunk + ")");
      assertEquals(expected.getClass(), actual.getClass(),
          "type mismatch for \"" + input + "\" (chunk=" + chunk + ")");
      Object ne = normGensyms(expected, new java.util.HashMap<>(), new int[]{0});
      Object na = normGensyms(actual, new java.util.HashMap<>(), new int[]{0});
      assertEquals(ne, na, "syntax-quote/fn mismatch for \"" + input + "\" (chunk=" + chunk + ")");
    }
  }

  @Test
  public void testSyntaxQuoteSimple() {
    // No gensyms — must match Clojure exactly (including class + resolution).
    assertAllMatchClojure("`x", "`5", "`:kw", "`\"s\"", "`nil", "`true",
        "`map", "`inc", "`foo/bar", "`clojure.core/map", "`if", "`do", "`let*", "`fn*",
        "`quote", "`recur", "`.foo", "`Foo.", "`()", "`(a b c)", "`[a b c]", "`{:a 1 :b 2}",
        "`#{a b c}", "`~x", "`~@x", "`(a ~b c)", "`(a ~@b c)", "`(1 ~(+ 1 2) 3)", "``x");
  }

  @Test
  public void testSyntaxQuoteGensym() {
    // Auto-gensyms in deterministic (list/vector) contexts.
    assertGensymMatch("`x#");
    assertGensymMatch("`(x# x#)");
    assertGensymMatch("`[a# a# b#]");
    assertGensymMatch("`(let [x# 1] x#)");
    assertGensymMatch("`(fn [a#] (+ a# a#))");
    assertGensymMatch("`(~x x# ~@ys x#)");
  }

  @Test
  public void testSyntaxQuoteErrors() {
    assertAllMatchClojure("`~@x", "`");   // splice-not-in-list, EOF
  }

  @Test
  public void testAnonymousFn() {
    assertGensymMatch("#(+ % 1)");
    assertGensymMatch("#(+ %1 %2)");
    assertGensymMatch("#()");
    assertGensymMatch("#(inc %)");
    assertGensymMatch("#(list % %2 %3)");
    assertGensymMatch("#(apply + %&)");
    assertGensymMatch("#(list %1 %&)");
    assertGensymMatch("#(vector %2)");            // %2 without %1 -> generated p1
    assertGensymMatch("#(do %)");
    assertGensymMatch("#(#{%})");
    assertGensymMatch("#([% %2])");
    assertGensymMatch("#({:a %})");
    assertGensymMatch("'#(+ % 1)");               // quoted fn literal
    assertGensymMatch("`#(inc %)");               // syntax-quoted fn literal
  }

  @Test
  public void testAnonymousFnErrors() {
    assertAllMatchClojure("#(#(+ % 1))", "%1", "#(%bad %)", "#(% ");   // nested #(), % outside, bad arg, EOF
  }

  @Test
  public void testCollectionFuzzAgainstClojure() {
    // Random s-expressions built from the reader macros we support, plus atoms.
    String[] atoms = {"1", "-2", "3.5", "foo", ":kw", "a/b", "\"s\"", "\\c", "nil",
        "true", "1/2", "0xff", "#_9", ";x\n"};
    String[] open = {"(", "[", "{", "#{"};
    String[] close = {")", "]", "}", "}"};
    java.util.Random rnd = new java.util.Random(0xDEADBEEFL);
    for (int t = 0; t < 20000; t++) {
      StringBuilder sb = new StringBuilder();
      java.util.Deque<String> stack = new java.util.ArrayDeque<>();
      int tokens = 1 + rnd.nextInt(14);
      for (int i = 0; i < tokens; i++) {
        int r = rnd.nextInt(10);
        if (r < 3 && stack.size() < 5) { int k = rnd.nextInt(open.length); sb.append(open[k]).append(' '); stack.push(close[k]); }
        else if (r < 4 && !stack.isEmpty()) { sb.append(stack.pop()).append(' '); }
        else { sb.append(atoms[rnd.nextInt(atoms.length)]).append(' '); }
      }
      while (!stack.isEmpty()) sb.append(stack.pop()).append(' ');   // usually balanced
      assertMatchesClojure(sb.toString().trim());
    }
  }

  @Test
  public void testStringAndCharFuzzAgainstClojure() {
    // Random string bodies (with backslashes/quotes) and character forms vs Clojure.
    char[] body = "abc \\\"nrtufo019AF{}[]:;/".toCharArray();
    java.util.Random rnd = new java.util.Random(0xC0FFEEL);
    for (int t = 0; t < 20000; t++) {
      int len = rnd.nextInt(8);
      StringBuilder sb = new StringBuilder("\"");
      for (int i = 0; i < len; i++) sb.append(body[rnd.nextInt(body.length)]);
      sb.append('"');
      assertMatchesClojure(sb.toString());
    }
    char[] cbody = "abcnewliuo0139AF() \\".toCharArray();
    for (int t = 0; t < 20000; t++) {
      int len = 1 + rnd.nextInt(6);
      StringBuilder sb = new StringBuilder("\\");
      for (int i = 0; i < len; i++) sb.append(cbody[rnd.nextInt(cbody.length)]);
      assertMatchesClojure(sb.toString());
    }
  }

  @Test
  public void testSymbolFuzzAgainstClojure() {
    // Tokens that reach readToken in Clojure (first char is not whitespace, digit, or a
    // reader-macro char). Embedded terminators are fine: both readers stop at the same spot.
    char[] alphabet = "abcXYZ+-*/.:!?_'#%<>=&$.0123456789".toCharArray();
    java.util.Random rnd = new java.util.Random(19731129L); // fixed seed
    int checked = 0;
    for (int t = 0; t < 20000; t++) {
      int len = 1 + rnd.nextInt(8);
      StringBuilder sb = new StringBuilder(len);
      for (int i = 0; i < len; i++) sb.append(alphabet[rnd.nextInt(alphabet.length)]);
      String tok = sb.toString();

      char c0 = tok.charAt(0);
      if (Character.isDigit(c0) || isWhitespaceCh(c0) || isMacroCh(c0)) continue;
      assertMatchesClojure(tok);
      checked++;
    }
    assertTrue(checked > 500, "expected a meaningful number of fuzz cases, got " + checked);
  }

  private static boolean isWhitespaceCh(char c) {
    return c == ',' || Character.isWhitespace(c);
  }

  private static boolean isMacroCh(char c) {
    return "\";'@^`~()[]{}\\%#".indexOf(c) >= 0;
  }

  // The deprecated #^ metadata reader is the old spelling of ^; both must read identically.
  @Test
  public void testDeprecatedMetaReaderAgainstClojure() {
    assertAllMatchClojure(
        "#^String x",           // symbol tag -> {:tag String}
        "#^:dynamic x",         // keyword    -> {:dynamic true}
        "#^{:a 1} [1 2]",       // map meta
        "#^\"tag\" x",          // string tag
        "[#^Long a #^Long b]"); // several in a collection
  }

  // Record construction (#pkg.Class[...] / #pkg.Class{...}). readRecord works on any class with a
  // matching constructor / create method, so java.awt.Point (a stable (int,int) data class) lets
  // this run without defining a record. Diffed against the original reader like everything else.
  @Test
  public void testRecordConstructionAgainstClojure() {
    assertAllMatchClojure(
        "#java.awt.Point[1 2]",       // positional -> new Point(1, 2)
        "#java.awt.Point[3 4] ",
        "[#java.awt.Point[1 2] :x]",  // nested in a collection
        "#java.awt.Point[1 2 3]",     // wrong arity -> both throw
        "#java.awt.Point 5",          // neither vector nor map -> both throw "Unreadable constructor"
        "#no.such.Class[1]");         // missing class -> both throw
  }
}
