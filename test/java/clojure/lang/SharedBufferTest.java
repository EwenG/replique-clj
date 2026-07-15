package clojure.lang;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Regression tests for the shared-{@link Buffer} architecture, covering the ways a chunked reader
 * that shares its cursor with {@link LineNumberingPushbackReader} can go wrong. Each of these
 * guards a bug found in review that the value-only reader tests did not catch, because they turn
 * on the buffer STATE the reader leaves behind (captured source text, line count, backing-array
 * size) rather than the value read.
 */
public class SharedBufferTest {

  private static LineNumberingPushbackReader lnpr(String s) {
    return new LineNumberingPushbackReader(new StringReader(s));
  }

  // read+string's source capture (captureString/getString over a Buffer pin) must return the
  // verbatim source of the form -- including a string literal's escapes UN-decoded. The bug: the
  // reader decoded escapes in place, overwriting the very bytes the capture reads.
  @Test
  public void captureReturnsVerbatimSourceWithEscapes() throws IOException {
    // (o, expected source text). The reader consumes exactly the form; getString is the source.
    String[][] cases = {
        {"\"a\\nb\"", "\"a\\nb\""},              // \n stays two chars in the source
        {"\"tab\\tend\"", "\"tab\\tend\""},
        {"\"u\\u0041z\"", "\"u\\u0041z\""},
        {"\"plain\"", "\"plain\""},               // no-escape fast path
        {"(def x \"a\\r\\nb\")", "(def x \"a\\r\\nb\")"},
    };
    for (String[] c : cases) {
      LineNumberingPushbackReader r = lnpr(c[0] + " trailing");
      r.captureString();
      Object form = LispReader.read(r, false, null, false, null);
      assertNotNull(form);
      assertEquals(c[1], r.getString().trim(),
          "captured source for " + c[0]);
    }
  }

  // A \n / \r escape inside a string literal must NOT advance the source line counter: it is one
  // token on one line. The bug: the in-place decode wrote a real newline into the counted region,
  // so every following form's line number was inflated.
  @Test
  public void escapedNewlineInStringDoesNotBumpLineNumber() throws IOException {
    LineNumberingPushbackReader r = lnpr("(def s \"line1\\nstill\")\n(def t 42)");
    LispReader.read(r, false, null, false, null);   // read the first form
    // Still on line 1: the only real newline (before the second form) has not been consumed yet.
    // The bug counted the string's decoded \n as a source line, which would report 2 here.
    assertEquals(1, r.getLineNumber(), "line after a string containing a \\n escape");
    Object second = LispReader.read(r, false, null, false, null);
    assertEquals(2, RT.get(RT.meta(second), Keyword.intern(null, "line")),
        ":line metadata of the form after an escaped-newline string");
  }

  // Driving the reader as a plain Reader (readLine over a big stream) must run in bounded memory.
  // The bug: tokenStart, advanced only by LispReader's tokenizers, stayed at 0, so consumed input
  // was never reclaimed and the backing array grew without bound.
  @Test
  public void plainReaderUseIsMemoryBounded() throws IOException {
    // 2 million chars (20k lines x 100) with no line ever retained. If the buffer accumulated it
    // would dwarf the base chunk size; we assert it stays within a small multiple of it.
    final long total = 2_000_000L;
    Reader synth = new Reader() {
      long produced = 0;
      public int read(char[] cbuf, int off, int len) {
        if (produced >= total) return -1;
        int n = (int) Math.min(len, Math.min(8192, total - produced));
        for (int i = 0; i < n; i++)
          cbuf[off + i] = ((produced + i + 1) % 100 == 0) ? '\n' : 'x';
        produced += n;
        return n;
      }
      public void close() {}
    };
    LineNumberingPushbackReader r = new LineNumberingPushbackReader(synth);
    Buffer buf = r.buffer();
    String line;
    int lines = 0;
    while ((line = r.readLine()) != null) {
      lines++;
      // Backing array must stay bounded: a few chunks, never proportional to the stream.
      assertTrue(buf.buffer.length < 200_000,
          "backing array grew to " + buf.buffer.length + " after " + lines + " lines");
    }
    assertEquals(20_000, lines);
  }

  // A reentrant read on the SAME reader (a data reader whose body reads another form) must not
  // corrupt the outer read. The cached reader's per-read state (#() args, #?@ queue) is saved and
  // restored around each top-level read.
  @Test
  public void reentrantReadDoesNotCorruptOuterState() throws IOException {
    final LineNumberingPushbackReader r = lnpr("[1 #x/pull 2 3 4]");
    IFn pull = new AFn() {
      public Object invoke(Object form) {
        return LispReader.read(r, false, null, true, null);   // read the next form off the stream
      }
    };
    Var.pushThreadBindings(RT.map(
        RT.var("clojure.core", "*data-readers*"),
        RT.map(Symbol.intern("x", "pull"), pull)));
    try {
      Object v = LispReader.read(r, false, null, false, null);
      // The data reader swallowed the 2; the outer vector keeps 1, then 3 and 4.
      assertEquals(RT.readString("[1 3 4]"), v);
    } finally {
      Var.popThreadBindings();
    }
  }
}
