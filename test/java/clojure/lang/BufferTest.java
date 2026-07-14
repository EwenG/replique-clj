package clojure.lang;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.StringReader;

import static org.junit.jupiter.api.Assertions.*;

public class BufferTest {

  @Test
  public void testReadCharacters() throws IOException {
    Buffer buffer = new Buffer(new StringReader("abc"), 2);

    assertEquals('a', buffer.read());
    assertEquals('b', buffer.read());
    assertEquals('c', buffer.read());
    assertEquals(-1, buffer.read()); // End of input
  }

  @Test
  public void testPeekDoesNotAdvance() throws IOException {
    Buffer buffer = new Buffer(new StringReader("ab"), 2);

    assertEquals('a', buffer.peek());
    assertEquals('a', buffer.peek()); // still 'a'
    assertEquals('a', buffer.read());
    assertEquals('b', buffer.peek());
    assertEquals('b', buffer.read());
    assertEquals(-1, buffer.peek()); // EOF
    assertEquals(-1, buffer.read());
  }

  @Test
  public void testUnreadBehavior() throws IOException {
    Buffer buffer = new Buffer(new StringReader("xyz"), 2);
    assertEquals('x', buffer.read());
    assertEquals('y', buffer.read());
    buffer.unread(); // Should step back to 'y'
    assertEquals('y', buffer.read());
  }

  @Test
  public void testUnreadDoesNotUnderflowTokenStart() throws IOException {
    Buffer buffer = new Buffer(new StringReader("hi"), 1);
    buffer.startNewToken();
    assertEquals('h', buffer.read());
    buffer.unread(); // valid unread
    buffer.unread(); // should not go before tokenStart
    assertEquals('h', buffer.read());
  }

  @Test
  public void testTokenStringAndBounds() throws IOException {
    Buffer buffer = new Buffer(new StringReader("hello world"), 5);
    buffer.startNewToken();
    for (int i = 0; i < 5; i++) buffer.read(); // h e l l o

    assertEquals("hello", buffer.getTokenString());
    assertEquals(0, buffer.getTokenStart());
    assertEquals(5, buffer.getTokenEnd());
  }

  @Test
  public void testStartNewTokenNoCompaction() throws IOException {
    // pos (3) is not greater than chunkSize (3), so no compaction: positions are kept.
    Buffer buffer = new Buffer(new StringReader("abcdef"), 3);
    buffer.read(); // a
    buffer.read(); // b
    buffer.read(); // c
    buffer.startNewToken();

    buffer.read(); // d
    buffer.read(); // e

    assertEquals("de", buffer.getTokenString());
    assertEquals(3, buffer.getTokenStart());
    assertEquals(5, buffer.getTokenEnd());
  }

  @Test
  public void testStartNewTokenCompacts() throws IOException {
    // pos (3) exceeds chunkSize (2), so startNewToken compacts back to the front.
    Buffer buffer = new Buffer(new StringReader("abcdef"), 2);
    buffer.read(); // a
    buffer.read(); // b
    buffer.read(); // c
    buffer.startNewToken(); // shifts remaining data to index 0

    buffer.read(); // d
    buffer.read(); // e

    assertEquals("de", buffer.getTokenString());
    assertEquals(0, buffer.getTokenStart());
    assertEquals(2, buffer.getTokenEnd());
  }

  @Test
  public void testBufferGrowthBeyondInitialSize() throws IOException {
    String input = "01234567890123456789"; // 20 characters
    Buffer buffer = new Buffer(new StringReader(input), 5);
    int base = buffer.buffer.length;

    StringBuilder result = new StringBuilder();
    int ch;
    while ((ch = buffer.read()) != -1) {
      result.append((char) ch);
    }

    assertEquals(input, result.toString());
    assertTrue(buffer.buffer.length > base, "buffer should have grown"); // never compacted
  }

  @Test
  public void testBufferShrinksAfterGrowth() throws IOException {
    int chunkSize = 4;
    Buffer buffer = new Buffer(new StringReader("abcdefghi"), chunkSize);
    int base = buffer.buffer.length; // 2 * chunkSize + 1

    // Read everything without starting a new token, forcing the buffer to grow.
    for (int i = 0; i < 9; i++) {
      buffer.read();
    }
    assertTrue(buffer.buffer.length > base, "buffer should have grown");

    // Consumed input is discarded; buffer shrinks back to its initial size.
    buffer.startNewToken();
    assertEquals(base, buffer.buffer.length, "buffer should shrink back to initial size");
  }

  @Test
  public void testEOFHandling() throws IOException {
    Buffer buffer = new Buffer(new StringReader("x"), 1);
    assertEquals('x', buffer.read());
    assertEquals(-1, buffer.read()); // EOF
    assertEquals(-1, buffer.read()); // Keep returning EOF
    assertTrue(buffer.eof); // package-private, visible to tests
  }

  @Test
  public void testSentinelAtPosEnd() throws IOException {
    Buffer buffer = new Buffer(new StringReader("hi"), 8);
    buffer.read();
    assertEquals(Buffer.SENTINEL, buffer.buffer[buffer.posEnd]);
    buffer.read();
    assertEquals(Buffer.SENTINEL, buffer.buffer[buffer.posEnd]);
  }

  @Test
  public void testLineColumns() throws IOException {
    Buffer buffer = new Buffer(new StringReader("abc\nde"), 2, true);

    assertEquals(0, buffer.getLine());
    assertEquals(0, buffer.getColumn());
    buffer.read();
    assertEquals(0, buffer.getLine());
    assertEquals(1, buffer.getColumn());
    buffer.read();
    assertEquals(0, buffer.getLine());
    assertEquals(2, buffer.getColumn());
    buffer.read();
    assertEquals(0, buffer.getLine());
    assertEquals(3, buffer.getColumn());
    buffer.read();
    assertEquals(1, buffer.getLine());
    assertEquals(0, buffer.getColumn());
    buffer.read();
    assertEquals(1, buffer.getLine());
    assertEquals(1, buffer.getColumn());
    buffer.read();
    assertEquals(1, buffer.getLine());
    assertEquals(2, buffer.getColumn());
    assertEquals(-1, buffer.read());
  }

  @Test
  public void testLineColumnsDisabled() throws IOException {
    Buffer buffer = new Buffer(new StringReader("a\nb"), 2); // countLines defaults to false
    buffer.read();
    buffer.read();
    assertEquals(-1, buffer.getLine());
    assertEquals(-1, buffer.getColumn());
  }

  @Test
  public void testCRLFCountsAsOneLine() throws IOException {
    Buffer buffer = new Buffer(new StringReader("a\r\nb"), 8, true);
    buffer.read(); // a
    buffer.read(); // \r
    assertEquals(1, buffer.getLine());
    assertEquals(0, buffer.getColumn());
    buffer.read(); // \n  -- part of the same line break, not a second one
    assertEquals(1, buffer.getLine());
    assertEquals(0, buffer.getColumn());
    buffer.read(); // b
    assertEquals(1, buffer.getLine());
    assertEquals(1, buffer.getColumn());
  }

  @Test
  public void testLineCountingAcrossCompaction() throws IOException {
    // Regression: line/column must stay correct after startNewToken compacts the buffer.
    Buffer buffer = new Buffer(new StringReader("ab\ncde\nfg"), 2, true);

    buffer.read(); // a
    buffer.read(); // b
    buffer.read(); // \n
    assertEquals(1, buffer.getLine());
    assertEquals(0, buffer.getColumn());

    buffer.startNewToken(); // pos (3) > chunkSize (2): compacts

    buffer.read(); // c
    buffer.read(); // d
    buffer.read(); // e
    assertEquals(1, buffer.getLine());
    assertEquals(3, buffer.getColumn());

    buffer.read(); // \n
    assertEquals(2, buffer.getLine());
    assertEquals(0, buffer.getColumn());

    buffer.startNewToken(); // compacts again

    buffer.read(); // f
    buffer.read(); // g
    assertEquals(2, buffer.getLine());
    assertEquals(2, buffer.getColumn());
  }

  @Test
  public void testReplaceCollapsesChars() throws IOException {
    Buffer buffer = new Buffer(new StringReader("a\r\nb"), 8);
    buffer.startNewToken();
    assertEquals('a', buffer.read());
    assertEquals('\r', buffer.read());
    assertEquals('\n', buffer.read());

    buffer.replace(2, '\n'); // collapse "\r\n" -> "\n"

    assertEquals("a\n", buffer.getTokenString());
    assertEquals('b', buffer.read()); // must NOT re-read a stale character
    assertEquals(-1, buffer.read());
  }

  @Test
  public void testReplaceWorksAtEOF() throws IOException {
    Buffer buffer = new Buffer(new StringReader("a\r\n"), 8);
    buffer.startNewToken();
    buffer.read(); // a
    buffer.read(); // \r
    buffer.read(); // \n
    assertEquals(-1, buffer.read()); // hits EOF

    buffer.replace(2, '\n'); // still collapses, even after EOF

    assertEquals("a\n", buffer.getTokenString());
  }

  @Test
  public void testReplaceKeepsLookahead() throws IOException {
    // Ensure buffered lookahead past the replacement is preserved and re-readable.
    Buffer buffer = new Buffer(new StringReader("a\r\nbc"), 8);
    buffer.startNewToken();
    buffer.read(); // a
    buffer.read(); // \r
    buffer.read(); // \n

    buffer.replace(2, '\n');

    assertEquals("a\n", buffer.getTokenString());
    assertEquals('b', buffer.read());
    assertEquals('c', buffer.read());
    assertEquals(-1, buffer.read());
  }

  @Test
  public void testDirectArrayScan() throws IOException {
    // Demonstrates the fast tokenizer pattern: scan the backing array directly,
    // reconciling only at the sentinel and reloading buffer/pos after refill.
    Buffer buffer = new Buffer(new StringReader("hello world"), 4);
    buffer.startNewToken();

    int p = buffer.pos;
    char[] a = buffer.buffer;
    while (true) {
      char c = a[p];
      if (c == Buffer.SENTINEL && p == buffer.posEnd) {
        buffer.pos = p;
        if (!buffer.refill()) break; // real EOF
        a = buffer.buffer;           // may have grown
        p = buffer.pos;              // may have shifted
        continue;
      }
      if (c == ' ') break;
      p++;
    }
    buffer.pos = p;

    assertEquals("hello", buffer.getTokenString());
  }
}
