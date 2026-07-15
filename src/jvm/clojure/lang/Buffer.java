package clojure.lang;

import java.io.IOException;
import java.io.Reader;
import java.util.Arrays;

/**
 * A growable character buffer over a {@link Reader}. This is the single place characters live:
 * {@link LispReader} tokenizes straight out of the backing array, and
 * {@link LineNumberingPushbackReader} is a thin facade over it, so the reader and its callers
 * (the REPL, the Compiler) share one cursor and one line/column count. Nothing else reads the
 * underlying {@link Reader}.
 *
 * <p>The hot path is {@link #read()} / {@link #peek()}: in steady state each is a
 * single bounds check plus an array load. For maximum throughput a tokenizer can
 * bypass those methods entirely and scan the backing array directly:
 *
 * <pre>{@code
 *   int p = buf.pos;
 *   char[] a = buf.buffer;
 *   while (true) {
 *     char c = a[p];
 *     if (c == Buffer.SENTINEL && p == buf.posEnd) { // maybe end of buffered input
 *       buf.pos = p;
 *       if (!buf.refill()) break;                    // real EOF
 *       a = buf.buffer;                              // may have grown
 *       p = buf.pos;                                 // may have shifted (compaction)
 *       continue;
 *     }
 *     if (isDelimiter(c)) break;
 *     p++;
 *   }
 *   buf.pos = p;
 * }</pre>
 *
 * <p>The buffer always keeps {@code buffer[posEnd] == SENTINEL}, so a scan loop needs
 * no per-character bounds check and only reconciles when it lands on the sentinel.
 * {@code SENTINEL} ('\0') may occur legitimately in the input, so a scanner tells a
 * real sentinel apart from end-of-buffered-data with the {@code p == posEnd} test.
 *
 * <p>Consumed input is discarded as the cursor advances, so a long stream does not grow the
 * buffer without bound. Two things hold text in place against that: the current token
 * ({@link #startNewToken()}), and the {@link #pin()} mark, which is how
 * {@code LineNumberingPushbackReader.captureString} keeps a form's source text intact until
 * {@code getString} slices it back out.
 *
 * <p>Not thread-safe.
 */
public class Buffer {
  /** Marker kept at {@code buffer[posEnd]} so scan loops need no per-char bounds check. */
  public static final char SENTINEL = '\0';

  private final Reader reader;
  private final int chunkSize;
  private final int baseLen;
  private final boolean countLines;
  private final boolean collapseNewlines;

  /** Backing store. Invariant: {@code buffer[posEnd] == SENTINEL}. Replaced on growth. */
  public char[] buffer;
  /** Index of the next character to read. */
  public int pos = 0;
  /** One past the last buffered character; {@code buffer[posEnd]} is the sentinel. */
  public int posEnd = 0;

  /** Start of the current token; {@link #unread()} will not step before it. */
  private int tokenStart = 0;
  /** Index compaction must not discard past, or -1 for none. See {@link #pin()}. */
  private int pin = -1;
  /** True once the underlying reader is exhausted. Package-private for tests. */
  boolean eof = false;

  // Lazy line/column tracking. countedPos is how far into the buffer we have counted. Counting is
  // driven off `pos` (the CONSUMED position), never posEnd (the BUFFERED position), so line and
  // column report where the reader actually is no matter how far ahead we have buffered. That is
  // what lets the chunk size be large: with LineNumberReader doing the counting instead, the line
  // number raced ahead to the end of each chunk.
  private int countedPos = 0;
  private int line = 0;
  private int column = 0;
  private boolean skipLF = false;

  // Set when a fill ended on a '\r' (emitted as '\n'). If the next fill opens with '\n' it is the
  // back half of a CRLF straddling the chunk boundary, and must be swallowed.
  private boolean pendingCR = false;

  public Buffer(Reader reader, int chunkSize, boolean countLines, boolean collapseNewlines) {
    this.reader = reader;
    this.chunkSize = chunkSize;
    this.countLines = countLines;
    this.collapseNewlines = collapseNewlines;
    this.baseLen = 2 * chunkSize + 1;   // +1 reserves the sentinel slot
    this.buffer = new char[baseLen];    // zero-filled, so buffer[0] == SENTINEL
  }

  public Buffer(Reader reader, int chunkSize, boolean countLines) {
    this(reader, chunkSize, countLines, false);
  }

  public Buffer(Reader reader, int chunkSize) {
    this(reader, chunkSize, false, false);
  }

  /** Returns the next character, or -1 at end of input. */
  public int read() throws IOException {
    if (pos < posEnd) return buffer[pos++];
    return fill() ? buffer[pos++] : -1;
  }

  /** Returns the next character without consuming it, or -1 at end of input. */
  public int peek() throws IOException {
    if (pos < posEnd) return buffer[pos];
    return fill() ? buffer[pos] : -1;
  }

  /** Steps back one character. Never steps before the current token's start. */
  public void unread() {
    if (pos > tokenStart) pos--;
  }

  /**
   * Pushes {@code c} back so that it is read next. Unlike {@link #unread()} this is a true
   * pushback -- it is what serves {@code LineNumberingPushbackReader.unread}, whose callers may
   * push back a character other than the one they read. Makes room behind the cursor if the
   * buffer has just been compacted and there is none.
   */
  public void unread(char c) {
    if (pos == 0) makeRoomBefore(1);
    pos--;
    buffer[pos] = c;
    if (countLines && countedPos > pos) uncount(c);
  }

  /**
   * Pins the current position: compaction will not discard anything before it, so the text from
   * here onward stays contiguous in {@link #buffer} until {@link #unpin()}. This is how
   * {@code captureString} / {@code getString} (i.e. {@code clojure.core/read+string}) capture a
   * form's source text without copying a character.
   */
  public void pin() {
    pin = pos;
  }

  /** The pinned index, adjusted for any compaction since {@link #pin()}, or -1 if not pinned. */
  public int getPin() {
    return pin;
  }

  public void unpin() {
    pin = -1;
  }

  /**
   * Loads more input after {@code posEnd}. Returns true if at least one new character
   * was buffered, false at end of input. May grow or compact the buffer, so a caller
   * scanning the array directly must reload both {@link #buffer} and {@link #pos}.
   */
  public boolean refill() throws IOException {
    return fill();
  }

  // Ensures at least one unread character is available, without advancing pos.
  private boolean fill() throws IOException {
    if (eof) return false;
    while (true) {
      ensureRoom();
      int n = reader.read(buffer, posEnd, chunkSize);
      if (n <= 0) {
        eof = true;
        buffer[posEnd] = SENTINEL;
        return false;
      }
      if (collapseNewlines) n = collapse(posEnd, n);
      if (n > 0) {
        posEnd += n;
        buffer[posEnd] = SENTINEL;
        return true;
      }
      // The whole chunk collapsed away -- it was the '\n' of a CRLF split across a chunk
      // boundary. Nothing new is readable yet, so go round again.
    }
  }

  /**
   * Rewrites the freshly-read run [start, start+n) in place, collapsing CR, LF and CRLF each to a
   * single '\n', and returns the new length. Stock Clojure gets this from the LineNumberReader
   * that LineNumberingPushbackReader wraps -- so a string literal spanning a CRLF holds a bare
   * '\n' -- and we must match it. Here it happens once, in the one buffer everything reads from.
   */
  private int collapse(int start, int n) {
    char[] a = buffer;
    int w = start;
    for (int i = start; i < start + n; i++) {
      char c = a[i];
      if (c == '\r') {
        a[w++] = '\n';
        pendingCR = true;
      } else if (c == '\n') {
        if (pendingCR) pendingCR = false;   // back half of a CRLF; the '\n' is already emitted
        else a[w++] = '\n';
      } else {
        pendingCR = false;
        a[w++] = c;
      }
    }
    return w - start;
  }

  // Guarantees room for another chunk (plus the sentinel) after posEnd, reclaiming the discarded
  // prefix first, then doubling capacity as a last resort.
  private void ensureRoom() {
    if (buffer.length - posEnd > chunkSize) return;
    int k = discardable();
    if (k > 0) {
      shiftDown(k);
      if (buffer.length - posEnd > chunkSize) return;
    }
    int needed = posEnd + chunkSize + 1;
    int newLen = buffer.length;
    while (newLen < needed) newLen <<= 1;
    buffer = Arrays.copyOf(buffer, newLen);
  }

  // How much of the prefix may be thrown away: everything before the current token, but never
  // past the pin.
  private int discardable() {
    int k = tokenStart;
    if (pin >= 0 && pin < k) k = pin;
    return k;
  }

  // Number of already-consumed characters to keep behind pos so that a pushback (unread) has
  // somewhere to land. A LineNumberingPushbackReader consumer only ever unreads one character at
  // a time (skip-whitespace, skip-if-eol); 16 is comfortable headroom.
  private static final int PUSHBACK_MARGIN = 16;

  // Reclaims consumed input for a consumer that drives this Buffer purely as a Reader
  // (LineNumberingPushbackReader's read / readLine / skip) rather than through LispReader's
  // tokenizers. Those tokenizers advance tokenStart via startNewToken(); a plain Reader consumer
  // never does, so without this tokenStart would stay put and the backing array would grow without
  // bound over a long stream. Advancing tokenStart toward pos lets the next fill() shift the prefix
  // down. The pin (read+string capture) still caps discarding, via discardable(). Safe because the
  // facade never runs during a LispReader token scan -- the two share the cursor but not the clock.
  void reclaimConsumed() {
    int floor = pos - PUSHBACK_MARGIN;
    if (floor > tokenStart)
      tokenStart = floor;
  }

  // Opens n free slots behind pos by shifting the live region up, so unread() has somewhere to go.
  private void makeRoomBefore(int n) {
    if (buffer.length - posEnd <= n)
      buffer = Arrays.copyOf(buffer, Math.max(baseLen, buffer.length * 2));
    System.arraycopy(buffer, 0, buffer, n, posEnd);
    pos += n;
    posEnd += n;
    tokenStart += n;
    if (pin >= 0) pin += n;
    if (countLines) countedPos += n;
    buffer[posEnd] = SENTINEL;
  }

  // Drops the first k characters, shifting the live region down and fixing up every
  // index (including line-counting state) so nothing uncounted is discarded.
  private void shiftDown(int k) {
    if (k <= 0) return;
    updateLineColumn();                 // count up to pos before discarding [0, k)
    System.arraycopy(buffer, k, buffer, 0, posEnd - k);
    pos -= k;
    posEnd -= k;
    tokenStart = Math.max(0, tokenStart - k);
    if (pin >= 0) pin = Math.max(0, pin - k);
    if (countLines) countedPos = Math.max(0, countedPos - k);
    buffer[posEnd] = SENTINEL;
  }

  public char[] getToken() {
    return buffer;
  }

  public int getTokenStart() {
    return tokenStart;
  }

  public int getTokenEnd() {
    return pos;
  }

  public String getTokenString() {
    return new String(buffer, tokenStart, pos - tokenStart);
  }

  /**
   * Marks the previous token as finished and begins a new one at the current position.
   * Periodically compacts the buffer (discarding consumed input) and shrinks it back
   * toward its initial size once it has grown.
   */
  public void startNewToken() {
    if (pos > chunkSize) {
      int k = (pin >= 0 && pin < pos) ? pin : pos;
      if (k > 0) {
        shiftDown(k);
        if (buffer.length > baseLen && posEnd < chunkSize) {
          buffer = Arrays.copyOf(buffer, baseLen);
        }
      }
    }
    tokenStart = pos;
  }

  /**
   * Collapses the last {@code replaceLength} characters read into the single character
   * {@code ch} (e.g. "\r\n" -> "\n"). No-op if that would reach before the token start.
   */
  public void replace(int replaceLength, char ch) {
    int replacePos = pos - replaceLength;
    if (replacePos < tokenStart) return;
    buffer[replacePos] = ch;
    int shift = replaceLength - 1;
    System.arraycopy(buffer, pos, buffer, replacePos + 1, posEnd - pos);
    posEnd -= shift;
    pos -= shift;
    if (countLines && countedPos > replacePos) {
      countedPos = Math.max(replacePos, countedPos - shift);
    }
    buffer[posEnd] = SENTINEL;
  }

  private void updateLineColumn() {
    if (!countLines) return;
    char[] a = buffer;
    int line = this.line, column = this.column;
    boolean skipLF = this.skipLF;
    for (int i = countedPos; i < pos; i++) {
      char ch = a[i];
      if (skipLF && ch == '\n') { skipLF = false; continue; }
      if (ch == '\r') { skipLF = true; line++; column = 0; }
      else if (ch == '\n') { skipLF = false; line++; column = 0; }
      else { skipLF = false; column++; }
    }
    this.line = line;
    this.column = column;
    this.skipLF = skipLF;
    countedPos = pos;
  }

  // Rolls the line/column counters back over a single pushed-back character. Exact for the only
  // case that actually arises: everything that unreads (clojure.main/skip-whitespace, skip-if-eol,
  // Compiler.consumeWhitespaces) pushes back a NON-newline character.
  private void uncount(char c) {
    countedPos = pos;
    if (c == '\n') {
      if (line > 0) line--;
      int col = columnEndingAt(pos);
      if (col >= 0) column = col;
    } else if (column > 0) {
      column--;
    }
  }

  // Column of position p, by scanning back to the preceding '\n'. Returns -1 if that newline has
  // already been discarded from the buffer, in which case the caller keeps the column it had.
  private int columnEndingAt(int p) {
    for (int i = p - 1; i >= 0; i--)
      if (buffer[i] == '\n') return p - 1 - i;
    return -1;
  }

  /** Whether this buffer tracks line/column. Only a LineNumberingPushbackReader's buffer does. */
  public boolean countsLines() {
    return countLines;
  }

  /** 0-based line of the CONSUMED position, or -1 if this buffer does not count lines. */
  public int getLine() {
    if (!countLines) return -1;
    updateLineColumn();
    return line;
  }

  /** 0-based column of the CONSUMED position, or -1 if this buffer does not count lines. */
  public int getColumn() {
    if (!countLines) return -1;
    updateLineColumn();
    return column;
  }

  /** Overrides the 0-based line (clojure.main/renumbering-read re-numbers a form it re-reads). */
  public void setLine(int line) {
    if (!countLines) return;
    updateLineColumn();     // settle any pending count first, then override
    this.line = line;
  }
}
