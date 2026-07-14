package clojure.lang;

import java.io.IOException;
import java.io.Reader;
import java.util.Arrays;

/**
 * A growable character buffer over a {@link Reader}, designed as the basis for a
 * fast EDN/Clojure reader.
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
 * <p>Not thread-safe.
 */
public class Buffer {
  /** Marker kept at {@code buffer[posEnd]} so scan loops need no per-char bounds check. */
  public static final char SENTINEL = '\0';

  private final Reader reader;
  private final int chunkSize;
  private final int baseLen;
  private final boolean countLines;

  /** Backing store. Invariant: {@code buffer[posEnd] == SENTINEL}. Replaced on growth. */
  public char[] buffer;
  /** Index of the next character to read. */
  public int pos = 0;
  /** One past the last buffered character; {@code buffer[posEnd]} is the sentinel. */
  public int posEnd = 0;

  /** Start of the current token; {@link #unread()} will not step before it. */
  private int tokenStart = 0;
  /** True once the underlying reader is exhausted. Package-private for tests. */
  boolean eof = false;

  // Lazy line/column tracking. countedPos is how far into the buffer we have counted.
  private int countedPos = 0;
  private int line = 0;
  private int column = 0;
  private boolean skipLF = false;

  public Buffer(Reader reader, int chunkSize, boolean countLines) {
    this.reader = reader;
    this.chunkSize = chunkSize;
    this.countLines = countLines;
    this.baseLen = 2 * chunkSize + 1;   // +1 reserves the sentinel slot
    this.buffer = new char[baseLen];    // zero-filled, so buffer[0] == SENTINEL
  }

  public Buffer(Reader reader, int chunkSize) {
    this(reader, chunkSize, false);
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
    ensureRoom();
    int n = reader.read(buffer, posEnd, chunkSize);
    if (n <= 0) {
      eof = true;
      buffer[posEnd] = SENTINEL;
      return false;
    }
    posEnd += n;
    buffer[posEnd] = SENTINEL;
    return true;
  }

  // Guarantees room for another chunk (plus the sentinel) after posEnd, reclaiming the
  // discarded prefix before tokenStart first, then doubling capacity as a last resort.
  private void ensureRoom() {
    if (buffer.length - posEnd > chunkSize) return;
    if (tokenStart > 0) {
      shiftDown(tokenStart);
      if (buffer.length - posEnd > chunkSize) return;
    }
    int needed = posEnd + chunkSize + 1;
    int newLen = buffer.length;
    while (newLen < needed) newLen <<= 1;
    buffer = Arrays.copyOf(buffer, newLen);
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
      shiftDown(pos);
      if (buffer.length > baseLen && posEnd < chunkSize) {
        buffer = Arrays.copyOf(buffer, baseLen);
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

  public int getLine() {
    if (!countLines) return -1;
    updateLineColumn();
    return line;
  }

  public int getColumn() {
    if (!countLines) return -1;
    updateLineColumn();
    return column;
  }
}
