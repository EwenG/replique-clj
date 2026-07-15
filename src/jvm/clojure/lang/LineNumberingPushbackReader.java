/**
 * Copyright (c) Rich Hickey. All rights reserved.
 * The use and distribution terms for this software are covered by the
 * Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
 * which can be found in the file epl-v10.html at the root of this distribution.
 * By using this software in any fashion, you are agreeing to be bound by
 * the terms of this license.
 * You must not remove this notice, or any other, from this software.
 */

package clojure.lang;

import java.io.PushbackReader;
import java.io.Reader;
import java.io.IOException;


/**
 * A facade over a single {@link Buffer}, which is the only thing that reads the underlying Reader.
 *
 * <p>Stock Clojure builds this out of a LineNumberReader plus a PushbackReader's pushback array,
 * and LispReader then reads characters out of it one at a time. That left characters living in two
 * places, which is fine only as long as the reader never buffers ahead -- and a chunked reader
 * does nothing but buffer ahead. With two cursors, reading a chunk ahead would (a) race the line
 * counter to the end of the chunk, so Compiler.load stamps every form with the wrong line, (b) let
 * the capture buffer swallow text past the form, so read+string returns too much, and (c) hide
 * those characters from clojure.main/repl-read, which reads this stream directly.
 *
 * <p>So there is exactly one cursor now: {@code buffer.pos}. Every method below routes to the
 * Buffer, and {@link LispReader} tokenizes out of that same Buffer rather than draining it. None
 * of PushbackReader's inherited machinery is used -- we still extend it only because the class is
 * public API and callers (clojure.main, the Compiler, tooling) are typed against it.
 *
 * <p>Line and column come from the Buffer, which counts to the CONSUMED position rather than the
 * buffered one, so they stay correct at any chunk size. Capture is a pin plus a slice: the source
 * text is already sitting contiguously in the buffer, so read+string copies nothing.
 */
public class LineNumberingPushbackReader extends PushbackReader{

public static final int DEFAULT_CHUNK_SIZE = 4096;

private final Buffer buffer;
// Cached across forms so its token cache (interned symbols/keywords) survives a whole file load.
private LispReader lispReader;

public LineNumberingPushbackReader(Reader r){
	this(r, DEFAULT_CHUNK_SIZE);
}

public LineNumberingPushbackReader(Reader r, int size){
	// super(r) only so that close() closes the source; every read/unread below goes to `buffer`.
	// The Buffer both counts lines and collapses CR / LF / CRLF to '\n' -- the two jobs the
	// LineNumberReader used to do.
	super(r, 1);
	this.buffer = new Buffer(r, size, true, true);
}

Buffer buffer(){
	return buffer;
}

LispReader lispReader(){
	if(lispReader == null)
		lispReader = new LispReader(buffer);
	return lispReader;
}

public int getLineNumber(){
	return buffer.getLine() + 1;          // Buffer counts from 0, this API from 1
}

public void setLineNumber(int line){
	buffer.setLine(line - 1);
}

public void captureString(){
	buffer.pin();
}

public String getString(){
	int start = buffer.getPin();
	if(start < 0)
		return null;
	String ret = new String(buffer.buffer, start, buffer.pos - start);
	buffer.unpin();
	return ret;
}

public int getColumnNumber(){
	return buffer.getColumn() + 1;        // Buffer counts from 0, this API from 1
}

public int read() throws IOException{
	// reclaimConsumed keeps the backing array from growing without bound when this reader is driven
	// as a plain Reader (never through LispReader's tokenizers, which is what normally reclaims).
	buffer.reclaimConsumed();
	return buffer.read();
}

public int read(char[] cbuf, int off, int len) throws IOException{
	if(len <= 0)
		return 0;
	buffer.reclaimConsumed();
	if(buffer.pos >= buffer.posEnd && !buffer.refill())
		return -1;
	int n = Math.min(len, buffer.posEnd - buffer.pos);
	System.arraycopy(buffer.buffer, buffer.pos, cbuf, off, n);
	buffer.pos += n;                      // line counting is lazy and driven off pos; nothing else to do
	return n;
}

public void unread(int c) throws IOException{
	if(c != -1)
		buffer.unread((char) c);
}

public void unread(char[] cbuf, int off, int len) throws IOException{
	// Push back in reverse so the characters come out again in their original order.
	for(int i = len - 1; i >= 0; i--)
		buffer.unread(cbuf[off + i]);
}

public String readLine() throws IOException{
	int c = buffer.read();
	if(c == -1)
		return null;
	if(c == '\n')                         // the Buffer has already collapsed CR and CRLF to '\n'
		return "";
	StringBuilder sb = new StringBuilder();
	sb.append((char) c);
	for(; ;)
		{
		buffer.reclaimConsumed();         // bound growth even for one very long line
		c = buffer.read();
		if(c == -1 || c == '\n')
			return sb.toString();
		sb.append((char) c);
		}
}

public boolean atLineStart(){
	return buffer.getColumn() == 0;
}

public boolean ready() throws IOException{
	return buffer.pos < buffer.posEnd || super.ready();
}

public long skip(long n) throws IOException{
	long skipped = 0;
	while(skipped < n)
		{
		buffer.reclaimConsumed();
		if(buffer.read() == -1)
			break;
		skipped++;
		}
	return skipped;
}
}
