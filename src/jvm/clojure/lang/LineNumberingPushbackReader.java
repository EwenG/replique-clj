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
import java.io.LineNumberReader;
import java.io.IOException;


public class LineNumberingPushbackReader extends PushbackReader{

// This class is a PushbackReader that wraps a LineNumberReader. The code
// here to handle line terminators only mentions '\n' because
// LineNumberReader collapses all occurrences of CR, LF, and CRLF into a
// single '\n'.

private static final int newline = (int) '\n';

private boolean _atLineStart = true;
private boolean _prev;
private int _columnNumber = 1;
private StringBuilder sb = null;

// PushbackReader defaults to a one-character pushback buffer. LispReader reads through
// read(char[],int,int) and pushes its unconsumed lookahead back in one go, so give it room.
private static final int PUSHBACK_SIZE = 64;

public LineNumberingPushbackReader(Reader r){
	super(new LineNumberReader(r), PUSHBACK_SIZE);
}

public LineNumberingPushbackReader(Reader r, int size){
	super(new LineNumberReader(r, size), PUSHBACK_SIZE);
}

public int getLineNumber(){
	return ((LineNumberReader) in).getLineNumber() + 1;
}

public void setLineNumber(int line) { ((LineNumberReader) in).setLineNumber(line - 1); }

public void captureString(){
    this.sb = new StringBuilder();
}

public String getString(){
    if(sb != null)
        {
        String ret = sb.toString();
        sb = null;
        return ret;
        }
    return null;
}

public int getColumnNumber(){
	return _columnNumber;
}

public int read() throws IOException{
    int c = super.read();
    _prev = _atLineStart;
    if((c == newline) || (c == -1))
        {
        _atLineStart = true;
        _columnNumber = 1;
        }
    else
        {
        _atLineStart = false;
        _columnNumber++;
        }
    if(sb != null && c != -1)
        sb.append((char)c);
    return c;
}

public void unread(int c) throws IOException{
    super.unread(c);
    _atLineStart = _prev;
    _columnNumber--;
    if(sb != null)
        sb.deleteCharAt(sb.length()-1);
}

// LispReader reads through the array methods rather than read()/unread(int), so these must keep
// the same column / line-start state and, crucially, feed the capture buffer that
// captureString()/getString() (i.e. clojure.core/read+string) rely on. Without this, read+string
// returns "" and clojure.main/renumbering-read then re-reads an empty string.
public int read(char[] cbuf, int off, int len) throws IOException{
    int n = super.read(cbuf, off, len);
    if(n <= 0)
        {
        if(n == -1)
            {
            _prev = _atLineStart;
            _atLineStart = true;
            _columnNumber = 1;
            }
        return n;
        }
    for(int i = 0; i < n; i++)
        {
        _prev = _atLineStart;
        if(cbuf[off + i] == newline)
            {
            _atLineStart = true;
            _columnNumber = 1;
            }
        else
            {
            _atLineStart = false;
            _columnNumber++;
            }
        }
    if(sb != null)
        sb.append(cbuf, off, n);
    return n;
}

public void unread(char[] cbuf, int off, int len) throws IOException{
    // Push back in reverse so the characters come back out in their original order, reusing
    // unread(int) so the capture buffer and column state unwind along with them.
    for(int i = len - 1; i >= 0; i--)
        unread(cbuf[off + i]);
}

public String readLine() throws IOException{
    int c = read();
    String line;
    switch (c) {
    case -1:
        line = null;
        break;
    case newline:
        line = "";
        break;
    default:
        String first = String.valueOf((char) c);
        String rest = ((LineNumberReader)in).readLine();
        if (sb != null)
          sb.append(rest+"\n");
        line = (rest == null) ? first : first + rest;
        _prev = false;
        _atLineStart = true;
        _columnNumber = 1;
        break;
    }
    return line;
}

public boolean atLineStart(){
    return _atLineStart;
}
}
