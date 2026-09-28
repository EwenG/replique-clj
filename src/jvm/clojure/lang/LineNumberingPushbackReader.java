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

// The position just past the last character that stayed read - what the end of a
// source span wants, and what the line and column above cannot answer. A token is
// terminated by reading one character too many and unreading it, and by then read()
// has already moved them: for a newline the wrapped LineNumberReader has counted the
// line and unread only decrements the column, so a name that ends its line reports as
// ending at column 0 of the next one. End of input moves them the same way and leaves
// nothing to unread. These four are kept alongside instead, so that nothing existing
// shifts: the first pair moves only for a character that stays read, and unread rolls
// it back by the one step a single-character pushback can need.
private int _endLine = 1;
private int _endColumn = 1;
private int _prevEndLine = 1;
private int _prevEndColumn = 1;

public LineNumberingPushbackReader(Reader r){
	super(new LineNumberReader(r));
}

public LineNumberingPushbackReader(Reader r, int size){
	super(new LineNumberReader(r, size));
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

// The line and column just past the last character consumed. See the fields.
public int getEndLineNumber(){
	return _endLine;
}

public int getEndColumnNumber(){
	return _endColumn;
}

public int read() throws IOException{
    int c = super.read();
    _prev = _atLineStart;
    _prevEndLine = _endLine;
    _prevEndColumn = _endColumn;
    if((c == newline) || (c == -1))
        {
        _atLineStart = true;
        _columnNumber = 1;
        if(c == newline)
            {
            // Just past a newline is the start of the line it ended. No span is ever
            // taken here - every end is read at a token boundary, and a token never
            // ends on a newline it kept - but the pair means "just past the last
            // character consumed" and this is what keeps it meaning that. End of
            // input consumed nothing, so it moves nothing.
            _endLine = getLineNumber();
            _endColumn = 1;
            }
        }
    else
        {
        _atLineStart = false;
        _columnNumber++;
        _endLine = getLineNumber();
        _endColumn = _columnNumber;
        }
    if(sb != null && c != -1)
        sb.append((char)c);
    return c;
}

public void unread(int c) throws IOException{
    super.unread(c);
    _atLineStart = _prev;
    _columnNumber--;
    _endLine = _prevEndLine;
    _endColumn = _prevEndColumn;
    if(sb != null)
        sb.deleteCharAt(sb.length()-1);
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
        _prevEndLine = _endLine;
        _prevEndColumn = _endColumn;
        _endLine = getLineNumber();
        _endColumn = 1;
        break;
    }
    return line;
}

public boolean atLineStart(){
    return _atLineStart;
}
}
