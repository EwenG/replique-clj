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

import java.io.IOException;
import java.io.PushbackReader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.List;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A fast Clojure reader built on {@link Buffer}. Behaviour matches Clojure 1.12.5's original
 * LispReader, but tokens are scanned directly over the {@link Buffer} backing array rather than
 * character-by-character through a {@link PushbackReader}.
 *
 * <p>This class has two faces:
 *
 * <ul>
 *   <li>An <b>instance API</b> ({@link #LispReader(java.io.Reader)} + {@link #read()}) which owns
 *       its input and reads it in chunks. This is the fast path.
 *   <li>A <b>static API</b> ({@code read(PushbackReader, ...)}) preserving the signatures the rest
 *       of the runtime (Compiler, RT, clojure.core, clojure.main) calls. Because callers such as
 *       {@code clojure.main/repl-read} interleave their own {@code .read}/{@code .unread}/
 *       {@code .readLine} calls on the same stream, the static path must not consume more input
 *       than the form it returns: it reads with a chunk size of 1 and pushes any unconsumed
 *       lookahead back into the {@link PushbackReader}, so the stream is left positioned exactly
 *       where the original LispReader would have left it.
 * </ul>
 *
 * <p>Supported: numbers, symbols, keywords, strings, characters, {@code nil}/{@code true}/
 * {@code false}, collections, comments ({@code ;}, {@code #!}, {@code #_}), quote, deref, var,
 * unquote, metadata, symbolic values ({@code ##Inf}/{@code ##-Inf}/{@code ##NaN}), regex, tagged
 * literals, namespaced maps, syntax-quote (with auto-gensym), and the anonymous fn literal.
 *
 * <p>NOT YET SUPPORTED (see the TODOs at each site):
 * <ul>
 *   <li>{@code :line}/{@code :column} metadata on forms. {@link Buffer} already tracks line and
 *       column ({@code countLines}); the reader does not yet attach it. The Compiler degrades
 *       gracefully (it falls back to the reader's own line number), so stack traces still name the
 *       right top-level form, but inner forms and Var {@code :line} meta are missing.
 *   <li>Reader conditionals ({@code #?} / {@code #?@}) - {@code readDispatch} throws.
 *   <li>The {@code #=} eval reader - {@code *read-eval*} is honoured (which is the
 *       security-relevant half) but evaluating throws.
 *   <li>Record literals ({@code #my.Record[...]} / {@code #my.Record{...}}).
 *   <li>{@code *reader-resolver*} ({@link Resolver}) - the interface is kept for API
 *       compatibility but is not consulted.
 * </ul>
 * None of these are used by Clojure's own sources, so the fork bootstraps without them; they show
 * up in Clojure's test suite.
 */
public class LispReader {

  /** Returned by {@link #read()} at end of input. */
  public static final Object EOF = new Object();

  public static final int DEFAULT_CHUNK_SIZE = 4096;

  private final Buffer buffer;

  // Macro characters, matching the original LispReader's `macros` table (all ASCII).
  private static final boolean[] MACRO = new boolean[128];
  static {
    for (char c : new char[]{'"', ';', '\'', '@', '^', '`', '~',
                             '(', ')', '[', ']', '{', '}', '\\', '%', '#'}) {
      MACRO[c] = true;
    }
  }

  public LispReader(java.io.Reader r, int chunkSize) {
    this.buffer = new Buffer(r, chunkSize);
  }

  public LispReader(java.io.Reader r) {
    this(r, DEFAULT_CHUNK_SIZE);
  }

  // Reads from a Buffer someone else owns. This is how a LineNumberingPushbackReader hands us its
  // Buffer: we tokenize out of the same characters it serves to the REPL and the Compiler, sharing
  // one cursor, rather than draining it into a buffer of our own.
  LispReader(Buffer buffer) {
    this.buffer = buffer;
  }

  // Internal control-flow sentinels, mirroring the original read loop.
  private static final Object READ_EOF = new Object();       // end of input
  private static final Object READ_FINISHED = new Object();  // hit the expected closing delimiter
  private static final Object SKIP = new Object();           // no value (comment / discard); continue

  private static final Keyword UNKNOWN = Keyword.intern(null, "unknown");

  /** Reads one form, or returns {@link #EOF} at end of input. */
  public Object read() throws IOException {
    // The original guards the top of read() the same way: :unknown blocks everything.
    if (RT.READEVAL.deref() == UNKNOWN)
      throw Util.runtimeException("Reading disallowed - *read-eval* bound to :unknown");
    Object o = read0(0);
    return o == READ_EOF ? EOF : o;
  }

  // ---- Static API ---------------------------------------------------------------------------
  // The signatures the rest of the runtime calls. See the class doc for why the static path reads
  // one character at a time and pushes its lookahead back.

  public static interface Resolver {
    Symbol currentNS();
    Symbol resolveClass(Symbol sym);
    Symbol resolveAlias(Symbol sym);
    Symbol resolveVar(Symbol sym);
  }

  static boolean isWhitespace(int ch) {
    return ch < 128 ? (ch >= 0 && WS[ch]) : Character.isWhitespace(ch);
  }

  static void unread(PushbackReader r, int ch) {
    if (ch != -1)
      try {
        r.unread(ch);
      } catch (IOException e) {
        throw Util.sneakyThrow(e);
      }
  }

  public static class ReaderException extends RuntimeException implements IExceptionInfo {
    public final int line;
    public final int column;
    public final Object data;

    final static public String ERR_NS = "clojure.error";
    final static public Keyword ERR_LINE = Keyword.intern(ERR_NS, "line");
    final static public Keyword ERR_COLUMN = Keyword.intern(ERR_NS, "column");

    public ReaderException(int line, int column, Throwable cause) {
      super(cause);
      this.line = line;
      this.column = column;
      this.data = RT.map(ERR_LINE, line, ERR_COLUMN, column);
    }

    public IPersistentMap getData() {
      return (IPersistentMap) data;
    }
  }

  static public int read1(java.io.Reader r) {
    try {
      return r.read();
    } catch (IOException e) {
      throw Util.sneakyThrow(e);
    }
  }

  // Reader opts
  static public final Keyword OPT_EOF = Keyword.intern(null, "eof");
  static public final Keyword OPT_FEATURES = Keyword.intern(null, "features");
  static public final Keyword OPT_READ_COND = Keyword.intern(null, "read-cond");

  // EOF special value to throw on eof
  static public final Keyword EOFTHROW = Keyword.intern(null, "eofthrow");

  // Reader conditional options - use with :read-cond
  static public final Keyword COND_ALLOW = Keyword.intern(null, "allow");
  static public final Keyword COND_PRESERVE = Keyword.intern(null, "preserve");

  static public Object read(PushbackReader r, Object opts) {
    boolean eofIsError = true;
    Object eofValue = null;
    if (opts instanceof IPersistentMap) {
      Object eof = ((IPersistentMap) opts).valAt(OPT_EOF, EOFTHROW);
      if (!EOFTHROW.equals(eof)) {
        eofIsError = false;
        eofValue = eof;
      }
    }
    return read(r, eofIsError, eofValue, false, opts);
  }

  static public Object read(PushbackReader r, boolean eofIsError, Object eofValue, boolean isRecursive) {
    return read(r, eofIsError, eofValue, isRecursive, PersistentHashMap.EMPTY);
  }

  static public Object read(PushbackReader r, boolean eofIsError, Object eofValue, boolean isRecursive,
                            Object opts) {
    if (r instanceof LineNumberingPushbackReader) {
      // The fast path, and the one everything that matters takes: Compiler.load, clojure.main's
      // REPL, and RT.readReader all hand us a LineNumberingPushbackReader. We borrow its Buffer,
      // so reading ahead is free -- there is no second cursor to fall out of step with, and it
      // does not matter how much we buffer. The LispReader instance is cached on the reader, so
      // its token cache survives across every form in the file.
      LineNumberingPushbackReader lnpr = (LineNumberingPushbackReader) r;
      LispReader lr = lnpr.lispReader();
      try {
        Object o = lr.read();
        if (o == EOF) {
          if (eofIsError)
            throw Util.runtimeException("EOF while reading");
          return eofValue;
        }
        return o;
      } catch (Exception e) {
        if (isRecursive)
          throw Util.sneakyThrow(e);
        throw new ReaderException(lnpr.getLineNumber(), lnpr.getColumnNumber(), e);
      }
    }

    // Compat path: a PushbackReader we do not own, e.g. user code calling
    // (read (java.io.PushbackReader. rdr)). We cannot share a Buffer with it, and the caller may
    // well read it directly afterwards, so we must not consume past the form: read one character
    // at a time and push whatever lookahead is left back into it. Slow, but correct, and nothing
    // on a hot path arrives here.
    LispReader lr = new LispReader(new SingleCharReader(r), 1);
    try {
      Object o = lr.read();
      if (o == EOF) {
        if (eofIsError)
          throw Util.runtimeException("EOF while reading");
        return eofValue;
      }
      return o;
    } catch (Exception e) {
      throw Util.sneakyThrow(e);
    } finally {
      lr.pushBackLookahead(r);
    }
  }

  /**
   * Feeds a foreign Reader to a Buffer one character at a time, going through {@code read()} only.
   *
   * <p>Necessary because a foreign reader may not implement the array read at all.
   * {@code clojure.repl/source-fn} passes a {@code (proxy [PushbackReader] [rdr] (read [] ...))},
   * and a Clojure proxy routes EVERY overload of {@code read} to that single fn -- so calling
   * {@code read(char[],int,int)} on it blows up with an ArityException. The original LispReader
   * only ever called {@code read()}, so proxies like that worked; going through this shim keeps
   * them working.
   */
  private static final class SingleCharReader extends java.io.Reader {
    private final java.io.Reader in;

    SingleCharReader(java.io.Reader in) {
      this.in = in;
    }

    public int read(char[] cbuf, int off, int len) throws IOException {
      if (len <= 0)
        return 0;
      int c = in.read();
      if (c == -1)
        return -1;
      cbuf[off] = (char) c;
      return 1;
    }

    public void close() throws IOException {
      in.close();
    }
  }

  // Returns any buffered-but-unconsumed characters to `r`. With chunkSize 1 this is at most the
  // couple of characters of lookahead the scanners peeked at (a token delimiter, the character
  // after a leading +/-).
  private void pushBackLookahead(PushbackReader r) {
    int n = buffer.posEnd - buffer.pos;
    if (n <= 0)
      return;
    try {
      r.unread(buffer.buffer, buffer.pos, n);
    } catch (IOException e) {
      throw Util.sneakyThrow(e);
    }
  }

  /**
   * Reads a single form from a string. Unlike the {@link PushbackReader} path this owns its input,
   * so it reads in full chunks.
   */
  static public Object readString(String s, Object opts) {
    LispReader lr = new LispReader(new StringReader(s), DEFAULT_CHUNK_SIZE);
    try {
      Object o = lr.read();
      if (o == EOF) {
        boolean eofIsError = true;
        Object eofValue = null;
        if (opts instanceof IPersistentMap) {
          Object eof = ((IPersistentMap) opts).valAt(OPT_EOF, EOFTHROW);
          if (!EOFTHROW.equals(eof)) {
            eofIsError = false;
            eofValue = eof;
          }
        }
        if (eofIsError)
          throw Util.runtimeException("EOF while reading");
        return eofValue;
      }
      return o;
    } catch (IOException e) {
      throw Util.sneakyThrow(e);
    }
  }

  // ---- Reader core --------------------------------------------------------------------------

  // Reads one form. `returnOn` is the closing delimiter to stop on (0 = none): on it, consumes
  // the delimiter and returns READ_FINISHED. Returns READ_EOF at end of input. Loops over
  // comments and #_ discards (which produce no value), matching the original read loop.
  private Object read0(int returnOn) throws IOException {
    while (true) {
      int c1 = skipWhitespace();
      if (c1 == -1) return READ_EOF;
      if (returnOn != 0 && c1 == returnOn) { buffer.read(); return READ_FINISHED; }
      if (Character.isDigit(c1)) return readNumber();
      switch (c1) {
        case '"':  buffer.read(); return readStringForm();
        case '\\': buffer.read(); return readCharacterForm();
        case '(':  buffer.read(); return readList();
        case '[':  buffer.read(); return readVector();
        case '{':  buffer.read(); return readMap();
        case ')': case ']': case '}':
          throw Util.runtimeException("Unmatched delimiter: " + (char) c1);
        case ';':  buffer.read(); skipLine(); continue;         // line comment
        case '#':  { Object o = readDispatch(); if (o == SKIP) continue; return o; }
        case '\'': buffer.read(); return RT.list(QUOTE, readForm());              // 'x
        case '@':  buffer.read(); return RT.list(DEREF, readForm());             // @x
        case '~':  buffer.read(); return readUnquote();                          // ~x / ~@x
        case '^':  buffer.read(); return readMeta();                             // ^meta form
        case '%':  return argEnv != null ? readArg() : readToken();              // %/%n/%& in #(), else symbol
        case '`':  buffer.read(); return readSyntaxQuote();                      // `form
        default:   break;
      }
      // Every macro character has an explicit case above, so anything reaching here is a token.
      if ((c1 == '+' || c1 == '-') && Character.isDigit(peekAt(1))) return readNumber();
      return readToken();   // symbols, keywords, nil / true / false
    }
  }

  // Reads forms until the closing `delim`, collecting them. Port of readDelimitedList.
  private ArrayList<Object> readDelimitedList(int delim) throws IOException {
    ArrayList<Object> acc = new ArrayList<>();
    while (true) {
      Object form = read0(delim);
      if (form == READ_EOF) throw Util.runtimeException("EOF while reading");
      if (form == READ_FINISHED) return acc;
      acc.add(form);
    }
  }

  private Object readList() throws IOException {
    ArrayList<Object> a = readDelimitedList(')');
    return a.isEmpty() ? PersistentList.EMPTY : PersistentList.create(a);
  }

  private Object readVector() throws IOException {
    return LazilyPersistentVector.create(readDelimitedList(']'));
  }

  private Object readMap() throws IOException {
    Object[] a = readDelimitedList('}').toArray();
    if ((a.length & 1) == 1)
      throw Util.runtimeException("Map literal must contain an even number of forms");
    return RT.map(a);                       // RT.map does the duplicate-key check
  }

  private Object readSet() throws IOException {
    return PersistentHashSet.createWithCheck(readDelimitedList('}'));
  }

  // Symbols used by the wrapping macros.
  private static final Symbol QUOTE = Symbol.intern("quote");
  private static final Symbol THE_VAR = Symbol.intern("var");
  private static final Symbol DEREF = Symbol.intern("clojure.core", "deref");
  private static final Symbol UNQUOTE = Symbol.intern("clojure.core", "unquote");
  private static final Symbol UNQUOTE_SPLICING = Symbol.intern("clojure.core", "unquote-splicing");
  private static final Symbol SYM_INF = Symbol.intern("Inf");
  private static final Symbol SYM_NEG_INF = Symbol.intern("-Inf");
  private static final Symbol SYM_NAN = Symbol.intern("NaN");

  // Symbols used by #() and syntax-quote expansion.
  private static final Symbol FN = Symbol.intern("fn*");            // Compiler.FN
  private static final Symbol AMP = Symbol.intern("&");             // Compiler._AMP_
  private static final Symbol APPLY = Symbol.intern("clojure.core", "apply");
  private static final Symbol HASHMAP = Symbol.intern("clojure.core", "hash-map");
  private static final Symbol HASHSET = Symbol.intern("clojure.core", "hash-set");
  private static final Symbol VECTOR = Symbol.intern("clojure.core", "vector");
  private static final Symbol SEQ = Symbol.intern("clojure.core", "seq");
  private static final Symbol CONCAT = Symbol.intern("clojure.core", "concat");
  private static final Symbol LIST = Symbol.intern("clojure.core", "list");
  private static final Symbol WITH_META = Symbol.intern("clojure.core", "with-meta");
  private static final Keyword LINE_KEY = Keyword.intern(null, "line");
  private static final Keyword COLUMN_KEY = Keyword.intern(null, "column");

  // Per-read state for #() arg literals and syntax-quote auto-gensyms; null when not inside the
  // respective macro. These stand in for the original's ARG_ENV / GENSYM_ENV thread-local Vars;
  // because this reader is an instance rather than a pile of statics, they can just be fields.
  private java.util.TreeMap<Integer, Symbol> argEnv;       // #() arg map: n -> param symbol
  private java.util.HashMap<Symbol, Symbol> gensymEnv;     // syntax-quote foo# -> gensym

  // Reads a required form (end of input is an error), as the reader macros do.
  private Object readForm() throws IOException {
    Object o = read0(0);
    if (o == READ_EOF) throw Util.runtimeException("EOF while reading");
    return o;
  }

  // '~' just read: ~@form -> (unquote-splicing form), ~form -> (unquote form).
  private Object readUnquote() throws IOException {
    if (buffer.peek() == '@') { buffer.read(); return RT.list(UNQUOTE_SPLICING, readForm()); }
    return RT.list(UNQUOTE, readForm());
  }

  // ---- Anonymous fn #(...) and arg literals %, %n, %& -------------------------------------
  // The opening '(' has been consumed. Reads the body list (during which '%' literals register
  // themselves into argEnv), then builds (fn* [args] body). Nested #() is rejected.

  private Object readFn() throws IOException {
    if (argEnv != null) throw new IllegalStateException("Nested #()s are not allowed");
    java.util.TreeMap<Integer, Symbol> saved = argEnv;   // null
    argEnv = new java.util.TreeMap<>();
    try {
      Object form = readList();                          // reads to ')', registering % args
      PersistentVector args = PersistentVector.EMPTY;
      if (!argEnv.isEmpty()) {
        int higharg = argEnv.lastKey();                  // highest key (-1 sorts below positives)
        if (higharg > 0) {
          for (int i = 1; i <= higharg; i++) {
            Symbol sym = argEnv.get(i);
            if (sym == null) sym = garg(i);              // fill gaps, e.g. %2 without %1
            args = args.cons(sym);
          }
        }
        Symbol restsym = argEnv.get(-1);
        if (restsym != null) { args = args.cons(AMP); args = args.cons(restsym); }
      }
      return RT.list(FN, args, form);
    } finally {
      argEnv = saved;
    }
  }

  // A generated arg/param symbol, e.g. p1__42# or rest__43#.
  private static Symbol garg(int n) {
    return Symbol.intern(null, (n == -1 ? "rest" : ("p" + n)) + "__" + RT.nextID() + "#");
  }

  private Symbol registerArg(int n) {
    Symbol ret = argEnv.get(n);
    if (ret == null) { ret = garg(n); argEnv.put(n, ret); }
    return ret;
  }

  // '%' seen inside a #(); argEnv is non-null. Reads the token and interprets the arg literal.
  private Object readArg() throws IOException {
    // Scan the %-token and interpret it inline - no regex Matcher, no String. The grammar is
    // just %, %&, or %[1-9][0-9]* (the original's argPat), and arg literals can appear many times
    // in an arg-heavy #(), so this stays on the fast char[] path like the other token scanners.
    Buffer b = buffer;
    b.startNewToken();
    int p = b.pos;
    char[] a = b.buffer;
    while (true) {
      char c = a[p];
      if (c == Buffer.SENTINEL && p == b.posEnd) {
        b.pos = p;
        if (!b.refill()) { a = b.buffer; p = b.posEnd; break; }
        a = b.buffer; p = b.pos; continue;
      }
      if (isWhitespace(c) || isTerminatingMacro(c)) break;
      p++;
    }
    int start = b.getTokenStart();
    int len = p - start;
    b.pos = p;
    if (len == 1) return registerArg(1);                               // %
    if (len == 2 && a[start + 1] == '&') return registerArg(-1);       // %&
    char c1 = a[start + 1];
    if (c1 >= '1' && c1 <= '9') {                                      // %[1-9][0-9]*
      long n = c1 - '0';
      boolean digits = true;
      for (int i = start + 2; i < p; i++) {
        char d = a[i];
        if (d < '0' || d > '9') { digits = false; break; }
        n = n * 10 + (d - '0');
        if (n > Integer.MAX_VALUE)   // match Integer.parseInt's overflow (both throw)
          throw new NumberFormatException("For input string: \"" + new String(a, start + 1, len - 1) + "\"");
      }
      if (digits) return registerArg((int) n);
    }
    throw new IllegalStateException("arg literal must be %, %& or %integer");
  }

  // ---- Syntax-quote `form ------------------------------------------------------------------
  // A fresh auto-gensym map is scoped to each backquote, so nested `...` get independent foo#
  // gensyms. Symbol resolution matches Clojure exactly by calling Compiler.isSpecial /
  // Compiler.resolveSymbol directly (both package-private, and we are in clojure.lang).
  private Object readSyntaxQuote() throws IOException {
    java.util.HashMap<Symbol, Symbol> saved = gensymEnv;
    gensymEnv = new java.util.HashMap<>();
    try {
      return syntaxQuote(readForm());
    } finally {
      gensymEnv = saved;
    }
  }

  private Object syntaxQuote(Object form) {
    Object ret;
    if (Compiler.isSpecial(form)) {
      ret = RT.list(QUOTE, form);
    } else if (form instanceof Symbol) {
      Symbol sym = (Symbol) form;
      if (sym.getNamespace() == null && sym.getName().endsWith("#")) {
        // auto-gensym: foo# -> foo__N__auto__, stable within this syntax-quote
        if (gensymEnv == null) throw new IllegalStateException("Gensym literal not in syntax-quote");
        Symbol gs = gensymEnv.get(sym);
        if (gs == null) {
          gs = Symbol.intern(null, sym.getName().substring(0, sym.getName().length() - 1)
              + "__" + RT.nextID() + "__auto__");
          gensymEnv.put(sym, gs);
        }
        sym = gs;
      } else if (sym.getNamespace() == null && sym.getName().endsWith(".")) {
        Symbol csym = Symbol.intern(null, sym.getName().substring(0, sym.getName().length() - 1));
        csym = Compiler.resolveSymbol(csym);
        sym = Symbol.intern(null, csym.getName().concat("."));
      } else if (sym.getNamespace() == null && sym.getName().startsWith(".")) {
        // instance method name: leave as-is (quoted below)
      } else {
        Object maybeClass = null;
        if (sym.getNamespace() != null)
          maybeClass = currentNS().getMapping(Symbol.intern(null, sym.getNamespace()));
        if (maybeClass instanceof Class)
          sym = Symbol.intern(((Class) maybeClass).getName(), sym.getName());
        else
          sym = Compiler.resolveSymbol(sym);
      }
      ret = RT.list(QUOTE, sym);
    } else if (isUnquote(form)) {
      return RT.second(form);
    } else if (isUnquoteSplicing(form)) {
      throw new IllegalStateException("splice not in list");
    } else if (form instanceof IPersistentCollection) {
      if (form instanceof IRecord) {
        ret = form;
      } else if (form instanceof IPersistentMap) {
        IPersistentVector keyvals = flattenMap(form);
        ret = RT.list(APPLY, HASHMAP, RT.list(SEQ, RT.cons(CONCAT, sqExpandList(keyvals.seq()))));
      } else if (form instanceof IPersistentVector) {
        ret = RT.list(APPLY, VECTOR, RT.list(SEQ, RT.cons(CONCAT, sqExpandList(((IPersistentVector) form).seq()))));
      } else if (form instanceof IPersistentSet) {
        ret = RT.list(APPLY, HASHSET, RT.list(SEQ, RT.cons(CONCAT, sqExpandList(((IPersistentSet) form).seq()))));
      } else if (form instanceof ISeq || form instanceof IPersistentList) {
        ISeq seq = RT.seq(form);
        if (seq == null) ret = RT.cons(LIST, null);
        else ret = RT.list(SEQ, RT.cons(CONCAT, sqExpandList(seq)));
      } else {
        throw new UnsupportedOperationException("Unknown Collection type");
      }
    } else if (form instanceof Keyword || form instanceof Number
        || form instanceof Character || form instanceof String) {
      ret = form;
    } else {
      ret = RT.list(QUOTE, form);
    }

    if (form instanceof IObj && RT.meta(form) != null) {
      IPersistentMap newMeta = ((IObj) form).meta().without(LINE_KEY).without(COLUMN_KEY);
      if (newMeta.count() > 0)
        return RT.list(WITH_META, ret, syntaxQuote(((IObj) form).meta()));
    }
    return ret;
  }

  private ISeq sqExpandList(ISeq seq) {
    PersistentVector ret = PersistentVector.EMPTY;
    for (; seq != null; seq = seq.next()) {
      Object item = seq.first();
      if (isUnquote(item)) ret = ret.cons(RT.list(LIST, RT.second(item)));
      else if (isUnquoteSplicing(item)) ret = ret.cons(RT.second(item));
      else ret = ret.cons(RT.list(LIST, syntaxQuote(item)));
    }
    return ret.seq();
  }

  private static IPersistentVector flattenMap(Object form) {
    IPersistentVector keyvals = PersistentVector.EMPTY;
    for (ISeq s = RT.seq(form); s != null; s = s.next()) {
      IMapEntry e = (IMapEntry) s.first();
      keyvals = (IPersistentVector) keyvals.cons(e.key());
      keyvals = (IPersistentVector) keyvals.cons(e.val());
    }
    return keyvals;
  }

  private static boolean isUnquote(Object form) {
    return form instanceof ISeq && UNQUOTE.equals(RT.first(form));
  }

  private static boolean isUnquoteSplicing(Object form) {
    return form instanceof ISeq && UNQUOTE_SPLICING.equals(RT.first(form));
  }

  // Handles a form beginning with '#'. The leading '#' has NOT been consumed. Returns the
  // form, or SKIP for a no-value dispatch (#_, #!).
  private Object readDispatch() throws IOException {
    buffer.read();                          // consume '#'
    int ch = buffer.peek();                 // dispatch char (consumed below, except for tags)
    if (ch == -1) throw Util.runtimeException("EOF while reading character");
    switch (ch) {
      case '{': buffer.read(); return readSet();
      case '(': buffer.read(); return readFn();                          // #(...) anonymous fn
      case '_': {                           // discard the next form
        buffer.read();
        Object discarded = read0(0);
        if (discarded == READ_EOF) throw Util.runtimeException("EOF while reading");
        return SKIP;
      }
      case '!': buffer.read(); skipLine(); return SKIP;                 // shebang line comment
      case '\'': buffer.read(); return RT.list(THE_VAR, readForm());    // #'x -> (var x)
      case '"': buffer.read(); return readRegex();                      // #"..." regex
      case '#': buffer.read(); return readSymbolicValue();              // ##Inf / ##-Inf / ##NaN
      case '<': buffer.read(); throw Util.runtimeException("Unreadable form");
      case '?':
        // TODO reader conditionals (#? / #?@). Needs the :read-cond / :features opts threaded in
        // and a pendingForms queue for #?@ splicing. Nothing in Clojure's own sources uses them,
        // but the test suite and every .cljc file do.
        buffer.read(); throw Util.runtimeException("Conditional read not allowed");
      case '=': {                             // #= read-eval
        buffer.read();
        // The original checks *read-eval* before reading its form; false/nil throws exactly this.
        if (!RT.booleanCast(RT.READEVAL.deref()))
          throw Util.runtimeException("EvalReader not allowed when *read-eval* is false.");
        // TODO evaluate. The *read-eval* gating above is the security-relevant behaviour and
        // matches the original; actually evaluating needs Compiler.eval plus the Class/Var
        // special cases from the original EvalReader.
        throw new UnsupportedOperationException("#= read-eval is not implemented yet");
      }
      case ':': buffer.read(); return readNamespaceMap();               // #:ns{...} / #::{...}
      default:
        if (Character.isLetter(ch)) return readTagged();               // #tag form (leave the letter)
        throw new UnsupportedOperationException(
            "Unsupported dispatch macro '#" + (char) ch + "'");
    }
  }

  // #"..." - chars up to the closing quote; a backslash keeps the next char literally (so \d
  // stays \d for Pattern.compile).
  private Object readRegex() throws IOException {
    Buffer b = buffer;
    StringBuilder sb = new StringBuilder();
    while (true) {
      int ch = b.read();
      if (ch == '"') break;
      if (ch == -1) throw Util.runtimeException("EOF while reading regex");
      sb.append((char) ch);
      if (ch == '\\') {
        int ch2 = b.read();
        if (ch2 == -1) throw Util.runtimeException("EOF while reading regex");
        sb.append((char) ch2);
      }
    }
    return Pattern.compile(sb.toString());
  }

  // ## symbolic values.
  private Object readSymbolicValue() throws IOException {
    Object form = readForm();
    if (!(form instanceof Symbol)) throw Util.runtimeException("Invalid token: ##" + form);
    if (form.equals(SYM_INF)) return Double.POSITIVE_INFINITY;
    if (form.equals(SYM_NEG_INF)) return Double.NEGATIVE_INFINITY;
    if (form.equals(SYM_NAN)) return Double.NaN;
    throw Util.runtimeException("Unknown symbolic value: ##" + form);
  }

  // #tag form - reads the tag symbol and a form, then applies the matching data reader.
  private Object readTagged() throws IOException {
    Object tag = readForm();
    if (!(tag instanceof Symbol)) throw Util.runtimeException("Reader tag must be a symbol");
    Object form = readForm();
    IFn reader = dataReaderFor((Symbol) tag);
    if (reader != null) return reader.invoke(form);
    // No registered reader. Clojure routes tags whose *name* contains '.' to record
    // construction (TODO: not implemented); only plain tags fall back to
    // *default-data-reader-fn*, called as (f tag form). Guarding on the dot keeps dotted tags
    // from wrongly hitting it.
    if (!((Symbol) tag).getName().contains(".")) {
      IFn defaultReader = (IFn) RT.var("clojure.core", "*default-data-reader-fn*").deref();
      if (defaultReader != null) return defaultReader.invoke(tag, form);
    }
    throw Util.runtimeException("No reader function for tag " + tag);
  }

  // #:ns{...} / #::{...} / #::alias{...} - the leading "#:" has been consumed. Unqualified keys
  // get the namespace; keys with the "_" namespace become unqualified; already-qualified keys are
  // left alone.
  private Object readNamespaceMap() throws IOException {
    Buffer b = buffer;
    boolean auto = false;
    if (b.peek() == ':') { b.read(); auto = true; }   // #::

    Object osym = null;
    int nc = b.peek();
    if (nc == '{') {
      // no namespace symbol before the map (osym stays null)
    } else if (nc != -1 && isWhitespace(nc)) {
      int c = skipWhitespace();
      if (!(auto && c == '{'))
        throw Util.runtimeException("Namespaced map must specify a namespace");
    } else {
      osym = readForm();                              // the namespace symbol (or EOF -> error)
      if (skipWhitespace() != '{')
        throw Util.runtimeException("Namespaced map must specify a map");
    }

    String nsname;
    if (auto) {
      if (osym == null) {
        nsname = currentNS().getName().getName();
      } else if (osym instanceof Symbol && ((Symbol) osym).getNamespace() == null) {
        Namespace resolved = currentNS().lookupAlias(Symbol.intern(((Symbol) osym).getName()));
        if (resolved == null)
          throw Util.runtimeException("Unknown auto-resolved namespace alias: " + osym);
        nsname = resolved.getName().getName();
      } else {
        throw Util.runtimeException("Namespaced map must specify a valid namespace: " + osym);
      }
    } else if (osym instanceof Symbol && ((Symbol) osym).getNamespace() == null) {
      nsname = ((Symbol) osym).getName();
    } else {
      throw Util.runtimeException("Namespaced map must specify a valid namespace: " + osym);
    }

    b.read();                                          // consume '{'
    ArrayList<Object> kvs = readDelimitedList('}');
    if ((kvs.size() & 1) == 1)
      throw Util.runtimeException("Namespaced map literal must contain an even number of forms");
    Object[] out = new Object[kvs.size()];
    for (int i = 0; i < kvs.size(); i += 2) {
      out[i] = qualifyKey(kvs.get(i), nsname);
      out[i + 1] = kvs.get(i + 1);
    }
    return RT.map(out);                                // RT.map does the duplicate-key check
  }

  private static Object qualifyKey(Object key, String nsname) {
    if (key instanceof Keyword) {
      Keyword kw = (Keyword) key;
      if (kw.getNamespace() == null) return Keyword.intern(nsname, kw.getName());
      if (kw.getNamespace().equals("_")) return Keyword.intern(null, kw.getName());
      return key;
    }
    if (key instanceof Symbol) {
      Symbol sym = (Symbol) key;
      if (sym.getNamespace() == null) return Symbol.intern(nsname, sym.getName());
      if (sym.getNamespace().equals("_")) return Symbol.intern(null, sym.getName());
      return key;
    }
    return key;
  }

  // Looks up a data reader: *data-readers* first, then default-data-readers (#inst, #uuid).
  private static IFn dataReaderFor(Symbol tag) {
    Object r = RT.get(RT.var("clojure.core", "*data-readers*").deref(), tag);
    if (r == null) r = RT.get(RT.var("clojure.core", "default-data-readers").deref(), tag);
    return (IFn) r;
  }

  // ^meta form. TODO: attach source line/column here once the Buffer's line counting is wired up.
  private static final Keyword TAG_KEY = Keyword.intern(null, "tag");
  private static final Keyword PARAM_TAGS_KEY = Keyword.intern(null, "param-tags");

  private Object readMeta() throws IOException {
    Object meta = readForm();
    if (meta instanceof Symbol || meta instanceof String)
      meta = RT.map(TAG_KEY, meta);
    else if (meta instanceof Keyword)
      meta = RT.map(meta, Boolean.TRUE);
    else if (meta instanceof IPersistentVector)
      meta = RT.map(PARAM_TAGS_KEY, meta);
    else if (!(meta instanceof IPersistentMap))
      throw new IllegalArgumentException("Metadata must be Symbol,Keyword,String,Vector or Map");

    Object o = readForm();
    if (!(o instanceof IMeta))
      throw new IllegalArgumentException("Metadata can only be applied to IMetas");
    if (o instanceof IReference) {
      ((IReference) o).resetMeta((IPersistentMap) meta);
      return o;
    }
    IPersistentMap ometa = RT.meta(o);
    for (ISeq s = RT.seq(meta); s != null; s = s.next()) {
      IMapEntry e = (IMapEntry) s.first();
      ometa = (IPersistentMap) RT.assoc(ometa, e.getKey(), e.getValue());
    }
    return ((IObj) o).withMeta(ometa);
  }

  private void skipLine() throws IOException {
    Buffer b = buffer;
    while (true) {
      int c = b.read();
      if (c == -1 || c == '\n' || c == '\r') return;
    }
  }

  // ASCII whitespace (plus comma) lookup for the hot path; matches `ch == ',' ||
  // Character.isWhitespace(ch)` for ch < 128.
  private static final boolean[] WS = new boolean[128];
  static {
    WS[','] = true;
    for (int i = 0; i < 128; i++) if (Character.isWhitespace(i)) WS[i] = true;
  }

  private static boolean isMacro(int ch) {
    return ch >= 0 && ch < 128 && MACRO[ch];
  }

  // Terminating macros are all macros except #, ' and %: those three may appear inside a token,
  // so they don't terminate one.
  private static boolean isTerminatingMacro(int ch) {
    return ch != '#' && ch != '\'' && ch != '%' && isMacro(ch);
  }

  // Consumes leading whitespace; returns the next non-whitespace char (not consumed),
  // or -1 at end of input. Scans the backing array directly to avoid per-char peek/read.
  private int skipWhitespace() throws IOException {
    Buffer b = buffer;
    while (true) {
      char[] a = b.buffer;
      int p = b.pos, end = b.posEnd;
      while (p < end) {
        char c = a[p];
        if (!isWhitespace(c)) { b.pos = p; return c; }
        p++;
      }
      b.pos = p;
      if (!b.refill()) return -1;
    }
  }

  // Looks ahead `offset` characters past the current position without consuming.
  private int peekAt(int offset) throws IOException {
    Buffer b = buffer;
    while (b.pos + offset >= b.posEnd) {
      if (!b.refill()) return -1;
    }
    return b.buffer[b.pos + offset];
  }

  private Object readNumber() throws IOException {
    Buffer b = buffer;
    b.startNewToken();
    // Scan the token directly over the backing array, stopping at whitespace, a macro
    // character, or end of input.
    int p = b.pos;
    char[] a = b.buffer;
    while (true) {
      char c = a[p];
      if (c == Buffer.SENTINEL && p == b.posEnd) {   // maybe end of buffered input
        b.pos = p;
        if (!b.refill()) { a = b.buffer; p = b.posEnd; break; }  // EOF (refill may have compacted)
        a = b.buffer;                                 // may have grown
        p = b.pos;                                    // may have shifted (compaction)
        continue;
      }
      if (isWhitespace(c) || isMacro(c)) break;
      p++;
    }
    b.pos = p;

    int start = b.getTokenStart();
    int end = p;
    Object n = parseNumber(a, start, end);
    if (n == null) {
      throw new NumberFormatException("Invalid number: " + new String(a, start, end - start));
    }
    return n;
  }

  private Object readToken() throws IOException {
    Buffer b = buffer;
    b.startNewToken();
    // Scan the token directly, stopping at whitespace, a terminating macro, or end of
    // input. Note: #, ' and % do NOT terminate a token. Along the way, flag whether the token has
    // a '/' or a non-leading ':' - if not, it is a plain symbol/keyword and can skip the full
    // matchSymbol machinery.
    int ts = b.getTokenStart();
    int p = b.pos;
    char[] a = b.buffer;
    boolean special = false;
    while (true) {
      char c = a[p];
      if (c == Buffer.SENTINEL && p == b.posEnd) {
        b.pos = p;
        if (!b.refill()) { a = b.buffer; ts = b.getTokenStart(); p = b.posEnd; break; }
        a = b.buffer;
        ts = b.getTokenStart();
        p = b.pos;
        continue;
      }
      if (isWhitespace(c) || isTerminatingMacro(c)) break;
      if (c == '/' || (c == ':' && p != ts)) special = true;
      p++;
    }
    b.pos = p;
    return interpretToken(a, ts, p, special);
  }

  // Reads a string form (opening quote already consumed).
  private Object readStringForm() throws IOException {
    Buffer b = buffer;
    b.startNewToken();
    // Fast path: no escapes. The content stays contiguous in the buffer across refills,
    // so on the closing quote we can slice it out in one shot.
    int p = b.pos;
    char[] a = b.buffer;
    while (true) {
      char c = a[p];
      if (c == Buffer.SENTINEL && p == b.posEnd) {
        b.pos = p;
        if (!b.refill()) throw Util.runtimeException("EOF while reading string");
        a = b.buffer;
        p = b.pos;
        continue;
      }
      if (c == '"') {
        String s = new String(a, b.getTokenStart(), p - b.getTokenStart());
        b.pos = p + 1;               // consume closing quote
        return s;
      }
      if (c == '\\') break;          // an escape: switch to the in-place decode path
      p++;
    }
    // In-place decode path (first backslash reached). Each escape collapses into the buffer
    // *behind* the read cursor, so the finished string is still one contiguous slice - no
    // StringBuilder. This stays O(n): it writes decoded chars into the already-consumed prefix
    // rather than shifting the unscanned tail on every escape (which would be O(n^2)).
    b.pos = p;                                   // position the read cursor at the backslash
    int wOff = p - b.getTokenStart();            // the clean prefix is already in place
    while (true) {
      int ch = b.read();
      if (ch == '"')
        return new String(b.buffer, b.getTokenStart(), wOff);
      if (ch == -1)
        throw Util.runtimeException("EOF while reading string");
      if (ch == '\\')
        ch = readStringEscape();
      // Write index (tokenStart + wOff) always trails the read cursor once an escape has
      // shortened the content, so this never clobbers not-yet-read input.
      b.buffer[b.getTokenStart() + wOff] = (char) ch;
      wOff++;
    }
  }

  // Decodes one string escape (backslash already consumed), returning the resulting char.
  private char readStringEscape() throws IOException {
    Buffer b = buffer;
    int ch = b.read();
    if (ch == -1) throw Util.runtimeException("EOF while reading string");
    switch (ch) {
      case 't': return '\t';
      case 'r': return '\r';
      case 'n': return '\n';
      case '\\': return '\\';
      case '"': return '"';
      case 'b': return '\b';
      case 'f': return '\f';
      case 'u': {
        int d = b.read();
        if (Character.digit(d, 16) == -1)
          throw Util.runtimeException("Invalid unicode escape: \\u" + (char) d);
        return (char) readUnicodeChar(d, 16, 4, true);
      }
      default:
        if (Character.isDigit(ch)) {
          int uc = readUnicodeChar(ch, 8, 3, false);
          if (uc > 0377)
            throw Util.runtimeException("Octal escape sequence must be in range [0, 377].");
          return (char) uc;
        }
        throw Util.runtimeException("Unsupported escape character: \\" + (char) ch);
    }
  }

  // initch already read, reads up to length-1 more base-`base` digits, stopping (and leaving the
  // delimiter) on whitespace/macro/EOF.
  private int readUnicodeChar(int initch, int base, int length, boolean exact) throws IOException {
    Buffer b = buffer;
    int uc = Character.digit(initch, base);
    if (uc == -1) throw new IllegalArgumentException("Invalid digit: " + (char) initch);
    int i = 1;
    for (; i < length; i++) {
      int ch = b.peek();
      if (ch == -1 || isWhitespace(ch) || isMacro(ch)) break;   // leave delimiter unconsumed
      int d = Character.digit(ch, base);
      if (d == -1) throw new IllegalArgumentException("Invalid digit: " + (char) ch);
      b.read();
      uc = uc * base + d;
    }
    if (i != length && exact)
      throw Util.runtimeException("Invalid character length: " + i + ", should be: " + length);
    return uc;
  }

  // Reads a character form (backslash already consumed).
  private Object readCharacterForm() throws IOException {
    Buffer b = buffer;
    b.startNewToken();
    if (b.peek() == -1) throw Util.runtimeException("EOF while reading character");
    // The first char after '\' is always part of the token, even a macro or whitespace char.
    int p = b.pos + 1;
    char[] a = b.buffer;
    while (true) {
      char c = a[p];
      if (c == Buffer.SENTINEL && p == b.posEnd) {
        b.pos = p;
        if (!b.refill()) { a = b.buffer; p = b.posEnd; break; }  // EOF (refill may have compacted)
        a = b.buffer;
        p = b.pos;
        continue;
      }
      if (isWhitespace(c) || isTerminatingMacro(c)) break;
      p++;
    }
    b.pos = p;
    return interpretCharacter(new String(a, b.getTokenStart(), p - b.getTokenStart()));
  }

  private static Object interpretCharacter(String token) {
    int len = token.length();
    if (len == 1) return token.charAt(0);
    switch (token) {
      case "newline": return '\n';
      case "space": return ' ';
      case "tab": return '\t';
      case "backspace": return '\b';
      case "formfeed": return '\f';
      case "return": return '\r';
      default:
        char c0 = token.charAt(0);
        if (c0 == 'u') {
          char c = (char) readUnicodeChar(token, 1, 4, 16);
          if (c >= '\ud800' && c <= '\udfff')
            throw Util.runtimeException("Invalid character constant: \\u" + Integer.toString(c, 16));
          return c;
        }
        if (c0 == 'o') {
          int n = len - 1;
          if (n > 3)
            throw Util.runtimeException("Invalid octal escape sequence length: " + n);
          int uc = readUnicodeChar(token, 1, n, 8);
          if (uc > 0377)
            throw Util.runtimeException("Octal escape sequence must be in range [0, 377].");
          return (char) uc;
        }
        throw Util.runtimeException("Unsupported character: \\" + token);
    }
  }

  private static int readUnicodeChar(String token, int offset, int length, int base) {
    if (token.length() != offset + length)
      throw new IllegalArgumentException("Invalid unicode character: \\" + token);
    int uc = 0;
    for (int i = offset; i < offset + length; i++) {
      int d = Character.digit(token.charAt(i), base);
      if (d == -1)
        throw new IllegalArgumentException("Invalid digit: " + token.charAt(i));
      uc = uc * base + d;
    }
    return uc;
  }

  // nil / true / false, then symbol/keyword. `special` is true when the token contains a '/'
  // or a non-leading ':', which are the only cases needing the full matchSymbol logic; the
  // common plain symbol/keyword goes straight to Symbol.intern / Keyword.intern.
  private Object interpretToken(char[] a, int start, int end, boolean special) {
    int len = end - start;
    if (!special) {
      char c0 = a[start];
      if (c0 == ':') {
        if (len >= 2)   // plain keyword :name
          return internPlain(a, start, len, true);
        // ":" alone falls through to the full path (invalid token)
      } else {
        if (len == 3 && c0 == 'n' && a[start + 1] == 'i' && a[start + 2] == 'l')
          return null;
        if (len == 4 && c0 == 't' && a[start + 1] == 'r' && a[start + 2] == 'u' && a[start + 3] == 'e')
          return Boolean.TRUE;
        if (len == 5 && c0 == 'f' && a[start + 1] == 'a' && a[start + 2] == 'l'
            && a[start + 3] == 's' && a[start + 4] == 'e')
          return Boolean.FALSE;
        return internPlain(a, start, len, false);   // plain symbol
      }
    }
    String s = new String(a, start, len);
    Object ret = matchSymbol(s);
    if (ret != null) return ret;
    throw Util.runtimeException("Invalid token: " + s);
  }

  // Per-reader cache from a token's char range to its interned Symbol/Keyword, so a repeated
  // plain token (extremely common in real code) skips the String allocation and the
  // Symbol/Keyword intern. Lazily allocated; a hash collision just recomputes (still correct).
  // Keyed on the whole range including any leading ':', so symbols and keywords never collide.
  private char[][] tokKey;
  private Object[] tokVal;
  private int tokSeen;
  private static final int TOK_MASK = 1023;
  private static final int TOK_CACHE_AFTER = 32;   // don't allocate the cache for small reads

  private Object internPlain(char[] a, int start, int len, boolean keyword) {
    char[][] keys = tokKey;
    if (keys == null) {
      if (++tokSeen <= TOK_CACHE_AFTER)
        return keyword ? Keyword.intern(Symbol.intern(new String(a, start + 1, len - 1)))
                       : Symbol.intern(new String(a, start, len));
      keys = tokKey = new char[TOK_MASK + 1][];
      tokVal = new Object[TOK_MASK + 1];
    }
    int h = 0;
    for (int i = 0; i < len; i++) h = h * 31 + a[start + i];
    int idx = h & TOK_MASK;
    char[] k = keys[idx];
    if (k != null && k.length == len) {
      int i = 0;
      while (i < len && k[i] == a[start + i]) i++;
      if (i == len) return tokVal[idx];
    }
    Object v = keyword
        ? Keyword.intern(Symbol.intern(new String(a, start + 1, len - 1)))
        : Symbol.intern(new String(a, start, len));
    keys[idx] = java.util.Arrays.copyOfRange(a, start, start + len);
    tokVal[idx] = v;
    return v;
  }

  // Hand-rolled equivalent of the original matchSymbol, avoiding a regex on this hot path.
  // Reproduces, without allocating a Matcher:
  //   symbolPat      = [:]?([\D&&[^/]].*/)?(/|[\D&&[^/]][^/]*)
  //   arraySymbolPat = ([\D&&[^/:]].*)/([1-9])
  // plus the ::-autoresolve and validity checks. See symMatch for the greedy semantics.
  private static final int SYM_NO_MATCH = -1;
  private static final int SYM_NS_PRESENT = 1;      // group1 (namespace) present
  private static final int SYM_NS_COLON_SLASH = 2;  // group1 ends with ":/"

  private static Object matchSymbol(String s) {
    int n = s.length();
    // symbolPat's leading [:]? is greedy: try consuming a leading ':' first, then not.
    int r = (s.charAt(0) == ':') ? symMatch(s, 1) : SYM_NO_MATCH;
    if (r == SYM_NO_MATCH) r = symMatch(s, 0);

    if (r != SYM_NO_MATCH) {
      boolean nsPresent = (r & SYM_NS_PRESENT) != 0;
      boolean nsEndsColonSlash = (r & SYM_NS_COLON_SLASH) != 0;
      // (ns endsWith ":/") || (name endsWith ":") || (s contains "::" at index >= 1)
      if ((nsPresent && nsEndsColonSlash)
          || s.charAt(n - 1) == ':'
          || s.indexOf("::", 1) != -1)
        return null;
      if (n >= 2 && s.charAt(0) == ':' && s.charAt(1) == ':') {
        // ::-autoresolve, matching the original's null-Resolver path (as used by RT.readString):
        // ::ns/name resolves ns as an ALIAS of the current namespace only (no Namespace/find);
        // ::name resolves against the current namespace itself.
        Symbol ks = Symbol.intern(s.substring(2));
        Namespace kns;
        if (ks.getNamespace() != null)
          kns = currentNS().lookupAlias(Symbol.intern(ks.getNamespace()));
        else
          kns = currentNS();
        if (kns != null)
          return Keyword.intern(kns.name.getName(), ks.getName());
        return null;
      }
      boolean isKeyword = s.charAt(0) == ':';
      Symbol sym = Symbol.intern(isKeyword ? s.substring(1) : s);
      return isKeyword ? Keyword.intern(sym) : sym;
    }

    // arraySymbolPat: ([\D&&[^/:]].*)/([1-9]) - ns/N with N a single 1-9. The '/' and digit
    // are the last two chars; the first char is non-digit, non-'/', non-':'.
    if (n >= 3) {
      char last = s.charAt(n - 1);
      char c0 = s.charAt(0);
      if (last >= '1' && last <= '9' && s.charAt(n - 2) == '/'
          && !isDigit(c0) && c0 != '/' && c0 != ':')
        return Symbol.intern(s.substring(0, n - 2), s.substring(n - 1));
    }
    return null;
  }

  // Simulates symbolPat matching ([\D&&[^/]].*/)?(/|[\D&&[^/]][^/]*) against s[p0..], with the
  // regex's greedy .* (so group1, the namespace, extends to the LAST '/'). Returns SYM_NO_MATCH,
  // or SYM_NS_PRESENT/SYM_NS_COLON_SLASH flags (0 == matched with no namespace). Note \D means
  // "not [0-9]"; the token's first char is never a digit (the reader dispatches those to numbers).
  private static int symMatch(String s, int p0) {
    int n = s.length();
    if (p0 >= n) return SYM_NO_MATCH;                 // group2 needs at least one char
    char first = s.charAt(p0);
    int lastSlash = s.lastIndexOf('/');
    if (lastSlash < p0) lastSlash = -1;               // no '/' in s[p0..]

    if (lastSlash < 0) {                              // no namespace: group2 = s[p0..]
      return isDigit(first) ? SYM_NO_MATCH : 0;       // group2's first char must be non-digit
    }

    // Namespace present: group1 = [\D&&[^/]].*/ (first char non-digit, non-'/').
    if (first != '/' && !isDigit(first)) {
      // Greedy: group1 ends at the last '/', so group2 = s[lastSlash+1 ..].
      if (lastSlash + 1 < n && !isDigit(s.charAt(lastSlash + 1))) {
        int flags = SYM_NS_PRESENT;
        if (lastSlash - 1 >= p0 && s.charAt(lastSlash - 1) == ':')
          flags |= SYM_NS_COLON_SLASH;                // group1 ends with ":/"
        return flags;
      }
      // group2 invalid at the last '/'. The only productive backtrack is group2 = "/" (a
      // single trailing slash), which needs the token to end with "//".
      if (s.charAt(n - 1) == '/' && n - 2 >= p0 && s.charAt(n - 2) == '/') {
        int flags = SYM_NS_PRESENT;
        if (n - 3 >= p0 && s.charAt(n - 3) == ':')
          flags |= SYM_NS_COLON_SLASH;
        return flags;
      }
    }
    // No namespace: group2 can only be a lone "/".
    if (n - p0 == 1 && first == '/') return 0;
    return SYM_NO_MATCH;
  }

  private static Namespace currentNS() {
    return (Namespace) RT.CURRENT_NS.deref();
  }

  // Classifies and parses a number token directly, without regex, for the common
  // forms (decimal long, hex, octal, double). Delegates to matchNumber only for the
  // rarer tails: radix (NrDDD), ratios, N/M suffixes, over-long magnitudes, and
  // invalid tokens. Reproduces the original's pattern precedence exactly - in particular
  // that intPat is tried before floatPat, so a leading-zero integer ("08") is invalid
  // while a leading-zero float ("08.5") is a double.
  private static Object parseNumber(char[] a, int start, int end) {
    int i = start;
    boolean neg = false;
    char c0 = a[i];
    if (c0 == '+' || c0 == '-') { neg = (c0 == '-'); i++; }
    if (i >= end) return matchNumber(str(a, start, end));  // sign only (shouldn't happen)
    int bodyStart = i;
    char b0 = a[bodyStart];

    // A lone zero (with optional sign): 0, +0, -0.
    if (b0 == '0' && bodyStart + 1 == end) return 0L;

    if (b0 == '0') {
      // Hex: 0[xX][0-9A-Fa-f]+
      char b1 = a[bodyStart + 1];
      if (b1 == 'x' || b1 == 'X') {
        Long mag = parseMag(a, bodyStart + 2, end, 16);
        if (mag != null) return neg ? -mag : (long) mag;
        return matchNumber(str(a, start, end));            // empty/invalid/overflow/N
      }
      // A float can start with 0 ("0.5", "08.5", "0e3"); a plain integer starting with
      // 0 is octal ("0777") or invalid ("08"). Distinguish by the char after the digits.
      int j = bodyStart;
      while (j < end && isDigit(a[j])) j++;
      if (j < end && (a[j] == '.' || a[j] == 'e' || a[j] == 'E')) {
        if (isFloat(a, bodyStart, end)) return Double.parseDouble(str(a, start, end));
        return matchNumber(str(a, start, end));            // e.g. "1.5M", "1e"
      }
      Long mag = parseMag(a, bodyStart + 1, end, 8);        // octal 0[0-7]+
      if (mag != null) return neg ? -mag : (long) mag;
      return matchNumber(str(a, start, end));              // "08", "0N", "0/5", ...
    }

    // Leading digit 1-9: decimal integer, or a double, or a rarer form.
    int j = bodyStart;
    while (j < end && isDigit(a[j])) j++;
    if (j == end) {
      Long mag = parseMag(a, bodyStart, end, 10);           // [1-9][0-9]*
      if (mag != null) return neg ? -mag : (long) mag;
      return matchNumber(str(a, start, end));              // overflow -> BigInt
    }
    char cj = a[j];
    if (cj == '.' || cj == 'e' || cj == 'E') {
      if (isFloat(a, bodyStart, end)) return Double.parseDouble(str(a, start, end));
    }
    return matchNumber(str(a, start, end));                // radix, ratio, N, M, invalid
  }

  private static String str(char[] a, int start, int end) {
    return new String(a, start, end - start);
  }

  private static boolean isDigit(char c) {
    return c >= '0' && c <= '9';
  }

  private static int digitVal(char c, int base) {
    int d;
    if (c >= '0' && c <= '9') d = c - '0';
    else if (c >= 'a' && c <= 'f') d = c - 'a' + 10;
    else if (c >= 'A' && c <= 'F') d = c - 'A' + 10;
    else return -1;
    return d < base ? d : -1;
  }

  // Parses [i,end) as an unsigned magnitude in the given base (<= 16). Returns null if
  // any character is not a valid digit, the run is empty, or the value overflows a long
  // (in which case the caller falls back to matchNumber's BigInteger handling). A magnitude
  // that fits a long always has bitLength < 64, so it maps to Long just like Clojure does.
  private static Long parseMag(char[] a, int i, int end, int base) {
    if (i >= end) return null;
    long val = 0;
    for (; i < end; i++) {
      int d = digitVal(a[i], base);
      if (d < 0) return null;
      if (val > (Long.MAX_VALUE - d) / base) return null;  // overflow -> BigInt path
      val = val * base + d;
    }
    return val;
  }

  // True iff [i,end) matches floatPat's magnitude grammar: [0-9]+(\.[0-9]*)?([eE][-+]?[0-9]+)?
  // Only called once a '.' or exponent is known present, so it never accepts a bare integer
  // (which intPat would have claimed first).
  private static boolean isFloat(char[] a, int i, int end) {
    int ds = i;
    while (i < end && isDigit(a[i])) i++;
    if (i == ds) return false;                 // need at least one leading digit
    if (i < end && a[i] == '.') {
      i++;
      while (i < end && isDigit(a[i])) i++;
    }
    if (i < end && (a[i] == 'e' || a[i] == 'E')) {
      i++;
      if (i < end && (a[i] == '+' || a[i] == '-')) i++;
      int es = i;
      while (i < end && isDigit(a[i])) i++;
      if (i == es) return false;               // exponent needs at least one digit
    }
    return i == end;
  }

  // --- Faithful port of the original matchNumber ---

  private static final Pattern intPat =
      Pattern.compile("([-+]?)(?:(0)|([1-9][0-9]*)|0[xX]([0-9A-Fa-f]+)|0([0-7]+)|([1-9][0-9]?)[rR]([0-9A-Za-z]+)|0[0-9]+)(N)?");
  private static final Pattern ratioPat = Pattern.compile("([-+]?[0-9]+)/([0-9]+)");
  private static final Pattern floatPat = Pattern.compile("([-+]?[0-9]+(\\.[0-9]*)?([eE][-+]?[0-9]+)?)(M)?");

  private static Object matchNumber(String s) {
    Matcher m = intPat.matcher(s);
    if (m.matches()) {
      if (m.group(2) != null) {
        if (m.group(8) != null)
          return BigInt.ZERO;
        return Numbers.num(0);
      }
      boolean negate = m.group(1).equals("-");
      String n;
      int radix = 10;
      if ((n = m.group(3)) != null)
        radix = 10;
      else if ((n = m.group(4)) != null)
        radix = 16;
      else if ((n = m.group(5)) != null)
        radix = 8;
      else if ((n = m.group(7)) != null)
        radix = Integer.parseInt(m.group(6));
      if (n == null)
        return null;
      BigInteger bn = new BigInteger(n, radix);
      if (negate)
        bn = bn.negate();
      if (m.group(8) != null)
        return BigInt.fromBigInteger(bn);
      return bn.bitLength() < 64 ? Numbers.num(bn.longValue()) : BigInt.fromBigInteger(bn);
    }
    m = floatPat.matcher(s);
    if (m.matches()) {
      if (m.group(4) != null)
        return new BigDecimal(m.group(1));
      return Double.parseDouble(s);
    }
    m = ratioPat.matcher(s);
    if (m.matches()) {
      String numerator = m.group(1);
      if (numerator.startsWith("+"))
        numerator = numerator.substring(1);
      return Numbers.divide(
          Numbers.reduceBigInt(BigInt.fromBigInteger(new BigInteger(numerator))),
          Numbers.reduceBigInt(BigInt.fromBigInteger(new BigInteger(m.group(2)))));
    }
    return null;
  }
}
