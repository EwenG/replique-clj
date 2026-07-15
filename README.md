# replique-clj

Clojure 1.12.5 with its Lisp reader replaced by the fast, `Buffer`-backed reader from the
[lijeur](../lijeur) project (`Reader2`).

Everything else — the compiler, the runtime, the data structures, `clojure.core` and the rest of
the standard library — is Clojure 1.12.5, vendored unmodified. The jar is built as
`replique-clj/clojure:1.12.5-r1`, deliberately keeping the artifactId `clojure`, so it can be
dropped onto a classpath in place of `org.clojure/clojure`.

## Status

The fork **bootstraps**: the new reader reads all of `clojure/core.clj` and the rest of the
standard library, AOT-compiles them, and produces a working jar and REPL.

```
mvn install          # => target/clojure-1.12.5-r1.jar, 77 reader tests green
```

Clojure's own test suite matches stock Clojure 1.12.5 assertion-for-assertion. The full reader
suite (`clojure.test-clojure.reader`, 7,795 assertions) passes, identical to stock; a broad sweep
of ~16 namespaces is 14,372 assertions, 0 failures on both fork and stock (the one "error" is a
missing-fixture artifact present on stock too). **The port is complete: every reader macro of
Clojure 1.12.5's `LispReader` is implemented, with byte-for-byte parity.**

## What changed vs. Clojure 1.12.5

Four files, plus the build:

| File | Change |
|---|---|
| `src/jvm/clojure/lang/LispReader.java` | Replaced wholesale by lijeur's `Reader2`, renamed to `LispReader`. |
| `src/jvm/clojure/lang/Buffer.java` | New — lijeur's `Buffer`, moved into `clojure.lang`. |
| `src/jvm/clojure/lang/LineNumberingPushbackReader.java` | Rewritten as a facade over one shared `Buffer` (see "Input plumbing"). |
| `src/jvm/clojure/lang/RT.java` | `readString` now takes the reader's chunked path instead of going through a `PushbackReader`. |

Two things fell out of moving the reader into `clojure.lang`:

- The reflection hack is gone. `Reader2` had to reflect on `Compiler.isSpecial` /
  `Compiler.resolveSymbol` (both package-private) to make syntax-quote resolve symbols exactly like
  Clojure. In the same package, those are just direct calls.
- The reader is an **instance**, not a pile of statics. `Reader2`'s `#()` arg map and its
  syntax-quote gensym map are plain fields instead of the `ARG_ENV` / `GENSYM_ENV` thread-local
  `Var`s.

### Input plumbing (the one non-obvious part)

**`Buffer` is the single place characters live.** Nothing else reads the underlying `Reader`:
`LispReader` tokenizes straight out of the backing array, and `LineNumberingPushbackReader` is a
thin facade over the same `Buffer`. One cursor, one line/column count.

That inversion is the whole design, and it exists because a chunked reader cannot coexist with a
second cursor. Stock Clojure builds `LineNumberingPushbackReader` out of a `LineNumberReader` plus
a `PushbackReader`'s pushback array, and `LispReader` then drains characters out of it one at a
time — fine only as long as the reader never buffers ahead. Buffer ahead with two cursors and three
things break at once:

- **Line numbers race.** The line counter advances when characters are *buffered*, not when they
  are *consumed*, so `Compiler.load` stamps every form with a line from the end of the chunk.
- **`read+string` over-captures**, because the capture buffer swallowed the whole chunk.
- **The REPL skips input**, because `clojure.main/repl-read` calls `.read` / `.unread` /
  `.readLine` on `*in*` directly and lands past the buffered block.

With one shared cursor none of that can happen, so the chunk size is free. `Buffer` counts lines
against the **consumed** position, and capture is a pin plus a slice — the source text is already
sitting contiguously in the buffer, so `read+string` copies nothing. `Buffer` also took over the
CR / LF / CRLF collapsing that `LineNumberReader` used to do (a string literal spanning a CRLF must
hold a bare `\n`), which it does once, in place, as it fills.

`LispReader` still has two faces:

- **Fast path** — handed a `LineNumberingPushbackReader`, it borrows that reader's `Buffer`. This
  is what `Compiler.load`, the REPL and `RT` all take. The `LispReader` instance is cached on the
  reader, so its interned-token cache survives a whole file load.
- **Compat path** — a foreign `PushbackReader` (user code doing `(read (PushbackReader. rdr))`).
  No shared `Buffer` is possible and the caller may read the stream itself afterwards, so this
  reads one character at a time and pushes the lookahead back, exactly as the original did. It also
  only ever calls the single-arg `read()`, because `clojure.repl/source-fn` hands us a
  `(proxy [PushbackReader] …)` that overrides only that one — and a Clojure proxy routes *every*
  `read` overload to it, so an array read blows up with an `ArityException`.

Reading all 719 forms of `core.clj`, via the path `Compiler.load` actually uses (same JVM, both
readers, source metadata on in both):

| | |
|---|---|
| stock Clojure 1.12.5 | 18.7 ms |
| this fork | **7.8 ms** |

### Source metadata

`:line` / `:column` are attached exactly where stock Clojure attaches them — on lists (`ListReader`)
and, for seqs, in `^meta` (`MetaReader`); vectors, maps and sets get none, which surprises people
but is upstream's behaviour. Positions come from the shared `Buffer`, which counts against the
consumed position, so they are right regardless of how far the reader has buffered ahead. Metadata
is only attached when reading from a `LineNumberingPushbackReader`, again matching upstream — which
is why `read-string` produces no `:line`.

This is what makes `(meta #'foo)`, `clojure.repl/source` and inner-form stack traces work.

### Reader conditionals

`#?` / `#?@` are supported, in both `:allow` and `:preserve` modes, so `.cljc` files read (and
`test.check`, shipped as `.cljc`, loads). `opts` (`:read-cond`, `:features`) is threaded through the
instance reader with the platform feature `:clj` installed, and `#?@` splices through a pending-forms
queue that `read0` drains before reading anything new. While a non-matching branch is discarded,
`*suppress-read*` is bound, so a `#js` or `#some.nonexistent.Record` literal in a dead branch is kept
as a `TaggedLiteral` rather than applied — matching stock Clojure exactly (verified against the
`clojure.test-clojure.reader` suite).

### Record literals

`#my.Record[v …]` (positional constructor) and `#my.Record{:k v …}` (map `create`) are supported,
gated on `*read-eval*` like the original. Unblocks `clojure.test-clojure.protocols` and
`clojure.test-clojure.def`.

### Deprecated metadata reader

`#^meta form` is the old spelling of `^meta form`; both route to the same metadata reader, as
upstream. Unblocks `clojure.test-clojure.evaluation`.

### `#=` eval reader

`#=form` evaluates at read time, gated on `*read-eval*` (false/nil throws before the form is even
read, as upstream). It is not a general `eval`: like the original it handles exactly the forms
`print-dup` and the Compiler's constant serialization emit — a class name, `(var ns/name)`, a
`(Ctor. …)` call, a static-member call, and a `(var-fn …)` application. This is reachable from
ordinary `eval` too, whenever a non-trivial constant (e.g. a function used as code) gets embedded
and round-tripped through `#=`.

### `*reader-resolver*`

A resolver bound to `*reader-resolver*` (`LispReader.Resolver`) overrides how `::keywords`,
`#::maps`, and syntax-quoted symbols resolve — the path ClojureScript's reader and similar tooling
use to read code for a namespace other than the one doing the reading. `RT.readString` and the
Compiler never bind one, so the default path (resolve against the current namespace) is what
normally runs. Diffed against the original reader with a resolver bound to both
(`ReaderResolverTest`), since Clojure's own suite does not cover it.

## Tests

`mvn test` runs the reader's own JUnit tests (86, green):

- `test/java/clojure/lang/LispReaderNumberTest.java` — ported from lijeur's `Reader2NumberTest`,
  plus differential tests for record construction and the `#^` metadata reader.
- `test/java/clojure/lang/BufferTest.java` — ported from lijeur's `BufferTest`.
- `test/java/clojure/lang/SharedBufferTest.java` — the shared-cursor invariants (source capture,
  line stability across escaped strings, bounded memory, reentrant reads).
- `test/java/clojure/lang/ReaderResolverTest.java` — `*reader-resolver*`, diffed against the oracle.
- `test/java/clojure/lang/OriginalLispReader.java` — **the oracle.**

That last file matters. These are *differential* tests: they assert the new reader reads exactly
what Clojure 1.12.5 reads — same value, same type, same metadata, same exceptions — at several
buffer chunk sizes, so the refill / compaction / growth paths get exercised too. In lijeur the
oracle was `RT.readString`; here `RT.readString` **is the reader under test**, so the tests would
have compared the reader against itself and passed vacuously. `OriginalLispReader` is upstream's
reader kept verbatim in test scope, purely to preserve that comparison. If the two disagree, the
new reader is wrong.

Clojure's own suite (currently red — see the gaps above; it is the driver for the remaining work):

```
mvn test -Pclojure-test
```

## Comparing against upstream Clojure

Clojure's repo is wired up as a second remote (push URL set to `DISABLED`, so nothing can be pushed
to clojure/clojure by accident). The vendored files sit at their upstream paths, so diffs line up
directly.

```
git diff clojure-1.12.5 -- src test    # exactly what we changed, and nothing else
git log clojure/master --oneline -- src/jvm/clojure/lang/LispReader.java   # upstream reader history
```

### Keeping those diffs clean: line endings

The vendored files are byte-identical to upstream, **including line endings**. 15 upstream files
are stored with CRLF (`epl-v10.html`, `Sequential.java`, `ISeq.java`, `MapEntry.java`, …), and this
machine has `core.autocrlf=input`, which would normalize them to LF when git hashes the working
tree — making 15 files we never touched diff as *fully rewritten*, ~2,400 phantom lines drowning
the real changes.

`.gitattributes` sets `* -text`, which disables EOL conversion so blobs stay byte-identical to
upstream. Two things to know about it:

- It must stay committable. `.gitignore` had `/.gitattributes` on line 884 (it is a generated
  file), which made git ignore it entirely; that line has been removed. If the `.gitignore` is ever
  regenerated, check that line does not come back.
- **If you edit one of those 15 CRLF files with an editor that saves LF, its diff balloons to the
  whole file.** `LineNumberingPushbackReader.java` is one of them, and is one of the files we
  change. Not fatal, just noise — reconvert with:
  `python3 -c 'p="<file>"; d=open(p,"rb").read().replace(b"\r\n",b"\n").replace(b"\n",b"\r\n"); open(p,"wb").write(d)'`

Note that `git diff --ignore-cr-at-eol` is *not* a substitute: it only changes how hunks are
rendered, while the changed-*file* list (git's and IntelliJ's alike) is computed on blob equality —
so the files would still show up.

## Build

The build is Maven, but **not** Clojure's Maven build. Upstream's `pom.xml` uses
`maven-antrun-plugin` to shell out to a 215-line `build.xml` for the two interesting steps
(AOT-compiling `clojure.core`, and running the tests). That Ant hop is gone; `exec-maven-plugin`
calls `clojure.lang.Compile` directly, and `build.xml` is not vendored.

The bootstrap is the load-bearing part, and is worth understanding:

```
maven-compiler-plugin   src/jvm/**.java            -> target/classes
exec-maven-plugin       java -cp target/classes clojure.lang.Compile clojure.core …
                        ^ this JVM runs the NEW reader, and uses it to read clojure/core.clj.
                          If the reader is broken, this is the step that fails.
maven-jar-plugin        target/classes + src/clj   -> clojure-1.12.5-r1.jar
```

`src/resources/clojure/version.properties` is a filtered template (`version=${version}`) that
`clojure.core` reads at load time to build `*clojure-version*`.

`src/assembly/` (upstream's slim-jar and distribution descriptors) is vendored but unused — the
assembly plugin is not configured here. Wire it back up if you want those artifacts.

## Licence

Clojure is © Rich Hickey, distributed under the Eclipse Public License 1.0 (`epl-v10.html`), which
this fork inherits.
