# replique-clj

Clojure 1.12.5, vendored from the upstream `clojure-1.12.5` tag, with a self-contained Maven build.
The jar is published as `replique-clj/clojure:1.12.5-r1`, deliberately keeping the artifactId
`clojure`, so it can be dropped onto a classpath in place of `org.clojure/clojure`.

## What this is (and isn't)

- **This fork does not promise to stay byte-identical to upstream.** Divergence in `src` is on the
  table where it earns its keep. Judge a change on its merits — a benchmark, a bug, the vendored
  test suite passing — not on whether it perturbs the diff against the tag.
- **As it stands, `src` and `test` are unmodified** (`git diff clojure-1.12.5 -- src test` is
  empty), so behaviour is stock Clojure 1.12.5: the reader, the compiler, the numerics, source
  metadata (`:line` / `:column` on lists and `^meta` seqs). That is a description of the current
  state, not a constraint on future ones.
- **What differs today is the build** and the packaging (`groupId` / `version`). See
  [Build](#build) and [The build vs. upstream's](#the-build-vs-upstreams).

> **History.** An earlier iteration replaced the `LispReader` with a faster, `Buffer`-backed reader
> (ported from the sibling *lijeur* project). It was reverted, and the measurements say that was the
> right call on the merits: reading is only ~5% of AOT compile time, so even a 2.7× reader buys
> ~3.4% overall — macroexpansion (~24%) and analysis (~22%) are where the time actually goes. Not
> worth carrying a reader rewrite. The work lives in the git history if you want it back.

## Build

```
mvn install          # => target/clojure-1.12.5-r1.jar (+ a -sources.jar)
```

The load-bearing step is the bootstrap, and is worth understanding:

```
maven-compiler-plugin   src/jvm/**.java            -> target/classes
exec-maven-plugin       java -cp target/classes clojure.lang.Compile clojure.core …
                        ^ this JVM AOT-compiles clojure/core.clj and the rest of the standard
                          library into the jar. It runs the classes just built above.
maven-jar-plugin        target/classes + src/clj   -> clojure-1.12.5-r1.jar
```

`src/resources/clojure/version.properties` is a filtered template (`version=${version}`) that
`clojure.core` reads at load time to build `*clojure-version*`.

Core is AOT-compiled with **direct linking** on (`clojure.compiler.direct-linking`), as upstream
builds it. Mind the prefix: `Compiler.java` collects compiler options by scanning system properties
under `clojure.compiler.`, so the plausible-looking `clojure.compile.direct-linking` is silently
ignored and yields a jar with direct linking *off*. (This pom had exactly that typo, and shipped
non-direct-linked jars because of it.) The `clojure.compile.` prefix is a different, smaller thing —
`path`, `warn-on-reflection`, `unchecked-math` — read by `clojure.lang.Compile` itself. To check
which you got, disassemble a core fn: direct-linked call sites are `invokestatic … invokeStatic`,
non-direct-linked ones go through `Var.getRawRoot`.

`src/assembly/` (upstream's slim-jar and distribution descriptors) is vendored but unused — the
assembly plugin is not configured here. Wire it back up if you want those artifacts.

### Using the jar standalone

Clojure 1.12 pulls in `org.clojure/spec.alpha` and `org.clojure/core.specs.alpha` at boot, and this
jar does not bundle them. They are declared as dependencies (so downstream Maven/deps consumers get
them transitively), but if you run the jar directly you must put them on the classpath yourself:

```
java -cp clojure-1.12.5-r1.jar:spec.alpha.jar:core.specs.alpha.jar clojure.main
```

## The build, vs. upstream's

Upstream's `pom.xml` uses `maven-antrun-plugin` to shell out to a 215-line `build.xml` for the two
interesting steps (AOT-compiling `clojure.core`, and running the tests). That Ant hop is gone here:
`exec-maven-plugin` calls the same entry point (`clojure.lang.Compile`) directly, and `build.xml` is
not vendored. The result is a single, self-contained `pom.xml` — nothing to build the build.

## Running Clojure's test suite

Clojure's own test suite (`test/clojure/test_clojure/**`, vendored unmodified) runs through
upstream's own runner script, via a profile that is **not** bound to the default `test` phase:

```
mvn test -Pclojure-test     # 783 tests, 20448 assertions, 0 failures, 0 errors
```

Because the source is byte-identical to the tag, this behaves exactly as it does on upstream Clojure
1.12.5. (`mvn test` on its own runs the `test/java` JUnit tests — there are currently none, so it is
a no-op that just confirms the build.)

Three things about that profile are load-bearing, all of them things upstream's `build.xml` does and
an earlier version of this pom did not:

- **A subset of test namespaces is AOT-compiled first** (`aot-compile-tests`, mirroring upstream's
  `compile-tests` target). They are referenced by class name rather than required — `clj-1208`
  evaluates `(clojure.test_clojure.compilation.load_ns.x.)` — so loading them from source is not
  enough.
- **The suite runs in a forked JVM** (`exec:exec`, not `exec:java`). Two tests build a
  `clojure.asm.ClassReader` from a class *name*, which resolves through
  `ClassLoader.getSystemResourceAsStream`. Under `exec:java` the project classpath is a child
  classloader while the system classloader is Maven's own, so those classes are invisible.
- **`test/` is on the classpath as a directory**, and the working directory is the project root.
  `CLJ-1184-do-in-non-list-test` writes `test/clojure/bad_def_test.clj` at runtime and compiles it,
  so a copy staged into `target/` at `process-test-resources` time will not do.

`readme.txt` is upstream's Clojure readme, restored verbatim from the tag and distinct from this
file: `sequences/test-iteration` reads it from the working directory.

## Comparing against upstream Clojure

Clojure's repo is wired up as a second remote (push URL set to `DISABLED`, so nothing can be pushed
to clojure/clojure by accident). The vendored files sit at their upstream paths, so diffs line up
directly.

```
git diff clojure-1.12.5 -- src test    # what this fork changes in the source (today: nothing)
git diff clojure-1.12.5                 # the whole fork: the build, the packaging, this README
```

Keeping that first diff honest and small is the point — not because the source may never change,
but so that when it does, the change is legible against upstream.

### Keeping those diffs clean: line endings

The vendored files carry upstream's line endings. 15 upstream files are stored with CRLF
(`epl-v10.html`, `Sequential.java`, `ISeq.java`, `MapEntry.java`, …), and a machine with
`core.autocrlf=input` would normalize them to LF when git hashes the working tree — making 15 files
we never touched diff as *fully rewritten*, ~2,400 phantom lines drowning any real change.

`.gitattributes` sets `* -text`, which disables EOL conversion so those blobs keep matching
upstream's. Two things to know about it:

- It must stay committable. `.gitignore` had `/.gitattributes` on line 884 (it is a generated file
  in upstream's layout), which made git ignore it entirely; that line has been removed. If the
  `.gitignore` is ever regenerated, check that line does not come back.
- **If you edit one of those 15 CRLF files with an editor that saves LF, its diff balloons to the
  whole file.** Reconvert with:
  `python3 -c 'p="<file>"; d=open(p,"rb").read().replace(b"\r\n",b"\n").replace(b"\n",b"\r\n"); open(p,"wb").write(d)'`

Note that `git diff --ignore-cr-at-eol` is *not* a substitute: it only changes how hunks are
rendered, while the changed-*file* list (git's and IntelliJ's alike) is computed on blob equality —
so the files would still show up.

## Licence

Clojure is © Rich Hickey, distributed under the Eclipse Public License 1.0 (`epl-v10.html`), which
this fork inherits.
