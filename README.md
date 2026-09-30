# replique-clj

Clojure 1.12.5, vendored from the upstream `clojure-1.12.5` tag, with a self-contained Maven build.
The jar is published as `replique-clj/clojure:1.12.5-r1`, deliberately keeping the artifactId
`clojure`, so it can be dropped onto a classpath in place of `org.clojure/clojure`.

**Requires Java 21+**, unlike upstream 1.12.5, which runs on Java 8 — a deliberate modern-JVM
baseline (`maven.compiler.release=21`), not something the `src` diff forces: nothing in it needs
21 today. The fork targets current JVMs, and 1.12 is upstream's last release on a Java 8 floor. The
bytecode the *Clojure* compiler emits is unaffected — that stays pinned to `V1_8`, i.e. Java 8
class files; it is `clojure.lang.*` itself that is built for 21.

## What this is (and isn't)

- **This fork does not promise to stay byte-identical to upstream.** Divergence in `src` is on the
  table where it earns its keep. Judge a change on its merits — a benchmark, a bug, the vendored
  test suite passing — not on whether it perturbs the diff against the tag.
- **Behaviour is stock Clojure 1.12.5 with analysis off** (the default — see the second divergence
  below) — the reader, the numerics, source metadata (`:line` / `:column` on lists and `^meta`
  seqs) — with the compiler diverging as listed below.
- **The rest of the difference is the build** and the packaging (`groupId` / `version`). See
  [Build](#build) and [The build vs. upstream's](#the-build-vs-upstreams).

## Divergence from upstream

`git diff clojure-1.12.5 -- src test` lists it; `test` is untouched. Three divergences in `src`:
one small, measured compiler change; one larger — a gated, off-by-default analysis subsystem
(the bulk of the diff by line count); and three hooks that exist only so a compiler for another
target can be written against this runtime.

- **`Reflector.getMethods` caches `Class.getMethods()` in a `ClassValue`.** `Class.getMethods()`
  copies the whole public-method array *and every `Method` object in it* on every call, and the
  compiler calls it once per interop form it analyses — which made `Class.copyMethods` the single
  hottest leaf under `analyze`. Worth **~4%** of compile time (25 recompiles of a 3240-line
  namespace: 6296ms → 6033ms). It also speeds up runtime reflective calls, so unhinted code
  benefits at run time and not just at compile time.

  `ClassValue` is JDK 7+, so this change needs no particular baseline of its own. It keys on the
  `Class`, so a class redefined at the REPL is a distinct key rather than a stale hit, and entries
  are collected with the class instead of pinning its loader — which matters for a REPL that
  reloads namespaces all day.

  Caching gives up the isolation `Class.getMethods()` was paying for: the `Method` objects handed
  out are now shared instances, so a caller that mutated one (`setAccessible`) would affect every
  later caller. `getMethods` is therefore **package-private now, where upstream has it public** —
  every caller is `Compiler` or `Reflector` itself, none of which mutate them, so the shared
  instances cannot leave `clojure.lang`. Nothing the compiler emits calls `getMethods` (reflective
  call sites go to `Reflector.invokeInstanceMethod` / `invokeNoArgInstanceMember`), so this does
  not affect already-AOT-compiled code; it breaks only third-party code calling
  `clojure.lang.Reflector/getMethods` directly. If you upstream this, expect that narrowing to be
  the contentious part.

- **A compiler-integrated analysis & macro-aware reload subsystem** — the largest divergence by
  line count, and the one the two changes above don't mention: `clojure.analysis` (new),
  `clojure.lang.IAnalysisSink` (new), and gated taps in `Compiler.java` and `LispReader.java`. The
  compiler emits typed semantic events (var / local / class / keyword / Java member usages, var
  defs, macro-expansion edges, the clauses of an `ns` form and the calls of `require`) into a sink installed by binding `Compiler/ANALYSIS_SINK`; a Clojure-side
  model folds them into find-usages / jump-to-definition / unused-`require`-import-local queries and
  a **macro-aware stale reload** that recompiles the files a macro edit actually invalidates, in
  dependency order. It exists to let an in-process REPL tool inherit the *real* compiler's
  resolution instead of re-approximating it statically.

  **Off by default, gated on that one dynamic var.** When `ANALYSIS_SINK` is unbound — normal
  compilation, AOT, the REPL — every capture point is skipped and behaviour is byte-for-byte stock,
  which is what preserves the drop-in `org.clojure/clojure` property. The one measurable off-cost
  is a dynamic-var deref per datum in the reader (well under 1% of AOT; reading is ~5% of it), not
  the "null check only" the design doc claims for the *compiler* taps. Enabling analysis *runs* the
  code it analyses (top-level and macroexpansion side effects fire), so it is a dev tool, not a
  sandboxed linter. Full design, drivers, and known limitations (notably: macro-body line numbers
  shift under an active analysis load) are in
  [`doc/analysis-and-reload.md`](doc/analysis-and-reload.md), where the feature is still marked
  *in progress*.

With analysis off — the default, and how the vendored test suite runs — none of these change what
the compiler emits, and that suite passes unmodified.

### Speed without AOT

The Reflector cache above barely helps a REPL: it is only ~4%. Compiling a namespace from source is
dominated by analysis and macroexpansion, and the two things that actually move it are **not** code
changes:

```
-Dclojure.spec.skip-macros=true     # -15% cold, -18% on a warm recompile loop
-XX:SharedArchiveFile=app.jsa       # -10% cold; startup only, ~100ms per JVM launch
```

`Compiler.checkSpecs` — validating `defn` / `let` / `fn` forms against `core.specs.alpha` on every
macroexpansion — is **12.8% of all compile time**, and 52% of everything `macroexpand1` does. The
cost of skipping it is that a malformed `defn` gets you a raw compiler error rather than a spec
explanation. Together the two are ~-26% on a cold "boot + load a namespace" loop.

The AppCDS archive is fussy to produce. Dump it from a **minimal boot** on a **jars-only**
classpath — it refuses directories, and an archive dumped from a run that compiled code archives
the dynamically generated classes (16MB vs 9.7MB) and is worth nothing on replay:

```
java -XX:ArchiveClassesAtExit=app.jsa -cp <jars only> clojure.main -e nil
```

Appending entries to the runtime classpath is fine; a directory on the classpath changing after the
dump is not — the archive is then rejected at startup and you silently get no speedup. Check with
`-Xlog:cds=warning`: no "shared class paths mismatch" means it loaded.

> **History.** An earlier iteration replaced the `LispReader` with a faster, `Buffer`-backed reader
> (ported from the sibling *lijeur* project). It was reverted, and the measurements say that was the
> right call on the merits: reading is only ~5% of AOT compile time, so even a 2.7× reader buys
> ~3.4% overall — macroexpansion (~24%) and analysis (~22%) are where the time actually goes. Not
> worth carrying a reader rewrite. The work lives in the git history if you want it back.

- **Three hooks for a front end targeting another platform.** Small, off by default, and inert
  for anything that does not ask for them. The consumer is the sibling project
  [`../replique-cljs`](../replique-cljs) — a ClojureScript compiler built on this runtime — and
  its `doc/cljs-compiler.md` is where the design lives.

  **`clojure.lang.NamespaceWorld`** (new, ~90 lines) gives the namespace table an identity, so
  there can be more than one. Namespaces were always just symbol tables; a second world lets a
  front end intern its own vars in its own `clojure.string` without colliding with the JVM's.
  `NamespaceWorld.DEFAULT` holds the JVM's namespaces and is what `Namespace.find` /
  `findOrCreate` / `remove` / `all` — and therefore `find-ns`, `create-ns`, `remove-ns`, `all-ns`
  — address, so that path is unchanged and costs no indirection it did not already pay. A
  `Namespace` does **not** know which world it is in: every caller that resolves a symbol already
  holds the world explicitly, and a back-pointer would be a second source of truth to keep in
  agreement with the first.

  **`LispReader.PLATFORM_FEATURE`** is the reader conditional's platform key, as a dynamic var.
  Unbound it is `:clj`, which is what this runtime always reads with. A front end reading the same
  `.cljc` source for another target *binds* it to that target's keyword rather than adding one,
  because `readCondDelimited` takes the **first** matching feature in written order — leaving
  `:clj` in the set beside `:cljs` would make `#?(:clj a :cljs b)` always yield `a`.

  **`Compiler.RECORD_POSITIONS`** lets source positions be recorded without an analysis sink
  installed. Positions were already recorded whenever analysis was on; this separates *wanting the
  positions* from *having somewhere to report events*, which is what a front end needs — it reads
  with this runtime's reader and keeps the positions for its own source maps.

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

Needs a **Java 21+** runtime (see [Divergence from upstream](#divergence-from-upstream)); on an
older JVM `clojure.lang.Compiler` fails to initialise.

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
git diff clojure-1.12.5 -- src test    # what this fork changes in the source (the three divergences above)
git diff clojure-1.12.5                 # the whole fork: the source, the build, the packaging, this README
```

Keeping that first diff legible is the point — gated on `ANALYSIS_SINK` so the off-path stays stock,
and small outside the analysis subsystem — so that a change against upstream reads clearly.

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
