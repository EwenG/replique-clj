# replique-clj

Clojure 1.12.5, vendored verbatim, with a self-contained Maven build.

The source tree — compiler, runtime, data structures, the `LispReader`, `clojure.core` and the rest
of the standard library — is **byte-identical to the upstream `clojure-1.12.5` tag**. The only thing
that differs is how it builds: a plain `pom.xml` instead of upstream's Maven-shells-out-to-Ant
arrangement. The jar is published as `replique-clj/clojure:1.12.5-r1`, deliberately keeping the
artifactId `clojure`, so it can be dropped onto a classpath in place of `org.clojure/clojure`.

## What this is (and isn't)

- **The behaviour is stock Clojure 1.12.5.** Nothing in `src` or `test` is modified —
  `git diff clojure-1.12.5 -- src test` is empty. The reader, the compiler, the numerics, source
  metadata (`:line` / `:column` on lists and `^meta` seqs) — all exactly upstream.
- **The difference is the build**, and the packaging (`groupId` / `version`). See
  [Build](#build) and [The build vs. upstream's](#the-build-vs-upstreams).

> **History.** An earlier iteration of this project replaced the `LispReader` with a faster,
> `Buffer`-backed reader (ported from the sibling *lijeur* project). That reader has been reverted
> to stock: the ~2.7× read speedup it bought was only a few percent of compile time, and keeping the
> tree byte-identical to upstream is worth more than the win. The reader work lives in the git
> history if you want it back.

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
mvn test -Pclojure-test
```

Because the source is byte-identical to the tag, this behaves exactly as it does on upstream Clojure
1.12.5. (`mvn test` on its own runs the `test/java` JUnit tests — there are currently none, so it is
a no-op that just confirms the build.)

## Comparing against upstream Clojure

Clojure's repo is wired up as a second remote (push URL set to `DISABLED`, so nothing can be pushed
to clojure/clojure by accident). The vendored files sit at their upstream paths, so diffs line up
directly.

```
git diff clojure-1.12.5 -- src test    # empty: the source is unmodified
git diff clojure-1.12.5                 # the fork = pom.xml + .gitattributes + this README
```

### Keeping those diffs clean: line endings

The vendored files are byte-identical to upstream, **including line endings**. 15 upstream files are
stored with CRLF (`epl-v10.html`, `Sequential.java`, `ISeq.java`, `MapEntry.java`, …), and a machine
with `core.autocrlf=input` would normalize them to LF when git hashes the working tree — making 15
files we never touched diff as *fully rewritten*, ~2,400 phantom lines drowning any real change.

`.gitattributes` sets `* -text`, which disables EOL conversion so blobs stay byte-identical to
upstream. Two things to know about it:

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
