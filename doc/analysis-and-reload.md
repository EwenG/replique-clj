<!-- -*- mode: markdown ; mode: visual-line ; coding: utf-8 -*- -->

# Compiler-integrated analysis & macro-aware reload — design

Status: **in progress.** This document is the plan we build against.

Implementation progress (see §10 for the full sequence):
- **Layer 0 — done.** `clojure.lang.IAnalysisSink` + gated `Compiler.ANALYSIS_SINK`; var-def
  and var-usage taps; `clojure.analysis` model + query API (`run-analysis`, `find-usages`,
  `definition`). Cross-namespace find-usages works; zero-cost when off.
- **Layer 1 — done.** Gated reader capture attaches `:line/:column/:end-line/:end-column` to
  symbols (`LispReader.positionsRequested()` / `attachSourcePosition`); taps read the symbol's
  own span via `Compiler.symbolPosition`; the sink interface and model carry end positions.
  Multiple references in one form now resolve to distinct, editor-ready ranges.
- **Layer 2 — done.** All capture points, in five waves, each tested:
  - **A. Locals** — `registerLocal` + `analyzeSymbol` local branch; `localDef`/`localUsage`;
    `unused-locals` query. Synthetic (macro-introduced) locals filtered via `isSourceSymbol`.
  - **B. Keywords** — reader-side `keywordUsage` (keywords can't hold metadata); auto-resolved
    `::x`/`::alias/x` indexed fully-qualified; `find-keyword-usages`. A reader conditional's untaken branch (read under
    `*suppress-read*`) records nothing; a `#_` discard is still recorded.
  - **C. Interop** — `classUsage` from `HostExpr.maybeClass` + the two `analyzeSymbol` class
    branches; `(Foo. ...)` position carried through the constructor desugaring in `macroexpand1`
    (`carryClassPosition`). Covers `new`, type hints, static/instance members. `find-class-usages`.
    Also the interfaces a `deftype*`/`reify` names (`NewInstanceExpr.build`), which is where a
    type says what it is. A PROTOCOL is named in source and reaches the compiler as the interface
    it generated, so `clojure.core/parse-opts+specs` carries the written symbol's position onto
    the substituted one (`carry-position`, `carryClassPosition`'s shape) and the occurrence lands
    where the protocol is named; `find-usages` of a protocol merges in the class usages of its
    `:on-interface`, so "who implements this" is answered by the same query as "who calls it".
    The interfaces an expansion added - `reify`'s `IObj`, `defrecord`'s `IRecord` and the rest -
    carry no position and are not recorded, by the capture rule below.
    `proxy` is the one class reference no capture point can reach: it `resolve`s its bases
    while it expands and returns a form naming only the proxy class it generated, so it reports
    them itself from its own body (`Compiler/sinkProxyClasses`), the way `ns`, `import` and
    `destructure` do - otherwise an `:import` nothing but a `proxy` uses reads as unused.
  - **D. Macro edges** — `macroexpand1` tap emits `macroExpansion`, always feeding the
    `:macro-deps` compile-time dependency graph that drives §9 stale reload, and feeding
    `:usages` (macro calls bypass `analyzeSymbol`) only for source-written calls. `:inline`
    fns still TODO.
  - **Capture rule (all realms)** — a usage is recorded only where the name is textually
    present in source (`isSourceSymbol`); references a macro *emits* are captured once at the
    macro body (read-time `sinkSyntaxQuoteRef`), never re-recorded at expansion sites. See
    "The capture rule" under Layer 1.
  - **E. Requires/imports** — query-side, read from live namespace state (`ns-aliases`/
    `ns-refers`/`ns-imports`) combined with the usage model: `unused-aliases`, `unused-refers`,
    `unused-imports`. Bare `(require 'x)` with no `:as`/`:refer` leaves no per-ns trace, so it is
    not covered (documented limitation). An `:as` is asked of the **reader** as well
    (`qualifierUsage`, the `:qualifiers` facts): the namespace part of every qualified symbol
    read, at the place it is written. A macro that *eats* a qualified symbol at expansion time
    emits nothing naming the target, and one that rebuilds the body it was given (core.async's
    `go`) re-emits it fully qualified, so the alias reaches the compiler as something else or
    not at all — what the compiler can still say of such a name, that it is read and is
    *nowhere*, is the position-free `:ref-usages`/`:local-refs`. `unused-aliases` is the union
    of the two questions and not the spelling alone, because `::alias/k` is resolved in the
    reader and is only ever the keyword afterwards.

  Not yet done at that point: collection spans, `:inline`-fn compile-time edges.
- **§7 (provenance + retraction) — done, form-based.** Per-top-level-form provenance via
  `beginForm`/`endForm` wrapping read+eval in `Compiler.load` (so read-time keyword facts and
  eval-time facts share one form); each fact filed under its form's `[:index target span]`
  retraction list; `entity->form` drives retract-on-redefine; `source->forms` batches file
  ops. Drivers: `run-analysis`, `load-file!` (retract + reload), and `retract-file!` — all
  populated **from disk**, so the model stays in sync with the file and never reflects an
  un-saved REPL eval. Proven: locals no longer accumulate across reloads; a single-file reload
  preserves other files' usages of its vars. This also fixed the `:locals` lifecycle
  issue noted above.

- **File-centric, resource-keyed — done.** The reload/staleness unit is the **file**, keyed by
  the classpath-relative source path the compiler records (`"app/util.clj"`), not the namespace.
  A file is what an editor edits, and — the payoff — **one file may define several namespaces**;
  the file reload re-analyses all of them at once, which a require-by-namespace can't (it can't
  even *name* a file's second `(ns …)`). `load-file!` reloads by the file's **resource**
  (`load`), so it runs the whole file and records the same key `require` does for transitive
  deps (which the editor does not drive) — keeping the model consistent however a file entered
  it. Each form still keeps its `:ns` as metadata, so the per-namespace lints (unused-*) still
  work; `file-namespaces` lists the namespaces a file defines. `find-usages`/`definition` take a
  Var **or** its fully-qualified symbol (an editor has the name at a cursor, not a Var).

- **§9 (stale-reload + prune) — done, file-based.** Staleness is **mtime-based**:
  `snapshot-mtimes!` / `load-file!` record each file's source modification time in `:file-mtime`
  (the source path *is* the resource path — no namespace→path munging); `changed-files` flags a
  file whose current mtime differs from the baseline (edited since last loaded). `stale-files`
  then takes the **conservative** transitive closure over the **macro** dependency graph in file
  space (runtime call dependents are excluded — the precision tools.namespace lacks; but any
  edit to a macro-defining file marks its macro-dependent files stale, without distinguishing
  which form changed). `stale-reload!` reloads the stale set in macro-dependency (topological)
  order via `load-file!` (§9.2), optionally pruning; `prune-file!` ns-unmaps vars whose defining form
  vanished (across every namespace the file defines), warning (not blocking) on remaining usages.
  Proven end-to-end: editing a macro reloads its dependent *files* so they re-expand the new
  macro, reloading the macro's file *alone* does not update the dependent (the case a naive
  reload misses), and a removed var is pruned.

  Notes on the mtime choice: it reports a change whenever the file's timestamp moves — so a
  touch or save-without-edit can trigger a reload — and its resolution is milliseconds, so an
  edit within the same millisecond as the last load would be missed (not a concern in practice,
  since edits follow loads by far more than a ms). `not=` is used, so a backwards-moving mtime
  still counts as changed. (An earlier per-macro-source-hash *precise* variant was built and
  then reverted to this simpler mtime + conservative-closure scheme by request.)
- **Collection spans — done.** Vector/map/set literals (which carried no reader position at all)
  now get `:line/:column/:end-line/:end-column`, and lists gain end positions — all gated by
  analysis, so normal reads are unchanged (verified: no metadata when the sink is unbound).
  This completes Layer 1's position model for structural/editor use and binding-form diagnostics.

  Still not done (deliberately skipped): `:inline`-fn compile-time edges — an `:inline` fn change
  won't mark its callers stale. `:inline` is rare enough that this is left as a known gap.

## 1. Goal

Two capabilities, both built by teaching the real compiler to expose what it already
knows, rather than by writing a separate static analyzer:

1. **Semantic information for tooling** — enough to support clj-kondo-style features:
   find-usages, jump-to-definition, unused `require` / unused var / unused locals /
   unused import, unresolved-symbol, and more over time. Both **cross-namespace** and
   **per-file**. Consumed **in-process** by a tool (a REPL/nREPL-style server) that
   queries an in-memory model — not emitted to a file or database.

2. **Compile-time-aware stale reload** — a new reload operation that recompiles the files that
   are actually out of date, *including files that are stale only because a macro (or
   `:inline` fn) they expand changed, or because a class they name was generated again*,
   in dependency order — and can optionally prune
   vars that no longer exist in the source. Clojure's existing single-file reload is
   **kept unchanged** alongside it.

## 2. The core bet: observe the real compiler

clj-kondo, tools.analyzer, and LSP servers re-implement an *approximate* analysis of
Clojure source without running it. That forces them to hardcode knowledge of macros and
get it wrong for arbitrary user macros — macros are Turing-complete, so no static
analyzer can be correct in general.

The real compiler already does the thing they approximate:

- `Compiler.analyzeSymbol` (`src/jvm/clojure/lang/Compiler.java:7865`) resolves **every**
  symbol to a local, a var, a class, or a Java member. That resolution is ground truth.
- `Compiler.macroexpand1` (`Compiler.java:7566`) expands **every** macro call, so the
  compiler sees the true compile-time dependency edges — including macro-induced ones.

So we tap the compiler and inherit correctness for free, for arbitrary macros. That is the
entire reason to own a Clojure fork here.

**The cost we accept consciously:** analysis means *running* the compiler over the code,
which executes top-level and macro-expansion side effects. It is heavier than static
parsing and unsafe on untrusted input. For a personal/project dev tool this is fine; this
design is not a sandboxed linter.

## 3. Ground rules

- **Gated, zero-cost when off.** One dynamic var — `Compiler.ANALYSIS_SINK`, default
  `nil`. Every capture point is `if(sink != null) sink.record(...)`. Normal compilation,
  AOT, and the REPL pay one null check per event and nothing else. This is what lets the
  fork remain a drop-in `org.clojure/clojure` replacement, and it is the single most
  important constraint on the design. Do not add always-on state to hot classes (`Var`,
  `Symbol`) for this feature — see §5.
- **We are done being byte-identical to upstream.** This feature edits `Compiler.java` and
  `LispReader.java`. Keep the diff **minimal and gated** so upstream 1.12.x merges stay
  tractable, but the byte-identity property (asserted in the current README) no longer
  holds and that copy will need updating when this lands.
- **Runtime is the source of truth for definitions** — see §5.

## 4. Layered architecture

### Layer 0 — the gated event sink

`Compiler.ANALYSIS_SINK` (dynamic, default `nil`). A tool binds a sink, drives a
compile/load (§8), queries the resulting in-memory model (§7), and unbinds. Capture points
emit typed semantic events into the sink. Off by default ⇒ no behavioural or performance
change to normal use.

### Layer 1 — source positions (the prerequisite)

Precise per-node positions are required for find-usages / jump-to-definition, and today the
reader does **not** provide them for the nodes we care about:

- The reader attaches `:line`/`:column` only to **lists** (`LispReader.java:970`), never to
  bare symbols. A symbol read via `interpretToken → matchSymbol → Symbol.intern` carries no
  position. Correspondingly, `analyzeSymbol` falls back to `lineDeref()/columnDeref()` — the
  *enclosing form's* line — so today you cannot point at the exact `foo` in `(bar foo baz)`.

Plan: attach `:line/:column/:end-line/:end-column` at read time, gated by the analysis flag
so normal reads are unaffected in behaviour and speed. Scope:

- **Symbols** — required. This is what makes every referenceable feature precise.
- **Keywords** — required (see §6). Keyword position + resolution both happen in the reader.
- **Collections** — capture spans (cheap). Not referenceable, but the spans are needed to
  reach the symbols inside binding forms (for unused/shadowed locals) and to anchor
  form-level diagnostics (duplicate keys, etc.).
- **Literals** (numbers, strings, chars, `nil`, `true/false`, regex) — skip until a specific
  lint needs them. They have no reference identity, so find-usages is meaningless for them.

**Where the end of a span comes from.** Not from where the reader stands: a token is terminated
by reading one character past it and putting it back, and `LineNumberingPushbackReader.unread`
cannot give a newline back — the wrapped `LineNumberReader` has already counted the line, and
unread only decrements the column. Read that way, a name that ends its line ends at column 0 of
the next one, which no editor can highlight and no `subs` can cut. So the reader keeps a second
pair of coordinates beside the stock line and column — moved only by a character that stays read,
rolled back by `unread`, and exposed as `getEndLineNumber`/`getEndColumnNumber`. Every end
position is read from those; the stock pair is untouched, so nothing that was reading it shifts.
ClojureScript reads through the same `LispReader` (`clojure.cljs.reader`), so its spans are the
same spans.

**The capture rule: a usage is recorded exactly where the referenced name is textually
present in source.** Because positions are attached *in the reader*, only user-written nodes
carry them; symbols introduced by macroexpansion (gensyms, template plumbing, resolved
syntax-quote symbols) do not. So the rule is "record a usage only if the reference node
carries a read position" (`isSourceSymbol`), applied uniformly to vars, classes and macro
calls. Keywords need no gate: they are captured in the reader, so only literally-written ones
are ever seen. This gives one consistent semantics across realms:

- A var/class/keyword written in ordinary code → recorded at that spot.
- A reference the macro *emits* into its expansion (`` `(helper ...) ``) → recorded once, at
  the macro **body** where it is written — see the syntax-quote capture below — and **not**
  re-recorded at each call site (the expanded symbol has no read position, so the gate skips
  it). `find-usages` therefore never points at a call site where the name isn't textually
  present.
- The macro **var itself** at a direct call `(my-macro x)` *is* textually present → recorded.
  A macro emitting another macro call is not, so only the dependency edge is kept there (§9).

**Read-time capture of references inside syntax-quote.** A reference written inside a
`` `(...) `` template (typically a `defmacro` body) is *quoted*, so analysis never sees it as
a reference. `LispReader.syntaxQuote` therefore calls `Compiler.sinkSyntaxQuoteRef` when a
templated symbol resolves to an existing var or class, emitting the usage at the originally-
written position. Lookups are best-effort and never throw: a not-yet-defined (forward-
referenced) target is silently skipped (§12 TODO: deferred resolution closes this gap and
yields an unresolved-symbol lint).

*Interaction with Layer 1:* syntax-quote re-attaches a written symbol's remaining metadata to
the emitted symbol, and only skips this when the sole metadata is `:line`/`:column`. Layer 1
adds `:end-line`/`:end-column`, which would defeat that skip and stamp the macro-body position
onto every expanded symbol (making it look source-written and re-introducing the call-site
phantom). So syntax-quote also strips the end-position keys, and when analysis is on attaches
position-free metadata; with analysis off the behaviour is byte-identical to upstream. *Cost:*
this drops `:line`/`:column` from expanded code, so macro-body diagnostics lose line precision
under analysis — a known limitation, see §11.

De-risk by prototyping this layer first; without it, every feature degrades to form-level
precision and the value proposition changes.

### Layer 2 — capture points in the compiler

Few and centralized:

| Event | Where |
| --- | --- |
| var **usage** | `analyzeSymbol` var branch (`Compiler.java:7910`, the `registerVar(v); return new VarExpr(v)` path), gated on `isSourceSymbol` |
| var / class **usage in a syntax-quote body** | `LispReader.syntaxQuote` → `Compiler.sinkSyntaxQuoteRef`: templated references (macro bodies) captured at read time, positioned at the written symbol |
| var **usage at a var-quote** | `TheVarExpr.Parser.parse`: `#'a/b` resolves here and never reaches `analyzeSymbol`, so without this an `alter-var-root`, an `add-watch`, a `with-redefs` or a `binding` - whose expansion var-izes the very symbol the source wrote - records nothing. Gated on `isSourceSymbol`, positioned at the symbol rather than at the reader macro, so what a rename replaces is the name and the `#'` stays |
| local **usage** | `analyzeSymbol` local branch (`Compiler.java:7869`, `LocalBindingExpr`) |
| local **definition** (+ scope extent) | `registerLocal` (`Compiler.java:7313`); `let`/`loop`/`fn` parsers for scope entry/exit |
| var **definition** | `DefExpr.Parser.parse` (`Compiler.java:524`, already calls `registerVar`) |
| Java interop (class / field / method) | `StaticFieldExpr` / `QualifiedMethodExpr` branches in `analyzeSymbol`; host-method parsers |
| macro **usage** + compile-time edge | `macroexpand1` (`Compiler.java:7566`): always record the compile-time edge "this file depends on M"; record the "macro M used here" usage only for a source-written call (the macro name is textually present) |
| keyword usage | in the **reader**, at `::` resolution (`matchSymbol`) — see §6 |
| require / refer / alias / import | do **not** parse `ns` forms for what a namespace *has*; let them run, then read `Namespace` alias/mapping/refer state (authoritative; handles `ns`, bare `require`, `use`, dynamic requires uniformly). What a clause *writes* is another matter — see below |

**The names an `ns` form writes.** Reading the namespace's state says which vars it
refers and which classes it imports; it does not say where in the file those names are
written, and a `:refer [helper]` is a place `helper` is written — the place that makes the
short name mean that var, and one a rename has to rewrite along with the call sites. Neither
half reaches the capture points above: the specs are handed on QUOTED, so nothing in them is
ever resolved as a reference, and a quoted symbol loses its reader position when the form is
compiled, so by the time `refer` runs there is nothing left to say where the name was. So
both are captured while the form is EXPANDING, the last moment at which they exist:
`clojure.core/ns` hands the whole form to `IAnalysisSink.nsForm` and `clojure.core/import`
hands its specs to `Compiler.sinkImportSpecs`, each from its own macro body. `import` is
separate because it is also written on its own, and because its expansion has each class as
a string.

Nothing is resolved at that point — the target namespaces are not loaded yet, the `ns` form
is what loads them — so `clojure.analysis` qualifies each name by the libspec it is written
under and records it with `:declaration :refer` or `:declaration :import`. They join the
usages, because "where is this name written" is one list and a rename walks all of it; they
are marked, because a declaration is not a use; and `counts-as-use?` leaves them out, because
a refer or an import kept alive by its own mention is one the unused-* lints could never
report. `:exclude` is not among them: it names what the namespace will not be writing.

One rule cleans up after the last of those. A macro that DEFINES a name often
writes that same symbol again in its expansion - `defmacro` hands the name to
`(. (var name) (setMacro))` and then returns `(var name)` - and the copy carries
the reader's position, so it arrives as a var usage sitting exactly on the def.
`clojure.analysis`'s `drop-def-echoes!` drops a usage whose entity and position
match a def recorded **in the same form**: it is the definition seen twice, not a
use. Per form, so a var-quote of something defined elsewhere in the same file is
a real reference and is kept. `clojure.cljs.analysis` has the same rule, and had
it first - there a `deftype` expansion echoes the type's name.

Output: a stream of typed, positioned semantic events, tagged with provenance (§7.2).

### Layer 3 — in-memory model + query API

The sink folds events into a model (§7). Plain Clojure query functions a tool calls
in-process:

- **find-usages**(var|keyword) → usage sites
- **jump-to-definition**(position) → resolve to target → its definition site
- **unused require** — required ns with no usage of any of its vars
- **unused import** — imported class never resolved
- **unused private var** — def with empty usages (scope to private / non-exported to avoid
  false positives on public API; same limitation clj-kondo has — state it in results)
- **unused local** — binding with no recorded use
- **unresolved symbol** — the `UnresolvedVarExpr` path, per-ns bucket

Every named feature falls out of one model. "More clj-kondo-style features" = more event
*types* + more queries, not new architecture.

## 5. Runtime-as-truth, and where usages live

**Definitions are the runtime; usages are keyed by the runtime.**

- **Definitions** — do **not** build a parallel def index. `Namespace.getMappings()` already
  is the authoritative list of what's defined, and a var survives redefinition as the *same
  object*. "What's defined" is a live read of the runtime and cannot drift. This is exactly
  the requested "a var removed from source is not undefined unless explicitly undefined" — it
  is Clojure's existing semantics, and we inherit the stale-var problem, which §9 fixes.

- **Usages** — genuinely new information (the runtime discards "who calls whom"), so they must
  be stored somewhere new, but keyed by the live var identity so they stay in sync by
  construction: they die when the var is unmapped, survive when it's redefined, with no
  reconciliation step.

**Storage decision: a side `IdentityHashMap<Var, Usages>` held by the analysis session, not a
field on `Var`.** Same semantics as "usages on the var" (keyed by identity, survives redef,
cleared on unmap), but it exists only while analysis is active and touches nothing otherwise.
A field on `Var` would be a permanent structural change to one of the hottest classes in the
runtime, carried by every var in every JVM even when analysis is off — which violates §3. If
profiling ever shows the map lookup matters, promoting to a field is mechanical.

**Two directions are unavoidable.** A usage is an edge `(from-ns, position) → to-var`. We
index it **by target** (for find-usages) *and* **by source-ns** (for retraction — see §7).
Storing on/beside the target does not remove the need for the per-namespace outgoing journal;
it only decides where the *other* index lives.

**Not everything has a var.** The target-keyed store covers **vars** only. **Keywords** →
global `keyword → usages` map. **Locals** → per-ns/per-form. **Unresolved symbols** → per-ns
bucket. So "on the var" is right for the var case specifically, not a uniform mechanism.

> **Superseded — var key is the name, not the object.** The implementation keys `:usages` /
> `:defs` / `:entity->form` (and the `:macro-deps` macro key) by the var's **fully-qualified
> name symbol** (`my.ns/foo`), not by `Var` object identity — the sink converts each resolved
> `Var` via `var-key` at ingestion. Identity keying stranded a deleted var's references under a
> dead key when a later `def` minted a new `Var`, and pinned the dead `Var` (and its root) in
> memory. A name key is stable across unmap+redef, matches Clojure's late binding (callers
> re-resolve the name), and lets a deleted-but-referenced var live on as a **tombstone**
> (`:defs` entry with `:removed true`) so its dangling references stay findable until the last
> one is retracted, at which point the tombstone is GC'd (§9.3, `sweep-tombstones`).

## 6. What is referenceable

Split: **referenceable** (has identity → find-usages / jump-to-def) vs **anchorable**
(no identity → positions only buy diagnostics + editor navigation).

- **Symbols → vars / locals / classes / interop** — fully referenceable via `analyzeSymbol`.
  find-usages + jump-to-def both work. Classes resolve through `HostExpr.maybeClass` + the ns
  import map; find-usages of a class = every resolution site (imports, `Foo.`,
  `Foo/staticMethod`, `^Foo` hints, `instance?`); jump-to-def lands on the import (the class
  itself is Java). Enables **unused-import**.

- **Keywords → referenceable, but definition-less.** A keyword is a constant (`ConstantExpr`);
  the compiler never resolves it to a definition. So keyword support is **occurrence indexing
  by value**: find-usages yes, jump-to-def not intrinsically (unless we later add
  convention-based def sites — `s/def ::x`, `defmethod … ::x`, re-frame reg-* — which is
  heuristic, not ground truth). Auto-resolved keywords (`::x`, `::alias/x`) are resolved **in
  the reader** via the ns alias map, so keyword capture is a reader concern and we index by the
  **fully-qualified** keyword so `::foo` and `:this.ns/foo` unify.

- **Collections** — not referenceable. Their spans buy two things: (1) form-anchored
  diagnostics (duplicate map keys, duplicate set elements); (2) reaching the symbols *inside*
  binding vectors / destructuring maps, which is what makes precise unused/shadowed **local**
  analysis possible.

- **Literals** — no identity, no find-usages; skip until a specific lint asks.

### 6.1 Code the program does not run: `#_` and `(comment ...)`

Nothing here is compiled, so no capture point above sees it. It is still code someone
wrote and runs at the REPL, so find-usages and rename have to see it. It is **resolved,
not compiled**:

- **Getting the form.** The sink's `deadForm(form, kind, ns, source)` (a default method)
  receives it from two places. `LispReader.DiscardReader` sends the discarded form
  (`:discard`), except under `*suppress-read*`: the branch of a reader conditional that
  this platform does not take is another platform's code, the same rule `keywordUsage`
  follows. `Compiler.macroexpand1` sends the whole form when the macro is
  `clojure.core/comment` (`:comment`), nested ones included.
- **Resolving it.** The sink keeps the forms on the file frame. When the file ends,
  `walk-dead-code` resolves every symbol the reader wrote (one with `:line`) in the
  namespace current where the form is written. Resolving at the end of the file means
  that defs and requires written after a rich comment block are found. There is no
  macroexpansion, no eval, no interning and no class initialisation, and code that no
  longer compiles raises no error.
- **Locals.** Without macroexpansion, locals are found by knowing the binding forms of
  `clojure.core` and destructuring (`let`, `fn`, `loop`, `for`, `doseq`, `letfn`,
  `deftype`, `reify`, `catch`, ...). This is exact for those forms and a guess for any
  other macro that binds a name. The locals of the live code around a dead form (a `#_`
  inside a `defn`) come from the top-level form's own local facts: a name bound earlier
  in the same form is taken to be that local.
- **Facts.** The walk produces var usages and class usages marked `:dead :discard` or
  `:dead :comment`, and files them on one extra form per file. It produces no defs (a def
  in a comment must not keep a deleted var from being pruned), no local facts and no
  macro edges. Dead usages play no part in the compile graphs, the reload order or
  prune's warnings.
- **What the reader reports inside.** A keyword or a syntax-quoted reference inside dead
  code is reported by the reader while it reads it, as live. `deadForm` also carries the
  dead span. For `#_` the span is taken off the reader, because a discarded syntax-quote
  arrives as its expansion and a keyword holds no metadata. For a comment it starts after
  the `comment` symbol, which is a live call. When the top-level form ends, `close-dead!`
  marks the form's usages, class usages and keyword usages that lie inside a span as
  `:dead`; the innermost span wins.
- **Who counts them.** find-usages returns them, with `:dead`. The `unused-*` lints count
  a use in a `comment` (a rich comment block is REPL code, and dropping its require
  breaks it; clj-kondo counts it too) but not one in a `#_` (`counts-as-use?`).

`clojure.cljs.analysis` uses the same walk with its own resolution (a ClojureScript var,
or a macro for a call head).

## 7. The shared mechanism: provenance + generation

Single-ns reload, stale recompile, and prune are all "namespace **N** is being recompiled;
replace whatever N contributed last time with whatever it contributes now." The trap: N's
contributions are **scattered across other namespaces' data** (usages are stored on the target
var), and we must retract exactly N's old contributions without disturbing anything else. This
is the load-bearing bookkeeping; get the boundaries wrong and find-usages / unused-var queries
silently drift over a long session.

### 7.1 Worked example

`app.core` calls `app.util/parse` three times. With usages keyed by target, those three
records live on **`app.util/parse`'s** usage list, not on `app.core`. Edit `app.core` to call
`parse` once and reload it. To keep the model correct we must:

1. remove the **old three** usages on `app.util/parse` **that came from `app.core`** — while
   leaving usages of `parse` from `app.other` untouched, and leaving all of `app.util`'s own
   facts untouched; then
2. add the **new one**.

### 7.2 Provenance

Every recorded fact (def, usage, macro-edge, import, keyword usage) carries **who produced
it**: the source ns/file, and the **defining top-level form** (identity/position) it came
from. Provenance does double duty:

- **Retraction** — "which usages did `app.core` produce" (step 1 above).
- **Prune** — "which vars did the form at line 12 define" (§9), which is also how one form that
  mints many vars (`defprotocol`, `defrecord`/`deftype`, `defmulti`) is handled correctly —
  name-set diffing gets these wrong.

### 7.3 The retraction unit is the top-level form

The unit of provenance and retraction is the **top-level form**, not the namespace. Each
top-level form analysed gets a **form id** (`fid`, a monotonic counter assigned at the form
boundary), and every fact it produces is filed under that fid in `forms[fid].facts` — an exact
list of `[:index target span]` retraction instructions. Retracting a form is then O(its own
facts): replay the list, `disj`/`dissoc` each entry, drop empty sets. No global sweep, no
per-fact generation stamp needed — the form's own fact-list *is* the generation record.

A **file** operation is just a batch over its forms: `source->forms[F]` holds the fids whose
source is file F, so reloading F is "retract every fid in `source->forms[F]`, then load fresh."
Form granularity subsumes file granularity — one mechanism, and file-load / stale-load are
batches of form-loads (see §8). (The index keys on the file, not the namespace, because a file
is the editor's unit and may hold several namespaces; each form keeps its `:ns` as metadata.)

**The active-form stack is per-thread, not part of the shared model.** "Which form am I inside"
(the stack that `begin-form!`/`end-form!` push and pop, and that every fact reads via
`current-fid`) is held in a thread-local (`*form-stack*`), bound to a fresh atom by `with-sink`
for the duration of each analysis. This matches the sink binding, which is already thread-local:
only the recorded facts — and `:next-fid`, the global unique-id source — live in the shared
`model` atom. So two analyses running on different threads cannot stamp facts with each other's
form ids (they'd only ever contend on the model atom's atomic `swap!`, which is safe), and off-
thread callbacks with no binding just yield a nil fid — facts recorded without provenance, never
misattributed. Fid allocation stays global (an atomic bump of `:next-fid`) so ids are unique
across threads.

**Recognising "the same form" across re-evals.** Retraction must match a re-eval to the prior
version of the same logical form. Position is fragile (edits shift it), so the key is **what the
form defines**: an `entity->form` index maps each defined var to the fid that currently defines
it. When a new form's `varDef` fires for a var already in `entity->form`, the prior fid is
retracted first (retract-on-redefine), then the new def installs. This is position-independent —
re-evaluating `(defn foo …)` finds and replaces foo's prior form wherever it moved to — and it
handles multi-var forms (`defprotocol`) because the first def retracts the whole prior form,
clearing all its entity links, so the remaining defs re-file cleanly under the new fid. Forms
that define nothing (bare expressions) have no entity key; a driver may pass an explicit form id
or fall back to position, and otherwise their facts are replaced only on a full ns retract.

Retract-on-redefine is also exactly what fixes locals accumulation (the ephemeral-`LocalBinding`
issue): a re-eval'd `defn` drops its prior binding entries before recording the new ones.

### 7.4 The invariant that keeps global queries honest

**"unused var V" is a global fold: no namespace anywhere holds a usage of V.** As long as each
form-load keeps that form's slice *current and complete* (via 7.2 + 7.3), the fold stays
correct **without ever rebuilding the whole model**. Same for unused-require and unused-import.
This is the one property to protect.

Consequence to design around: a single reload can *change verdicts in other namespaces* (delete
N's only call to `other/foo` and `other/foo` becomes unused). That is correct and desired — but
it means the query API must be **"ask the model,"** never "return diagnostics for the file I
just compiled."

**Sub-invariant: everything recorded is retractable.** A fact is written to the query index
*only* when a form is open (`current-fid` non-nil), because that is the only time there is a
form to file its undo-record under. If the sink fires with no form open — a bare `eval` under
`run-analysis`, outside any `beginForm`/`endForm` window — the recording is a **no-op**, not a
half-write. Otherwise the index entry would exist with no undo-record and no retraction could
ever remove it (a permanent ghost), and a `def` would additionally scribble a bogus `[:forms
nil]` entry. Nothing real is lost: `load` / `require` always open a form; only an unsupported
bare-eval lands here, and it was never retractable anyway.

## 8. Drivers (what triggers analysis)

The sink and capture points are identical across all drivers; only the **scope** and the
**model-update semantics** differ. Every driver ultimately runs the same per-form boundary
(`beginForm`/`endForm` around each top-level `eval`), so they compose out of one primitive:
**form-load** = "analyse one top-level form; retract its prior version's facts; install the new
ones."

Every driver reads **from disk**. There is deliberately no single-form / REPL-eval driver: the
model is meant to stay in sync with what is written on disk, so an un-saved REPL eval (a scratch
`def`, a form evaluated from the editor before saving) never enters it. The finest exposed
granularity is therefore the **file** (`load-file!`); the per-form primitive above is an
internal building block, not an operation on its own. Analysis of an edited form lands when its
file is saved and reloaded.

The unit is the file, keyed by its classpath-relative source path, and a file is reloaded by its
**resource** (`load "/app/util"`), never require-by-namespace. That is what lets a file defining
several namespaces reload as one unit (require can't name a file's second `(ns …)`), and it
records the same source key `require` uses for transitive deps — so however a file first entered
the model (cold `require`, or an editor `load-file!`), its key is the same and retraction matches.

- **Cold load → full-project analysis.** Clean slate; the model is built from empty as every file
  loads (via `require` of the entry namespaces, which pulls transitive deps in dependency order),
  each form a form-load. The only run where cross-file completeness is trivially guaranteed — the
  correctness baseline / rebuild button.
- **Single-file load → single-file analysis.** Batch of form-loads over the file: retract every
  fid in `source->forms[F]` (dropping defs removed from source and stale non-def forms), then
  `load` F's resource fresh — re-analysing every namespace the file defines. **Preserves every
  other file's usages of F's vars**, because those live under *their* forms, not F's.
- **Stale-files load → stale-files analysis.** Compute the macro-aware stale set (§9), reload it
  in topological order, each file a single-file load.

### 8.1 Saying what was defined — the `*defined*` channel

A tool on top of this wants a second question answered, and it is not a question about
the model: **which code did that evaluation replace?** A program whose top level built
something — a UI tree, a websocket, a timer — has to be told when the definitions under
it were replaced, and no query over the model can say so, because the model is a picture
of what is on disk rather than a log of what just happened.

`*defined*` is that channel, and it is a function var like `*reload-progress*`. The sink
calls it for every `def` the compiler analyses; `prune-vars!` calls it for every var a
reload takes away:

```clojure
{:dialect :clj :op :define :ns my.app :var my.app/render :source "my/app.clj"}
{:dialect :clj :op :remove :ns my.app :var my.app/gone}
```

Three things make it worth stating separately from everything above.

**It is told outside the §7.4 invariant.** Every other sink method is a no-op when no form
is open, because a fact with no form to belong to could never be retracted. `*defined*`
reports nothing to the model and has nothing to retract, so it is told first and
unconditionally — which is exactly what makes a `def` typed at a REPL, inside no file,
reportable at all. That case is the whole point: fixing one function without reloading
its file is what a REPL is for.

**`defining*` installs a sink only when there is none**, with `*file-stack*` and
`*form-stack*` left unbound. Every model-writing method is then a no-op (each is gated on
a nil-safe `current-frame` / `current-form`), so wrapping an arbitrary evaluation in it
reports what that evaluation defined **without** quietly starting to populate a model that
is disk-only by design — and wrapping one that is already under `run-analysis` adds the
reporting and leaves that sink, and the model it is filling, exactly alone.

**It answers a better question than watching does.** The two ways to work this out from
outside the compiler both get it wrong: watching var roots reports `alter-var-root`, which
is a value changing and no new code, and comparing what a namespace maps before and after
misses a redefinition that lands on the same names. The compiler knows, and it costs it one
deref per `def` to say so.

`clojure.cljs.analysis` reports through this same var with `:dialect :cljs`, for the reason
it shares `*reload-progress*`: half of a ClojureScript reload is Clojure macro files loaded
on this JVM, so a watcher that bound two vars would see half of one reload in each.

## 9. Reload workflows

Two coexisting workflows. The distinction is purely *what gets recompiled* — the model is kept
current on **both**.

### 9.1 Plain single-file reload — `load-file!`

Recompile that one file (by its resource, so all its namespaces), redefine its vars in place,
**no** cascade to callers, **no** re-expansion of macro calls in other files. The scalpel stays a
scalpel — the file analog of Clojure's `require :reload` scope.

Subtlety that makes the two workflows coexist cleanly: reloading a macro's defining file still
(a) atomically replaces that file's model slice, and (b) leaves the model recording "files X, Y
expanded an *older* version of this macro" (their macro-dep edges are unchanged, so a later
staleness check will see them depend on the just-edited file). It does **not** recompile X and Y.
Acting on that dependency (the cascade) is exclusive to stale-reload.

### 9.2 Stale-reload

Recompiles the touched files **plus** the caller **files** that are actually stale, in
topological order, and **optionally** prunes vars no longer in source.

Staleness inputs, recorded per file after each successful compile:

1. source-file **modification time** (`:file-mtime`, keyed by the resource path — no ns→path munging),
2. the **macro dependency edges** its forms expanded (`:macro-deps`, from the `macroexpand1` tap;
   each edge carries the expanding form's fid, hence its file),
3. the **classes its forms named** (`:class-usages`, keyed by class name), against the classes the
   model's own def forms generated.

A file is a **seed** if its mtime changed since last load (edited since last loaded). The stale
set is the seed plus the transitive closure of its compile-time dependent *files* over the
**compile graph** (`file-compile-graph`), which has two kinds of edge:

- **macro edges** — a form in F expanded a macro whose defining namespace lives in D
  (projected into file space via each form's `:source` and each macro's owning-namespace file);
- **generated-class edges** — a form in F named a class that a def form in D generated: a
  `defprotocol`'s interface, or a `deftype`'s / `defrecord`'s class (`build-file-class-graph`).

Both are *conservative*: any edit to a macro-defining file marks that file's macro-dependent
files stale, and any edit to a file that generates a class marks every file that names it,
neither distinguishing which form changed. Runtime (function-call) dependents are excluded — a
plain var re-resolves at runtime and needs no recompile.

**What is stale and what order to load it in are different questions.** The cascade above is right
to exclude runtime dependents: a call re-resolves its var every time it runs, so a file that only
calls into an edited file needs no recompile. The *order* is another matter. A var that does not
exist **yet** is not resolved at run time at all — the compiler resolves `alias/sym` when it
compiles the form and throws `No such var` on the spot — so two files that are **both** in the
stale set, one of which has just started using a definition the other has just grown, have to be
loaded in that order. Switching branches does this wholesale.

So the order comes from a wider graph than the cascade does, without loading anything the cascade
did not choose. On top of the compile graph:

- **var edges** (`file-var-graph`) — a form in F refers to a var that a def in D defines, both
  files being among the ones reloaded. Derived from `:usages` and `:defs` and restricted to the
  reload set, so it costs a lookup per def of those files rather than a walk of every usage in the
  program.
- **require edges** (`file-require-graph`) — the `ns` form of F's **new source on disk** requires
  a namespace that another file being reloaded holds. This is the one edge that cannot come from
  the model: every graph above is built from what the compiler recorded the *last* time these
  files were loaded, so it holds the dependencies the old sources had and none the edit
  introduces — and an edit that first reaches into a file it never touched before is exactly the
  one whose order matters, since the definition it has come for was not there before. A namespace
  is matched to a file the way `require` matches one (dashes to underscores, dots to slashes), and
  also through the model, for a file whose namespace is not named after it. A file that will not
  read contributes no edges rather than an error: it is about to be handed to the compiler, which
  will complain about it in better words.

Neither kind of edge widens the reload — they say which of the chosen files goes first and nothing
else — and a cycle is broken by placing one file and carrying on, so only the cycle itself loses
its order. Remaining gap: a dependency taken without a top-level `require` and absent from the old
sources (a run-time `require`, a fully-qualified name in a file that never mentions the namespace
at the top) is still not in the order.

**Why generated classes need an edge of their own.** `deftype` is `clojure.core`'s macro, so the
only macro edge a type-defining file has is to `clojure.core` — the file whose `defprotocol`
generated the interface the type was compiled against is not in the macro graph *at all*.
Reloading a protocol generates a **new** interface, and every type compiled against the old one
silently stops satisfying it: the call fails at run time with `No implementation of method: :m of
protocol: #'a/P found for class: b.T`, which reads like a missing `extend-type` and is nothing of
the sort. Recompiling a `deftype`/`defrecord` file has the same shape: two classes of one name,
and whoever holds the first one no longer agrees with the rest of the program about `instance?`.
This is the coupling `clojure.tools.namespace` handles by brute force (it reloads *all*
transitive dependents, which is why it needs `remove-ns`); here the model already records where
each class is named, so the edge is derived instead of assumed.

Which class a def generated is read out of the **running process**, not guessed from the name: a
protocol's var holds its `:on-interface`, and a `deftype`/`defrecord` is found from the `->T`
factory it interned plus the `T` its own namespace imports, with a name check so that an
*imported* class is never mistaken for a generated one. A class no def in the model generates —
from a jar, from the JDK, from `import` — owns no file and makes no edge: nothing can generate it
again, so nothing can go stale against it. Known gap: `definterface` and `gen-class` intern no
var, so an interface defined by one of them is not owned by its file.

(A precise variant — per-macro source-form versions, so only dependents of the specific changed
macro reload — was built and reverted to this simpler scheme by request. `:inline`-fn edges are
a deliberately-skipped staleness hole; `:inline` is rare.)

**Macro re-expansion is automatic here.** Recompiling a file inherently re-runs
macroexpansion, so "re-evaluate macro calls only when recompiling stale files" needs nothing
beyond the version edges + topo reload above.

**Files that are gone.** A file whose source has been deleted (or renamed, or moved off the
classpath) is not stale — staleness is "load it again", and there is nothing to load it from — so
`changed-files` skips it and always did. It is not current either: the process still holds what
the file defined, and the model still answers `definition` with a file no editor can open. So
`stale-reload!` asks `deleted-files` as well as `stale-files`, and **drops** what it names
(`drop-deleted-file!`) before loading anything:

- its forms leave the model unconditionally — a record of what was read out of files cannot go on
  answering for a file that cannot be read, and nothing will ever flag a gone file as changed, so
  a reload that left it would leave it for good. `retract-file!` drops its staleness baselines with
  its forms, so a dropped file is one the model has nothing left to say about;
- with `:prune`, everything it defined is unmapped — the same prune a reloaded file gets, with the
  whole file playing the part of the deleted `def`: no live form defines any of it, so all of it
  goes, wherever it is mapped (§9.3), protocol methods included;
- and its namespaces stop being **loaded libs** (`forget-lib!`, matching
  `clojure.tools.namespace`'s `remove-lib`), unless another file still defines one of them. The
  `ns` form in the file is what put the name in `*loaded-libs*`, whatever loaded the file, so
  taking it out undoes what the file did — and it is what makes `(require 'that.ns)` say what the
  disk says instead of finding the dead entry and doing nothing.

The namespace **object** is left standing, with its aliases, its imports and any var an `intern`
made in it. `remove-ns` would take all of that, and the model speaks for none of it; what is
removed here is removed one definition at a time, each because the model recorded the file
defining it.

Deleted files are dropped **before** the stale files are loaded, as on the ClojureScript side, so
that a stale file still using a gone definition fails where it uses it rather than compiling clean
against a file nobody can open. They never seed the cascade and are not in the reload's answer:
the files that expanded a deleted file's macros keep the expansion they have, which is a fact
about what their source now says, and they say so the next time anything compiles them.

Not a watcher. Whether a file is gone or merely between two writes is a question nothing can
answer from the filesystem alone, and an editor that saves by writing a new file over the old one
is a process where the answer changes twice per save — so `deleted-files` is asked by
`stale-reload!`, which is asked for by hand, and never polled.

### 9.3 Prune — the explicit "undefine"

The surgical counterpart to "vars persist" (§5). Default reload keeps vars alive; **prune** is
the explicit operation that removes vars whose defining form vanished from the source.

- Uses **def provenance** (§7.2): "form at position P defined vars {…}" — a form removed from
  source ⇒ prune exactly the vars that form defined (handles the multi-var `defprotocol` /
  `defrecord` / `defmulti` cases that name-set diffing gets wrong).
- The prune itself is `ns-unmap`, **runtime-only**, and it unmaps each pruned var **wherever any
  namespace maps it** — its own home (a file's vars may span several), and every namespace that
  `refer`red it, under the name that namespace refers it as. One sweep over `ns-map` finds all
  three cases (interned, referred, referred-and-renamed) and finds each by the name it is written
  as; the match is by **Var identity**, so a namespace with a var of its own under the same name
  keeps it. Leaving a refer behind would leave the name resolving in the referring file while the
  defining file no longer says it — the state prune exists to get out of, and the one that file
  would next be compiled against. The walk is only taken when something was actually pruned, so a
  reload that deleted nothing pays nothing. The model side is already reconciled by
  `load-file!`'s retract before `prune-file!` runs: a deleted def still referenced by other forms
  becomes a **tombstone** in `:defs` (`:removed true`, its `:usages` preserved so the now-dangling
  references stay findable), and once its last reference is gone the tombstone is dropped by
  `sweep-tombstones` at the operation boundary (deferred to the stable end state, not GC'd eagerly
  during retract — mid-reload a still-referenced var's usage set is transiently emptied and then
  re-filled). The sweep is **scoped**: each driver (`load-file!` / `retract-file!`)
  collects, in a thread-local `*emptied-tombstones*`, only the var keys *its own* retraction
  emptied, and sweeps just those — so it never scans the whole `:defs` map, and one thread cannot
  GC a tombstone another thread's concurrent reload has transiently emptied (a residual race
  needs two reloads racing on the very same deleted var; a cold reanalysis reconciles it). A
  deleted def with no references is dropped outright. Because vars are
  keyed by **name symbol**, not Var-object identity (§5), redefinition needs no reconciliation and
  no dead Var is pinned; `prune-file!` only removes the interned var that a `load`/`require :reload`
  leaves behind.
- **Gate with the usage graph, warn don't block.** The model knows every remaining usage, so
  prune can report precisely — "removing `foo`, still referenced at A:12, B:30." Default to
  **warn-and-prune**, not block: vars get referenced reflectively (`#'foo`, `resolve`,
  `requiring-resolve`) in ways no static graph sees, so refusing on any inbound edge is both
  noisy and still-unsafe.
- **Var-identity guard.** Since the model keys vars by name, not object, prune takes a
  `{qsym → Var}` snapshot (`file-def-var-snapshot`) of file F's defs *before* the reload and only
  unmaps a candidate when the **same Var object** is still interned afterwards. A def deleted from
  source but re-created under a fresh identity during the reload (an explicit `intern`, or
  `ns-unmap`+re-`intern`) is a different object, so it is preserved rather than destroyed. The
  "still deleted" test is "no healthy `:defs` entry for it **anywhere**" — so a def *moved* to
  another file that has since been reloaded (both files are stale, both reload) is not pruned.
- **A second sweep for protocol methods.** A `defprotocol`'s method vars are `intern`ed, never
  `def`-ed, so def provenance says nothing about them and the identity-guarded first sweep can
  never be their judge. The protocol is, and it is the authority: after the def sweep,
  `prune-file!` walks the protocols F defines - those the sweep just unmapped included - and
  unmaps every var in the protocol's home namespace whose `:protocol` is **identical** to that
  protocol var and whose name its live `:sigs` no longer lists (all of them when the protocol
  itself has gone). So deleting a method from a protocol, or deleting the whole `defprotocol`,
  stops the name resolving instead of leaving a var that answers to nobody: today's failure is a
  runtime `No implementation of method: :m of protocol: #'ns/P`, which reads like a missing
  `extend-type` rather than like code that is behind. A var an explicit `intern` made is still
  left alone - nothing records it, and nothing else speaks for it either.
- **Precondition: prune only right after a full (re)analysis of F.** Prune deletes vars that were
  in F's pre-reload defs but that the model now records no healthy `:defs` entry for, reading that
  absence as "deleted from source." That equivalence holds only when `:defs` was *just* fully
  repopulated — which `stale-reload!` guarantees by calling `load-file!` immediately before
  `prune-file!`. Absent that, a var that never entered `:defs` for a reason *other* than deletion
  — created by a runtime `intern` rather than a `def` form, or in a file never analysed under the
  sink — would be wrongly unmapped (silent data loss). So `prune-file!` **refuses** (throws) on a
  file with no forms in `:source->forms`, turning standalone misuse into a loud error.

**Out of scope for v1 (note so they aren't surprises):**
- `defmethod` is **not a var** — removing one mutates a multimethod, needing method-level
  provenance ("form P added dispatch value V to multi M"), a parallel mechanism.
- ~~**Refers aren't owned by a file**~~ — they are not, but leaving them was worse: a referred name
  went on resolving after the def behind it was pruned, so the two halves of one name disagreed.
  Prune now sweeps them too (see the `ns-unmap` bullet above). What is still out of scope is
  putting one back: a refer the source still asks for is restored by reloading the file that asks,
  not by prune.
- `declare` / forward decls define a var with no root — provenance handles them; don't mistake
  "no root value" for "not defined."

## 10. Suggested sequencing

1. **Layer 0** — gated sink + a couple of trivial events (var def, var usage), no positions.
   Proves the zero-cost-when-off property and validates the model shape via crude
   cross-namespace find-usages.
2. **Layer 1** — symbol + keyword positions in the reader (+ collection spans). De-risks
   everything; without it we're stuck at form-level.
3. **Layer 2** — remaining taps (locals, interop, macros/`:inline`, requires/imports).
4. **Layer 3** — query API + the named features.
5. **§7 provenance + generation** — needed the moment reload (not just cold load) is exercised;
   land it before incremental reload.
6. **§9** — stale-reload (dependency graph + versions) and prune, on top of the provenance the
   §9.1 version-bump already produces.

## 11. Known limitations (state them in results)

- Analysis *runs* the code (§2) — side effects fire; not for untrusted input.
- **unused public var** can't see external / reflective callers → scope to private/non-exported.
- **keyword jump-to-def** is convention-based at best (no true def site).
- `defmethod` removal, direct-linking caller staleness (if enabled), and reflective var usage
  are all partial — documented above where they bite.
- **Dead code (§6.1) is resolved by name, not compiled**: a name bound by a macro the walk
  does not know is recorded as a use of the var or class it also names, and a local of the
  live code around a `#_` is recognised only by having been bound earlier in the same
  top-level form.
- **Syntax-quote refs resolve at read time**, so a var referenced inside a macro body *before*
  it is defined in the same file (a bare forward reference, no `declare`) doesn't resolve and
  is skipped. Cross-namespace refs and `declare`d forwards are unaffected.
- **Macro-body line numbers under an analysis load.** To stop syntax-quoted forms from looking
  source-written (which would record a call-site phantom usage), analysis strips
  `:line`/`:column` from a syntax-quoted form's emitted metadata — but only for a form that also
  carries *other* metadata (a type hint or user `^{...}` meta); position-only forms already lose
  it in stock Clojure. So when analysis is on, a runtime error or compiler message in code
  generated by such a form reports the enclosing form's line instead of the precise macro-body
  line, disagreeing with a plain `require` of the same source. Program behaviour is unchanged
  (only positions are stripped, never semantic metadata like `:tag`), and a plain reload is
  unaffected. A precise fix means decoupling the compiler's line marker from `isSourceSymbol`'s
  `:line`-based "source-written" test (§4, Layer 1) — deferred as not worth the ripple for a
  diagnostics-only, narrowly-triggered gap.

## 12. TODO — deferred resolution (fixes the forward-ref gap + gives an undefined-symbol lint)

Replace read-time resolution in `sinkSyntaxQuoteRef` with **deferred resolution**:

- Syntax-quote already computes the fully-qualified *name* even for a not-yet-defined target,
  so at read time record a **pending** ref `{:sym qualified-sym :from-ns :span}` filed under the
  current form's fid (retraction works unchanged) instead of resolving to a `Var`/`Class`.
- After the file finishes loading (`load-file!` / `run-analysis` completion), run one resolve
  pass: each pending ref that now resolves moves into `:usages` keyed by identity.
- **Leftovers are the payoff:** a pending ref that still won't resolve is an
  **unresolved-symbol / undefined-reference diagnostic** — a clj-kondo-style lint the same
  mechanism gives for free. Build this when we do diagnostics; the forward-ref fix falls out.

## 13. What a lint is made of

Three more facts per form, and one per file, so that a tool can answer clj-kondo's
questions out of what the compiler resolved - replique's `:lints` op is the first such
tool.

- **Calls** (`IAnalysisSink.invokeUsage`) - every call of a var the source wrote, with its
  argument count *after* macroexpansion and the span of the list as written: `(-> x (f 1))`
  is a call of `f` with two arguments at `(f 1)`. The arity check is not made here. It is
  the caller's to make, against the var's `:arglists` as they are when it asks, so a caller
  is wrong the moment its callee changes and not only when the caller compiles again.
- **Warnings** (`IAnalysisSink.warning`) - the reflection, boxed-math and performance
  warnings the compiler prints, and the earmuffed-but-not-dynamic one, filed under the form
  that caused them. Told only where they are printed, so a sink hears what
  `*warn-on-reflection*` / `*unchecked-math*` asked for and nothing more. The printed text
  is unchanged; both go through `Compiler.compilerWarning`.
- **Failures** - the file whose load threw, where (the compiler's line and column, or the
  form being compiled) and why (the deepest cause's message), against the on-disk mtime of
  the version that failed. Kept until the file next loads to the end: `file-failure`.

All read through `file-facts`, one file's facts in form order, plus `file-mtime` (the
version they are about) and `version` (a token `identical?` to an earlier one exactly while
nothing has changed - what a tool compares around an evaluation to know whether to ask
again).
