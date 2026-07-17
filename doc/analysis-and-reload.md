<!-- -*- mode: markdown ; mode: visual-line ; coding: utf-8 -*- -->

# Compiler-integrated analysis & macro-aware reload — design

Status: **design, not yet implemented.** This document is the plan we build against.

## 1. Goal

Two capabilities, both built by teaching the real compiler to expose what it already
knows, rather than by writing a separate static analyzer:

1. **Semantic information for tooling** — enough to support clj-kondo-style features:
   find-usages, jump-to-definition, unused `require` / unused var / unused locals /
   unused import, unresolved-symbol, and more over time. Both **cross-namespace** and
   **per-file**. Consumed **in-process** by a tool (a REPL/nREPL-style server) that
   queries an in-memory model — not emitted to a file or database.

2. **Macro-aware stale reload** — a new reload operation that recompiles the files that
   are actually out of date, *including files that are stale only because a macro (or
   `:inline` fn) they expand changed*, in dependency order — and can optionally prune
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

**Free synthetic-form filtering.** Because positions are attached *in the reader*, only
user-written nodes carry them; symbols introduced by macroexpansion (gensyms, plumbing) do
not. So "record a usage only if the node carries a read position" automatically attributes
usages to real source and ignores macro-generated code — which is exactly the problem that
makes expansion-based analysis hard. Build this rule in from the start.

De-risk by prototyping this layer first; without it, every feature degrades to form-level
precision and the value proposition changes.

### Layer 2 — capture points in the compiler

Few and centralized:

| Event | Where |
| --- | --- |
| var **usage** | `analyzeSymbol` var branch (`Compiler.java:7910`, the `registerVar(v); return new VarExpr(v)` path) |
| local **usage** | `analyzeSymbol` local branch (`Compiler.java:7869`, `LocalBindingExpr`) |
| local **definition** (+ scope extent) | `registerLocal` (`Compiler.java:7313`); `let`/`loop`/`fn` parsers for scope entry/exit |
| var **definition** | `DefExpr.Parser.parse` (`Compiler.java:524`, already calls `registerVar`) |
| Java interop (class / field / method) | `StaticFieldExpr` / `QualifiedMethodExpr` branches in `analyzeSymbol`; host-method parsers |
| macro **usage** + compile-time edge | `macroexpand1` (`Compiler.java:7566`): record "macro M used here" and "this file depends on M@version" |
| keyword usage | in the **reader**, at `::` resolution (`matchSymbol`) — see §6 |
| require / refer / alias / import | do **not** parse `ns` forms; let them run, then read `Namespace` alias/mapping/refer state (authoritative; handles `ns`, bare `require`, `use`, dynamic requires uniformly) |

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

### 7.3 Generation

A **per-namespace counter**, bumped each time N is recompiled and stamped onto every fact N
produces. Retraction becomes one sweep — "drop every fact stamped `N@gen < current`" — atomic,
no diffing, no half-retracted state.

### 7.4 The invariant that keeps global queries honest

**"unused var V" is a global fold: no namespace anywhere holds a usage of V.** As long as each
reload keeps that ns's usage slice *current and complete* (via 7.2 + 7.3), the fold stays
correct **without ever rebuilding the whole model**. Same for unused-require and unused-import.
This is the one property to protect.

Consequence to design around: a single reload can *change verdicts in other namespaces* (delete
N's only call to `other/foo` and `other/foo` becomes unused). That is correct and desired — but
it means the query API must be **"ask the model,"** never "return diagnostics for the file I
just compiled."

## 8. Drivers (what triggers analysis)

The sink and capture points are identical across all three; only the **scope** and the
**model-update semantics** differ.

- **Cold load → full-project analysis.** Clean slate; the model is built from empty as every ns
  loads. The only run where cross-namespace completeness is trivially guaranteed — the
  correctness baseline / rebuild button.
- **Single-namespace load → single-ns analysis.** Atomically replace N's slice (7.2/7.3):
  retract N's outgoing facts, insert the new ones, **preserve every other namespace's usages of
  N's vars.**
- **Stale-files load (new) → stale-files analysis.** Compute the macro-aware stale set (§9),
  reload it in topological order, each file doing the single-ns atomic replace.

## 9. Reload workflows

Two coexisting workflows. The distinction is purely *what gets recompiled* — the model is kept
current on **both**.

### 9.1 Plain single-file reload — unchanged

`require :reload`, exactly Clojure's behaviour: recompile that one file, redefine its vars in
place, **no** cascade to callers, **no** re-expansion of macro calls in other namespaces. The
scalpel stays a scalpel.

Subtlety that makes the two workflows coexist cleanly: reloading a macro's defining file still
(a) atomically replaces that ns's model slice, and (b) **bumps the macro's version** — so the
model now records "callers X, Y expanded an *older* version of this macro." It does **not**
recompile X and Y. The version bump is a passive consequence of *any* reload; **acting** on it
(the cascade) is exclusive to stale-reload.

### 9.2 Stale-reload — new

Recompiles the touched files **plus** the caller namespaces that are actually stale, in
topological order, and **optionally** prunes vars no longer in source.

Staleness inputs, recorded per namespace after each successful compile:

1. content hash of its source,
2. `require`/`import` edges (runtime deps),
3. the set of **compile-time dependencies it expanded** — macros **and `:inline` fns** (and
   direct-linked callees if direct-linking is on; an analysis session will typically run with
   direct-linking **off** for redefinable vars, which drops that case, but `:inline` fns are
   always in play and would otherwise be a silent staleness hole) — each tagged with a
   **version** of that dependency's definition (hash of its source form, or a counter bumped on
   redefinition).

A file is stale if its own source hash changed **or** any compile-time dependency it expanded
changed version (the case tools.namespace misses). Propagate staleness through **both** graphs
(require edges and compile-time-dependency edges) and reload the stale set topologically.

**Macro re-expansion is automatic here.** Recompiling a file inherently re-runs
macroexpansion, so "re-evaluate macro calls only when recompiling stale files" needs nothing
beyond the version edges + topo reload above.

### 9.3 Prune — the explicit "undefine"

The surgical counterpart to "vars persist" (§5). Default reload keeps vars alive; **prune** is
the explicit operation that removes vars whose defining form vanished from the source.

- Uses **def provenance** (§7.2): "form at position P defined vars {…}" — a form removed from
  source ⇒ prune exactly the vars that form defined (handles the multi-var `defprotocol` /
  `defrecord` / `defmulti` cases that name-set diffing gets wrong).
- The prune itself is `ns-unmap` (plus dropping the var's side-map entry). Because definitions
  *are* the runtime (§5), there is no separate index to reconcile — mutate the runtime and the
  model follows.
- **Gate with the usage graph, warn don't block.** The model knows every remaining usage, so
  prune can report precisely — "removing `foo`, still referenced at A:12, B:30." Default to
  **warn-and-prune**, not block: vars get referenced reflectively (`#'foo`, `resolve`,
  `requiring-resolve`) in ways no static graph sees, so refusing on any inbound edge is both
  noisy and still-unsafe.

**Out of scope for v1 (note so they aren't surprises):**
- `defmethod` is **not a var** — removing one mutates a multimethod, needing method-level
  provenance ("form P added dispatch value V to multi M"), a parallel mechanism.
- **Refers aren't owned by N** — `refer`/`use` put other namespaces' mappings in N's map. Prune
  only vars where `var.ns == N`; leave refers to the require graph.
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
