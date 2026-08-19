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
    `::x`/`::alias/x` indexed fully-qualified; `find-keyword-usages`.
  - **C. Interop** — `classUsage` from `HostExpr.maybeClass` + the two `analyzeSymbol` class
    branches; `(Foo. ...)` position carried through the constructor desugaring in `macroexpand1`
    (`carryClassPosition`). Covers `new`, type hints, static/instance members. `find-class-usages`.
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
    not covered (documented limitation).

  Not yet done at that point: collection spans, `:inline`-fn compile-time edges.
- **§7 (provenance + retraction) — done, form-based.** Per-top-level-form provenance via
  `beginForm`/`endForm` wrapping read+eval in `Compiler.load` (so read-time keyword facts and
  eval-time facts share one form); each fact filed under its form's `[:index target span]`
  retraction list; `entity->form` drives retract-on-redefine; `ns->forms` batches namespace
  ops. Drivers: `run-analysis`, `load-ns!` (retract + reload), and `retract-ns!` — all
  populated **from disk**, so the model stays in sync with the file and never reflects an
  un-saved REPL eval. Proven: locals no longer accumulate across reloads; a single-ns reload
  preserves other namespaces' usages of its vars. This also fixed the `:locals` lifecycle
  issue noted above.

- **§9 (stale-reload + prune) — done.** Staleness is **mtime-based**: `snapshot-mtimes!` /
  `load-ns!` record each namespace's source-file modification time in `:ns-mtime`;
  `changed-namespaces` flags a namespace whose current file mtime differs from the baseline
  (edited since last loaded). `stale-namespaces` then takes the **conservative** transitive
  closure over the **macro** dependency graph (runtime call dependents are excluded — the
  precision tools.namespace lacks; but any edit to a macro-defining file marks its
  macro-dependents stale, without distinguishing which form in the file changed).
  `stale-reload!` reloads the stale set in macro-dependency (topological) order via `load-ns!`,
  optionally pruning; `prune-ns!` ns-unmaps vars whose defining form vanished, warning (not
  blocking) on remaining usages. Proven end-to-end: editing a macro reloads its dependents so
  they re-expand the new macro (25→10→0), reloading the macro's ns *alone* does not update the
  dependent (the case a naive reload misses), and a removed var is pruned.

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
| local **usage** | `analyzeSymbol` local branch (`Compiler.java:7869`, `LocalBindingExpr`) |
| local **definition** (+ scope extent) | `registerLocal` (`Compiler.java:7313`); `let`/`loop`/`fn` parsers for scope entry/exit |
| var **definition** | `DefExpr.Parser.parse` (`Compiler.java:524`, already calls `registerVar`) |
| Java interop (class / field / method) | `StaticFieldExpr` / `QualifiedMethodExpr` branches in `analyzeSymbol`; host-method parsers |
| macro **usage** + compile-time edge | `macroexpand1` (`Compiler.java:7566`): always record the compile-time edge "this file depends on M"; record the "macro M used here" usage only for a source-written call (the macro name is textually present) |
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

A **namespace** operation is just a batch over its forms: `ns->forms[N]` holds the fids whose
source is N, so reloading N is "retract every fid in `ns->forms[N]`, then load fresh." Form
granularity subsumes namespace granularity — one mechanism, and ns-load / stale-load are batches
of form-loads (see §8).

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
granularity is therefore the **namespace** (`load-ns!`); the per-form primitive above is an
internal building block, not an operation on its own. Analysis of an edited form lands when its
file is saved and reloaded.

- **Cold load → full-project analysis.** Clean slate; the model is built from empty as every ns
  loads, each form a form-load. The only run where cross-namespace completeness is trivially
  guaranteed — the correctness baseline / rebuild button.
- **Single-namespace load → single-ns analysis.** Batch of form-loads over the file: retract
  every fid in `ns->forms[N]` (dropping defs removed from source and stale non-def forms), then
  load N fresh. **Preserves every other namespace's usages of N's vars**, because those live
  under *their* forms, not N's.
- **Stale-files load (new) → stale-files analysis.** Compute the macro-aware stale set (§9),
  reload it in topological order, each file a single-ns load.

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

1. source-file **modification time** (`:ns-mtime`),
2. the **macro dependency edges** it expanded (`:macro-deps`, from the `macroexpand1` tap).

A namespace is a **seed** if its file mtime changed since last load (edited since last loaded).
The stale set is the seed plus the transitive closure of its macro-dependents over the macro
graph — the *conservative* macro-aware closure: any edit to a macro-defining file marks that
file's macro-dependents stale, without distinguishing which form in the file changed. Runtime
(function-call) dependents are excluded — a plain var re-resolves at runtime and needs no
recompile. Reload the stale set in macro-dependency (topological) order.

(A precise variant — per-macro source-form versions, so only dependents of the specific changed
macro reload — was built and reverted to this simpler scheme by request. `:inline`-fn edges are
a deliberately-skipped staleness hole; `:inline` is rare.)

**Macro re-expansion is automatic here.** Recompiling a file inherently re-runs
macroexpansion, so "re-evaluate macro calls only when recompiling stale files" needs nothing
beyond the version edges + topo reload above.

### 9.3 Prune — the explicit "undefine"

The surgical counterpart to "vars persist" (§5). Default reload keeps vars alive; **prune** is
the explicit operation that removes vars whose defining form vanished from the source.

- Uses **def provenance** (§7.2): "form at position P defined vars {…}" — a form removed from
  source ⇒ prune exactly the vars that form defined (handles the multi-var `defprotocol` /
  `defrecord` / `defmulti` cases that name-set diffing gets wrong).
- The prune itself is `ns-unmap`, **runtime-only**. The model side is already reconciled by
  `load-ns!`'s retract before `prune-ns!` runs: a deleted def still referenced by other forms
  becomes a **tombstone** in `:defs` (`:removed true`, its `:usages` preserved so the now-dangling
  references stay findable), and once its last reference is gone the tombstone is dropped by
  `sweep-tombstones` at the operation boundary (deferred to the stable end state, not GC'd eagerly
  during retract — mid-reload a still-referenced var's usage set is transiently emptied and then
  re-filled). The sweep is **scoped**: each driver (`load-ns!` / `retract-ns!`)
  collects, in a thread-local `*emptied-tombstones*`, only the var keys *its own* retraction
  emptied, and sweeps just those — so it never scans the whole `:defs` map, and one thread cannot
  GC a tombstone another thread's concurrent reload has transiently emptied (a residual race
  needs two reloads racing on the very same deleted var; a cold reanalysis reconciles it). A
  deleted def with no references is dropped outright. Because vars are
  keyed by **name symbol**, not Var-object identity (§5), redefinition needs no reconciliation and
  no dead Var is pinned; `prune-ns!` only removes the interned var that `require :reload` leaves
  behind.
- **Gate with the usage graph, warn don't block.** The model knows every remaining usage, so
  prune can report precisely — "removing `foo`, still referenced at A:12, B:30." Default to
  **warn-and-prune**, not block: vars get referenced reflectively (`#'foo`, `resolve`,
  `requiring-resolve`) in ways no static graph sees, so refusing on any inbound edge is both
  noisy and still-unsafe.
- **Var-identity guard.** Since the model keys vars by name, not object, prune takes a
  `{qsym → Var}` snapshot (`ns-def-var-snapshot`) of N's defs *before* the reload and only unmaps
  a candidate when the **same Var object** is still interned afterwards. A def deleted from source
  but re-created under a fresh identity during the reload (an explicit `intern`, or
  `ns-unmap`+re-`intern`) is a different object, so it is preserved rather than destroyed.
- **Precondition: prune only right after a full (re)analysis of N.** Prune deletes vars that are
  interned in N but absent from `:defs` (as a healthy, non-tombstone entry), reading that absence
  as "deleted from source."
  That equivalence holds only when `:defs` was *just* fully repopulated — which `stale-reload!`
  guarantees by calling `load-ns!` immediately before `prune-ns!`. Absent that, a var that never
  entered `:defs` for a reason *other* than deletion — created by a runtime `intern` rather than
  a `def` form, or in a namespace never analysed under the sink — would be wrongly unmapped
  (silent data loss). So `prune-ns!` **refuses** (throws) on a namespace with no forms in
  `:ns->forms`, turning standalone misuse into a loud error rather than a quiet deletion.

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
- After the namespace finishes loading (`load-ns!` / `run-analysis` completion), run one resolve
  pass: each pending ref that now resolves moves into `:usages` keyed by identity.
- **Leftovers are the payoff:** a pending ref that still won't resolve is an
  **unresolved-symbol / undefined-reference diagnostic** — a clj-kondo-style lint the same
  mechanism gives for free. Build this when we do diagnostics; the forward-ref fix falls out.
