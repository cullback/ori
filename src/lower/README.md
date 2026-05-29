# lower/

**AST → SSA translation.** The single place that establishes the
language's semantic invariants. Every downstream pass (`opt/*`) is
*strictly optional optimization*: delete the whole `opt/` folder
and programs still execute correctly, just slower.

## Why this matters

Anything the language guarantees — strict evaluation order, FBIP
in-place-when-unique semantics for structural updates, total
termination guarantees, leak-free RC, no observable side effects
from dropped pure bindings — must be enforced **here**, by lower.
Lower cannot rely on opt to clean up after a semantically-wrong
emission. If lower emits "build a fresh copy" where the language
spec says "mutate in place when unique," that's a bug even if some
opt pass would later promote the alloc. The language's behavior
is whatever lower produces, evaluated by the runtime; opt only
makes it faster.

This cuts both ways: lower must NOT skimp on emissions that are
semantically required (FBIP via `ReuseOrClone`, scope-end rc_decs
that establish leak-freedom, etc.), but it also must NOT do
optimizations that opt's job. Lower picks the **natural** emission
for each AST node; opt finds patterns within that emission.

## Inputs

A monomorphized AST module from the `passes/` pipeline:

- **Monomorphized** — no type variables remain.
- **Lambda-lifted and specialized** — every `Call` has a known
  first-order target.
- **Patterns flattened** — no nested constructor patterns, no
  `Pattern::List`.
- **Folds desugared** — every `Fold` is now a synthesized helper.
- **Reachability pruned** — no orphan decls.

## Outputs (invariants `lower` establishes)

The SSA module emitted satisfies all of these by construction. The
test harness re-validates after every pass — a breakage shows up as
`SSA validation failed after '<pass>'` rather than a runtime panic.

1. **Explicit block params for cross-block values** (`ssa_form`).
   Every value used in block B is either a function param, defined
   in B, or threaded into B via block-arg passing. No implicit
   scoping.
2. **Concrete typed `Value`s.** Every `Value` carries its
   `ScalarType` at creation. Type-aware semantics in eval (auto-rc
   for RcPtr, etc.) rely on this.
3. **Leak-free RC traffic** (`rc_emit`). Every heap allocation has
   a matching `rc_dec` (or cascade from a parent's release) by
   program exit. Tests assert via `Heap::count_live_objects() == 0`.
4. **Natural emission, including FBIP and decomposition.** Lower picks
   the natural emission for each AST node.
   - For "build a modified version of an existing structure" AST nodes
     (`RecordUpdate`, `list.set`, etc.), the natural lowering is
     `cow_store_dyn` / `cow_move_out` / `cow_resize_dyn` — primitives
     whose runtime check (`if src.rc == 1` → mutate in place, else
     clone) enforces FBIP semantics dynamically.
   - For fixed-shape aggregates (tuples, records, single-variant tag
     unions, closure envs), the natural lowering emits **parallel SSA
     Values** — no heap object. Multi-result `Inst::Call` and
     `Terminator::Return(Vec<Value>)` carry these across function
     boundaries. `LoweredValue::{Single, Multi}` is the bridge between
     emission and consumption.

   **Both FBIP and aggregate decomposition are established here, by
   lower; they are NOT opt passes.**
5. **No dead let-bindings.** Ori is total/pure, so an unused `let`
   binding has no observable effect. Lower elides them before
   emitting (see `lower_block` in `mod.rs`).
6. **Locally-clean output.** Once stores/loads are emitted, lower
   does small local cleanup before handing off:
   - **Local store→load forwarding** (`builder.recent_stores`):
     when the builder has just stored `v` to `ptr[k]` and is about
     to emit `load ptr[k]`, return `v` directly.
   - **Dead alloc elimination** (`elim_dead_allocs`): an alloc
     whose only uses are stores into it + a final rc_dec is dropped
     entirely (its data was never observed).

## Sub-modules

The translation lives in `lower/mod.rs`'s `LowerCtx::lower_expr`.
Domain-specific emissions are split into focused files:

| File | Role |
|---|---|
| `mod.rs` | Entry point; `LowerCtx`; statement and expression dispatch. |
| `boolean.rs` | Bool / comparison / `is` pattern / `and`/`or` short-circuit. |
| `call.rs` | Function / method / qualified-call dispatch. |
| `constructor.rs` | Tag union construction (`con_layout`). |
| `eq.rs` | Generated structural equality machinery. |
| `hash.rs` | `hash`, `to_str`, string-literal, string-concat. |
| `list_ops.rs` | `List.set`, `List.repeat`, `List.range`, `List.reverse`, `List.sublist`, `List.get`. FBIP for set. |
| `numeric.rs` | Integer/float coercion helpers. |
| `pattern.rs` | `when` arm compilation, pattern flattening. |
| `walk.rs` | `List.walk` (loop emission with `__apply_*` dispatch). |
| `ssa_form.rs` | Post-emission pass: convert implicit cross-block refs to explicit block params. |
| `rc_emit.rs` | Post-emission pass: insert end-of-scope `RcDec`s and pre-consume `RcInc`s for values whose last use is a transfer. Most rc semantics are intrinsic to eval now (auto-rc on RcPtr Load/Store/Call args), so this pass is smaller than it used to be — it mainly handles liveness-driven drops. |
| `elim_dead_allocs.rs` | Post-emission pass: kill alloc chains with no observers. |

## Lifecycle

`lower::lower(mono, fields)` runs the full pipeline:

1. Walk monomorphized AST, emit instructions via `Builder`. Local
   store-load forwarding fires during emission.
2. `ssa_form::run` — promote implicit cross-block refs to explicit
   block params.
3. `rc_emit::run` — establish RC traffic so the SSA is leak-free.
4. `elim_dead_allocs::run` — sweep dead alloc chains.

After step 4, the module is ready for `opt/*` (or for direct
interpretation).

## Design notes worth remembering

- **Lower establishes correctness; opt establishes performance.**
  If a problem is "the program crashes," it's lower's job. If it's
  "the program is slow," opt's.
- **Aggregates decompose at lower time.** Tuples, records, and single-
  variant tag unions emit parallel SSA Values directly. Heap stays for
  variable-length buffers and multi-variant tag union payloads. There
  is no aggregate type at the IR level — `ScalarType::Agg` doesn't
  exist; neither do `Pack` or `Extract`.
- **Auto-rc semantics live in `eval`, not in `lower`.** Lower emits
  RcPtr-typed loads/stores; the runtime handles the rc bookkeeping.
  This used to be `rc_emit`'s job; pushing it into eval simplified
  the convention zoo dramatically.
- **The `Builder` has a small forwarding cache and tracks recent
  stores.** This isn't an "opt pass" — it's local-scope hygiene
  during emission. Lower has the info; using it is cheap.
