# lower/

**AST → SSA translation.** The single place that establishes
semantic invariants. Every downstream pass (`opt/*`) is a *strictly
optional optimization*: delete the whole `opt/` folder and programs
still execute correctly, just slower.

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
4. **Naive-but-correct emission.** Lower picks the natural emission
   for each AST node, not the most optimal one. FBIP, scalarization,
   etc. fall out of opt passes; lower doesn't second-guess.
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
| `rc_emit.rs` | Post-emission pass: insert `RcInc`/`RcDec` for ownership tracking. |
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
- **Aggregates are heap-allocated at lower time.** SROA in `opt/`
  promotes them to register `Agg` values when safe — lower doesn't
  need to know.
- **Auto-rc semantics live in `eval`, not in `lower`.** Lower emits
  RcPtr-typed loads/stores; the runtime handles the rc bookkeeping.
  This used to be `rc_emit`'s job; pushing it into eval simplified
  the convention zoo dramatically.
- **The `Builder` has a small forwarding cache and tracks recent
  stores.** This isn't an "opt pass" — it's local-scope hygiene
  during emission. Lower has the info; using it is cheap.
