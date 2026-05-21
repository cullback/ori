# opt/

**SSA optimization passes.** Strictly optional — every pass here is
performance, not correctness. Delete this whole folder and programs
still execute correctly (just slower, with more allocations).

## Inputs

A well-formed SSA module from `lower/`. All of lower's invariants
hold: explicit-block-params, typed values, leak-free rc, no dead
lets. Each pass takes the module and returns a module satisfying
the same invariants.

## Output guarantees

Every pass preserves:
- **Structural correctness** — the validator's hard errors don't
  fire after any pass. (Soft warnings can fire transiently; the
  pipeline reconverges by the final pass.)
- **Semantic equivalence** — the program's observable behavior
  (return value, IO if any) is unchanged.
- **RC correctness** — no leaks, no UAF. Tests verify via
  `Heap::count_live_objects() == 0`.

## The full pipeline

`opt::run_full_pipeline` is the canonical entry — both the binary
(`main.rs`) and the test harness call it, so they can't drift apart.

```
static_promote     # constant allocs → module statics
optimize           # local cleanup bundle (below)
inline             # inline small/marked callees
ssa_form           # repair cross-block refs introduced by inline
optimize           # cleanup post-inline
const_eval         # compile-time-evaluate zero-arg pure functions
optimize           # cleanup post-const_eval
sroa               # promote non-escaping heap allocs to Agg values
optimize           # cleanup post-sroa
rc_elide_static    # strip rc traffic on StaticRef values
rc_fuse            # cancel adjacent rc_inc/rc_dec pairs
optimize           # final cleanup
```

`optimize` is a bundle of small local passes that runs after every
major transform (each major transform unlocks new local opportunities).

## Pass catalog

### Major passes (transform-the-shape)

| Pass | Goal | Mechanism |
|---|---|---|
| `static_promote` | Move constant allocs out of the hot path. | Find `Alloc(N)` whose every store is a Const (or a pointer to another promoted alloc). Replace with `StaticRef`. |
| `inline` | Eliminate small function-call overhead. | For each `Call` to a small callee (≤ `MAX_INLINE_INSTS` = 30), splice the body into the caller. Cross-block refs cleaned up by `ssa_form`. |
| `const_eval` | Bake out zero-arg pure computations. | For each user function `f()` (no args, not `__`-prefixed), run eval. If result is a `Scalar`, replace `Call` with `Const`; if a heap value, materialize as `StaticRef`. |
| `sroa` | Avoid heap allocs for ephemeral aggregates. | Detect `Alloc + N stores` whose result doesn't escape (no Call args, no Store-as-val, only Load/rc/Return uses). Replace with `Pack` (register-resident `Agg`); convert `Load` → `Extract`. Handles flow through block params and Returns (sig changes verified for safety). **Distinct from FBIP** — FBIP is established by lower's emission of `ReuseOrClone` for structure-update AST nodes; SROA is a separate static-analysis optimization for non-escaping allocs in general. |
| `rc_elide_static` | Strip no-op rc on statics. | `StaticRef` values have sentinel rc; `RcInc`/`RcDec` on them are no-ops. Remove them. |
| `rc_fuse` | Cancel obvious rc traffic. | Adjacent `RcInc(v)` / `RcDec(v)` pairs (with nothing between that could touch v's rc) cancel out. |

### Local cleanup bundle (`optimize`)

Runs in order, each one-shot (no internal fixpoint loop):

| Pass | Goal |
|---|---|
| `const_fold` | Fold `BinOp(Const, Const)` → `Const`. |
| `nop_elim` | Remove identities like `x+0`, `x*1`, `x/1`. |
| `jump_threading` | Skip empty intermediate blocks. |
| `branch_fold` | Fold branches whose condition is constant. |
| `jump_threading` | Re-run — branch_fold may have created new empty blocks. |
| `branch_fold` | Re-run — jump_threading may have exposed new constant conditions. |
| `merge_blocks` | Combine single-pred + single-succ pairs. |
| `dce` | Drop instructions whose result is unused (per side-effect classification) and unreachable blocks. |

### Helpers

| File | Role |
|---|---|
| `operands.rs` | `rewrite_operands` / `rewrite_terminator_operands` — used by `nop_elim` and `inline` for value substitution. |

## Known limitations / quirks

- **`jump_threading` has a bug** triggered post-inline by certain
  CFG shapes — `fold_tree_depth` test currently fails with
  "index out of bounds at jump_threading.rs:68." Not yet root-caused.
- **`sroa`'s escape detection is conservative.** Any single unsafe
  use of a flow value demotes ALL allocs in that function. A more
  precise per-flow-group analysis would catch more.
- **`Heap::aggs` (SROA's side table for register Aggs) doesn't
  free.** Aggregates accumulate over an `eval` call. For benchmarks
  and one-shot compilation this is fine; long-running programs
  would need lifecycle management.
- **`inline`'s threshold is 30 insts.** Larger functions don't get
  inlined regardless of whether SROA would benefit from inlining
  them. Could be made cost-based ("inline if the callee returns a
  heap alloc that'd be SROA'd at the call site"), but not yet.

## Design notes worth remembering

- **Each pass does ONE thing.** "Cleanup" = compose several
  one-thing passes; never write a single pass that "does the
  cleanup."
- **The `optimize` bundle runs after every major pass.** This is
  intentional: const folding after inline exposes new const branches;
  DCE after const eval kills dead code; etc.
- **Sig changes (e.g., SROA-promoting a function's return) require
  verification across ALL callers.** Roll back on first unsafe use.
  Aborting cleanly is always preferable to a half-applied transform.
- **Cross-function fixpoint** lives in `sroa::run` — analyses
  iterate until no function's outcome changes, then verify, then
  rewrite. Pattern that other whole-module passes (e.g., a future
  inliner-with-cost-model) can follow.
- **Disabling passes is cheap.** If a pass misbehaves, gate it off
  in `run_full_pipeline` and keep going; the program still works.
