# Compiler architecture

## Design goal

Three principles, in priority order:

1. **Correctness by construction.** The front-end emits SSA that runs
   correctly and leaks no memory, with zero optimization passes. The
   `main` pipeline can be reduced to `lower → eval` and produce
   correct (slow, memory-wasteful) output. Every optimization pass is
   *optional* and *removes* work, never adds correctness.
2. **One responsibility per module.** A pass is identified by the
   single SSA property it changes: it constructs an invariant, or
   eliminates a kind of redundancy. No "kitchen-sink" passes.
3. **Invariants are construction-time.** Every invariant is established
   exactly once (by the pass whose job it is) and preserved by every
   downstream pass. Re-establishing invariants mid-pipeline (today's
   double-`ssa_construct`) is a bug to be eliminated.

## Pipeline shape

```
source
  ↓ parse + frontend passes        (unchanged from today)
  ↓ ast::Module (monomorphic, lifted, specialized)
  ↓
  ↓ lower::*                       SSA construction
  ↓ ssa::Module                    Invariants established: see below
  ↓
  ↓ opt::*                         Optimization (every pass optional)
  ↓ ssa::Module                    Invariants preserved
  ↓
  ↓ eval                           Runtime result
```

## Core types — `src/ssa/`

The IR is shared by both `lower` and `opt`. Stays in `src/ssa/`.

- `Value { id, ty }` — SSA value, identity on `id`, type on every value.
- `BlockId`, `Block { params, insts, terminator }`.
- `Inst` — operations (Const, BinOp, Call, Alloc, Load, Store, RcInc,
  RcDec, Pack, Extract, Insert, BitCast, Cast, Reset, Reuse, …).
- `Terminator` — Return, Jump, Branch, SwitchInt.
- `BlockEdge { target, args }`.
- `Function { params, blocks, param_layouts, return_layout }`.
- `Layout` — slot-types per heap object (nested via `LayoutId`).
- `Module { functions, statics }`.
- `eval` — interpreter, sole authority on runtime semantics.

`ssa/` owns *types* and *invariant checkers* (`validate.rs`).
Construction logic lives in `lower/`, transformation in `opt/`.

## Front-end — `src/lower/`

A folder, not a single file. Each module does one thing and produces
a defined invariant on the SSA it sees.

```
src/lower/
├── mod.rs           orchestration: ast → ssa::Module
├── expr.rs          expression dispatch (let, if, match, call)
├── pattern.rs       pattern compilation → branch trees
├── constructor.rs   tag-union construction & destructuring
├── loop_walk.rs     List.walk / List.walk_until → SSA loops
├── list_ops.rs      List builtins (append, reverse, set, range, ...)
├── ssa_form.rs      explicit block-param threading (today: ssa_construct)
├── rc_emit.rs       naïve Perceus RC emission (replaces emit_drops)
├── layout.rs        layout assignment to every Ptr value
└── static_lift.rs   compile-time-known data → .statics
```

Each module is small (target <500 LOC) and tested independently.

### Lower invariants (post-`lower::*`)

After lowering, the SSA satisfies all of:

1. **Block-param scoping.** Every cross-block value reference is via
   explicit block-arg forwarding. No implicit scoping. *(Established
   by `ssa_form`.)*
2. **Concrete types.** Every Value carries its `ScalarType`. No type
   ambiguity at any use site.
3. **Naïve RC traffic.** Every Ptr value has explicit `RcInc` before
   each non-last consuming use, `RcDec` at scope-end where the last
   use was a borrow, and `RcInc` after each Ptr-returning Load
   (owning-load convention). *(Established by `rc_emit`.)*
4. **Layout on every Ptr.** Every Ptr value has an associated
   `LayoutId` recording its slot shape (including nested Ptr
   children). *(Established by `layout`.)*
5. **Statics extracted.** Compile-time-known data lives in
   `Module::statics`; references go through `StaticRef`. *(Established
   by `static_lift`.)*

### Pass order

```
ast → expr+pattern+constructor+loop_walk+list_ops    # emits naïve SSA
    → ssa_form                                       # explicit block params
    → layout                                         # attach LayoutId to Ptrs
    → rc_emit                                        # naïve Perceus RC
    → static_lift                                    # hoist literals
```

`rc_emit` runs after `ssa_form` so liveness across explicit block
edges is well-defined. `layout` runs before `rc_emit` so RC emission
can use layouts for cascade decisions.

### Key algorithms

- **`ssa_form`** — liveness fixpoint per block; insert missing
  block-params; rewrite cross-block uses to local references. The
  current `ssa_construct.rs` algorithm, modularized.
- **`rc_emit`** — for each Ptr value: classify each operand-use as
  *consuming* (Call arg, Store/StoreDyn val, Pack/Insert field,
  RcDec, terminator edge args) or *borrowing* (Load, BinOp,
  Extract agg, ...). Emit `RcInc(v)` before every non-last consuming
  use; emit `RcDec(v)` at scope-end iff the last use was a borrow;
  emit `RcInc(dest)` after each Ptr-returning Load.
- **`layout`** — derive each Ptr value's `LayoutId` from its source:
  Alloc size + Store types for locals; type-derived nested layouts
  for constructor allocs; function signature for params/returns.

## Mid-end — `src/opt/`

Every pass is `Module → Module`, optional, and removes redundancy
that `lower` introduced naïvely. Disabling all of `opt/` produces a
working (slow) program. **Each pass identifies and removes a single
kind of redundancy.**

```
src/opt/
├── mod.rs               configurable pipeline
├── dce.rs               dead code & dead blocks
├── const_fold.rs        scalar constant folding
├── jump_threading.rs    chain redundant jumps
├── branch_fold.rs       branch on constant → jump
├── merge_blocks.rs      collapse single-pred linear chains
├── inline.rs            small function inlining
├── static_promote.rs    Alloc of known data → StaticRef
├── rc_fuse.rs           cancel adjacent RcInc(v)/RcDec(v) pairs
├── rc_elide_static.rs   remove RC ops on .statics references
├── rc_borrow_window.rs  collapse RcInc(v); use; RcDec(v) into bare use
├── rc_unique_elide.rs   remove RC traffic on whole-program-Unique values
├── rc_reuse.rs          RcDec(v) + Alloc(same shape) → Reset(v) + Reuse
├── rc_move_out.rs       mask Drop cascade for moved-out Ptr slots
├── rc_edge_drop.rs      split critical edges where Ptr values die
├── sig_layouts.rs       whole-program param/return layout inference
└── sig_borrow.rs        whole-program Borrowing/Transferring inference
```

Naming convention: `rc_*` for RC-elimination passes, `sig_*` for
whole-program inference, others are general SSA opt.

### Optimization invariants

Each pass preserves all lower-invariants and additionally guarantees
the elimination it's responsible for.

### Pipeline composition

`opt::mod.rs` exposes a configurable `OptLevel` (`O0` = none, `O1`
= local-only, `O2` = whole-program). A test harness can request
exactly the passes it wants.

## Migration plan

Stepped refactor; each step keeps 218 tests green.

| # | Step | Risk |
|---|------|------|
| 1 | Create `src/lower/` folder, move existing `ssa::lower` and `ssa::ssa_construct` into it as-is. Rewire imports. | low |
| 2 | Create `src/opt/` folder, move existing `ssa::opt`, `ssa::inline`, `ssa::const_eval`, `ssa::static_promote`, `ssa::rc` into it. | low |
| 3 | Move `ssa::layouts`, `ssa::param_usage` into `src/opt/sig_*.rs`. They're already whole-program optimizations. | low |
| 4 | Split `ssa::opt` (the kitchen-sink module) into per-pass files in `src/opt/`. | medium |
| 5 | Build `lower::rc_emit` (naïve Perceus emission). Gate behind a flag; verify tests pass with it enabled and `opt::rc_*` disabled. | medium |
| 6 | Delete `ssa::emit_drops`. Its responsibilities are now split across `lower::rc_emit` and the `opt::rc_*` passes. | medium |
| 7 | Move `lower::layout` to compute layouts from type info, not from post-hoc inference. Eliminate the layout pass in `opt/` (or keep as a cross-function refinement). | medium |
| 8 | Once all of `lower/` is in place, eliminate `ssa::ssa_construct` as a separately-runnable pass — it's just one module inside `lower/` now. | low |

After step 8, the public surface is exactly two folders: `lower/`
(turn the AST into correct SSA) and `opt/` (make it faster). The
`ssa/` module shrinks to types + interpreter + validator.

## What's deliberately NOT in this plan

- **A new IR.** SSA stays as-is. Only its construction and
  transformation move around.
- **A type system change.** Frontend passes (parse → mono) are out of
  scope.
- **Codegen.** The interpreter is the runtime today; this design works
  for any future native backend without change.
- **Region inference / linear types.** Discussed elsewhere; not part
  of the Perceus story.
