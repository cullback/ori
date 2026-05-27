# Plan: decompose aggregates out of SSA (Cranelift-style)

Status: planning, not started. Land this as the next major SSA refactor.

**Scope honesty.** This is multi-day, multi-session work. Even with this
plan, the agent will hit decisions that need user input — function
signature shape for closures, exact eval handling of multi-result
calls, etc. Treat stage boundaries (see "Order of operations") as
explicit checkpoints to stop and confirm, not as autonomous milestones.

## Context for a fresh session

Ori is a total, pure, strict functional language. See `CLAUDE.md` and
`notes/ARCHITECTURE.md` for the project shape. The pipeline is roughly:

```
parse → resolve → fold_lift → flatten_patterns → topo → infer
     → mono → lambda_lift → lambda_solve → lambda_specialize
     → reachable prune → lower (SSA) → opt → eval
```

The compiler is interpreter-only today — `ssa::eval` is the runtime.
There is no codegen backend yet. The plan is to eventually add:

1. Ori's own codegen
2. LLVM backend
3. Cranelift backend

This plan reshapes the SSA layer to be friendly to all three, with
Cranelift as the strictest constraint (no aggregate types in IR).

### Today's SSA, in one paragraph

Two value kinds: **`RcPtr`** (heap object, rc-tracked) and **`Agg(N)`**
(register-resident tuple of N scalar fields). `Pack(d, fields)` builds
an Agg; `Extract(d, agg, i)` reads field `i`. The runtime mirror is
`Scalar::Agg(Vec<Scalar>)`. SROA promotes non-escaping heap allocs to
register Aggs. RC on an Agg cascades through its `RcPtr` fields at
runtime (the `Vec<Scalar>` self-describes). See `src/ssa/instruction.rs`
for `ScalarType::Agg(usize)` and `src/lower/README.md` for the
lower-stage rules.

### Why this needs to change

Three forces:

1. **Aggregate validation is weak.** `ScalarType::Agg(n)` carries only
   arity; field types are recoverable from the defining `Pack` (use-def
   in SSA), but the validator doesn't currently consult them. Type-lies
   like "Pack of `[I64, Ptr]` then Extract index 0 as `RcPtr`" slip
   through static checking and only surface at eval or as soft-validation
   warnings. This isn't urgent but it's a real gap.

2. **Cranelift target requires decomposition.** Cranelift IR has no
   aggregate type at all. Multi-value returns exist (`inst_results()` is
   a slice), but tuples-as-IR-values don't. Compound data lives in stack
   slots or heap. WASM made the same choice independently and adopted
   multi-value as its tuple-shaped story. So targeting Cranelift means
   decomposing aggregates regardless of what Ori's IR shape is — better
   to do it once in SSA than twice (once in SSA, once in lowering-to-CLIF).

3. **LLVM target is fine either way.** LLVM has structural aggregates
   (`{i32, i64}` literal structs, `%Foo = type {i32, i64}` nominal
   structs). Decomposed values work fine via multi-value calls and
   `insertvalue`/`extractvalue` if reaggregation is ever wanted. So
   LLVM doesn't push back against the Cranelift-shaped IR.

### Why Ori doesn't need stack slots

Cranelift's compound-data trichotomy is: register scalars / stack slots
/ heap. Stack slots exist because Rust takes addresses of locals via
`&mut`. Ori is **pure** — no `&mut`, no address-taking at the SSA level.
So Ori's trichotomy collapses to a dichotomy: **decomposed parallel
scalars** (in-flight, register-resident) or **heap** (escaped, shared,
or RC-tracked). No third tier. This is *strictly simpler* than
Cranelift's model.

Perceus/FBIP doesn't change this:

- RC inc/dec operates on `RcPtr`s — heap pointers that already have
  addresses. No register-value addressing involved.
- `cow_store_dyn` / `cow_move_out` / `cow_resize_dyn` all operate on
  `RcPtr`. They are the entire reason heap stays for shared/mutable-via-
  reuse data.
- In-place field update on a decomposed record is just value substitution
  (`replace value_k with newval`). No store, no RC, no COW machinery.

### What about large data / register pressure?

Two distinct worries to separate:

- **Bulk collections (lists, "1000-element arrays").** Ori doesn't have
  a fixed-size array type. Collections are `List(T)`, which is *always*
  a single `RcPtr` to a heap-allocated `[len, cap, data_ptr]` header
  plus a dynamic data buffer. A 1000-element list is one `RcPtr` Value
  at the SSA layer regardless. **Decomposition does NOT touch lists**
  — they stay as one RcPtr per list.

  (Note: one could in principle decompose the List *header* into three
  register Values — `len: U64`, `cap: U64`, `data_ptr: RcPtr` to the
  data buffer — saving the header allocation. This would shift FBIP's
  "is this uniquely owned" check from the header's rc to the data
  buffer's rc, which is a load-bearing semantic change. **That's a
  separate, future refactor**, not part of this plan. This plan only
  decomposes anonymous structural data (tuples, records); it leaves
  List/Str/other RC-managed runtime objects as one RcPtr each.)
- **Large records (say, 30 fields).** Decomposition produces 30
  parallel `Value`s. At the SSA layer this is fine — `Function::params`
  is just a longer `Vec<Value>`, env has 30 more entries, no semantic
  problem. At the *backend* layer (Cranelift, LLVM, native), the
  register allocator spills to stack when out of physical registers.
  That's the backend's job, not the SSA layer's. Ori's SSA has
  unlimited Values by design.

So **stack slots are a backend concern, not an SSA concern.** When
Ori's SSA → CLIF lowering is written, the CLIF emitter synthesizes
Cranelift stack slots for Values that don't fit in real registers.
The SSA doesn't need to model that.

If Ori ever grows fixed-size arrays (`[I64; N]`), the natural choice
is "always heap" like Lists — not "decompose into N register Values"
which would be silly for large N. That decision lives in front-end
type design, not in the SSA layer.

If a real workload later demands stack slots in SSA (e.g., a 100-field
record updated in a tight loop where both heap and decomposition are
wasteful), they're an *additive* extension: add `StackAlloc`,
`StackLoad`, `StackStore` instructions later. No impact on existing
SSA. Defer until a real program needs it.

## Target IR shape — concrete enum diff

### `ScalarType`

```rust
// BEFORE
pub enum ScalarType {
    I8, U8, I16, U16, I32, U32, I64, U64, F64,
    Ptr, RcPtr,
    Agg(usize),   // ← delete
}

// AFTER
pub enum ScalarType {
    I8, U8, I16, U16, I32, U32, I64, U64, F64,
    Ptr, RcPtr,
}
```

`byte_width()` loses its `Agg(_) => panic!` arm. `compute_layout` and
`total_byte_size` are unchanged (they're about heap layout). `is_heap_ptr()`
unchanged.

### `Inst`

```rust
pub enum Inst {
    // ── Single-result ──
    Const(Value, u64),
    BinOp(Value, BinaryOp, Value, Value),
    Alloc(Value, usize),
    AllocDyn(Value, Value),
    Load(Value, Value, usize),
    LoadDyn(Value, Value, Value),
    CowStore(Value, Value, usize, Value),
    CowStoreDyn(Value, Value, Value, Value),
    CowResizeDyn(Value, Value, Value),
    StaticRef(Value, usize),
    Cast(Value, Value),
    BitCast(Value, Value),

    // ── Zero-result (side-effecting) ──
    Store(Value, usize, Value),
    StoreDyn(Value, Value, Value),
    RcInc(Value),
    RcDec(Value),

    // ── Multi-result (CHANGED shape) ──
    Call { results: Vec<Value>, target: String, args: Vec<Value> },
    CowMoveOut { results: [Value; 2], src: Value, offset: usize },

    // ── DELETED ──
    // Pack(Value, Vec<Value>),
    // Extract(Value, Value, usize),
}
```

Two variants gain explicit multi-result shape:

- **`Call`**: a function returning a tuple now produces multiple `Value`s.
  Struct-style fields `{ results: Vec<Value>, target: String, args: Vec<Value> }`
  for clarity. `results.len()` matches the callee's `Function::return_type.len()`.
- **`CowMoveOut`**: today returns `Agg(2)` of `(out_ptr, extracted_val)`.
  Stays as **one fused instruction with two results** — the slot-nulling
  and rc-prep must happen atomically, can't split. Fixed-arity so `[Value; 2]`
  not `Vec<Value>`. Don't be tempted to split it into `CowPrep + MoveOut` —
  that pair was deleted in commit `4278d0a` for good reason (the prep and
  extract have to see consistent rc state).

`Pack` and `Extract` go away entirely. They're never emitted because
tuples/records are already N parallel `Value`s by the time SSA exists.

### `dests()` API

```rust
impl Inst {
    /// All Values defined by this instruction. Empty for side-effecting ops.
    pub fn dests(&self) -> &[Value] {
        match self {
            Self::Const(v, _)
            | Self::BinOp(v, ..)
            | Self::Alloc(v, _)
            | Self::AllocDyn(v, _)
            | Self::Load(v, ..)
            | Self::LoadDyn(v, ..)
            | Self::CowStore(v, ..)
            | Self::CowStoreDyn(v, ..)
            | Self::CowResizeDyn(v, ..)
            | Self::StaticRef(v, _)
            | Self::Cast(v, _)
            | Self::BitCast(v, _) => std::slice::from_ref(v),

            Self::Call { results, .. } => results,
            Self::CowMoveOut { results, .. } => results,  // [Value; 2] Derefs to &[Value]

            Self::Store(..) | Self::StoreDyn(..)
            | Self::RcInc(_) | Self::RcDec(_) => &[],
        }
    }

    pub fn dests_mut(&mut self) -> &mut [Value] { /* mirror */ }
}
```

`Option<Value>` is gone. Most callers want to iterate, which works
uniformly. The few callers that asserted single-result get a
`debug_assert_eq!(inst.dests().len(), 1)` and pick `dests()[0]`.

### `Function`

```rust
pub struct Function {
    pub name: String,
    pub params: Vec<Value>,           // already Vec — just more entries
    pub blocks: BTreeMap<BlockId, Block>,
    pub return_type: Vec<ScalarType>, // ← was ScalarType; now Vec
    pub entry: BlockId,
    pub next_block: usize,
}
```

`return_type: Vec<ScalarType>` — one entry for single-value returns,
N entries for multi-value. `__main` keeps a single-entry `vec![RcPtr]`.

### `Terminator::Return`

```rust
// BEFORE
Return(Value),

// AFTER
Return(Vec<Value>),
```

Arity must match the function's `return_type.len()`. Validator checks
this.

### `Block::params` and `BlockEdge::args`

**No structural change.** Both are already `Vec<Value>` — an `Agg(n)`
param just becomes n separate entries in the same Vec. Lower's
interpretation changes; the IR shape doesn't.

### `Scalar` (runtime, in `src/ssa/eval.rs`)

```rust
// BEFORE
pub enum Scalar {
    I8(i8), U8(u8), ...
    F64(f64),
    Ptr(HeapId),
    RcPtr(HeapId),
    Agg(Vec<Scalar>),  // ← delete
}
```

`Scalar::Agg` is gone. Eval never has a multi-Scalar bundle as one
Scalar. The env is `HashMap<Value, Scalar>` — multi-result instructions
just insert N entries, one per result Value. Search eval for `Scalar::Agg`,
`is_agg`, `Pack`, `Extract` and remove each handler.

## Lower's emission decision (the key piece)

Lower picks emission mode for each tuple/record construction based on
the *immediate use context*. The decision is local and structural — no
global escape analysis needed at lower time.

| Use context | Emission |
|---|---|
| Immediately destructured (`(x, y) = (a, b)`) | Parallel Values, no instructions emitted |
| Passed to a function whose sig declares multi-slot | Parallel Values, fed into the `Call.args` |
| Returned from current function (sig declares multi-slot) | Parallel Values, fed into `Return(...)` |
| Stored into a list slot, heap field, or closure capture | Heap-materialize: `Alloc + Store + Store + ...` |
| Bound to a name with mixed escape/non-escape uses | Conservatively heap-materialize (safe default) |

Lower has the source `Type` for every expression — it already knows
whether the destination is a function param, a list slot, a closure
capture. So the decision is just "look at the immediate parent expr's
shape and pick."

**Field access on decomposed:** if `r = (a, b, c)` is decomposed (three
parallel Values), then `r.b` (or `r.1`) is literally the second Value.
No Load, no Extract — just name resolution.

**Field access on heap:** if `r` is heap-materialized, `r.b` lowers
to a `Load` at the appropriate offset, exactly as today.

**Record update on decomposed:** `{ r | b: newval }` where `r` is
decomposed is `(value_a, newval, value_c)` — pure value substitution.

**Record update on heap:** lowers to `CowStore` as today.

## Concrete before/after example

Today, `(a, b) = pair; a + b` where pair is heap:

```
v0 = Alloc(16)
Store(v0, 0, va)
Store(v0, 8, vb)
... (pair leaves the construction site)
v3 = Load(v0, 0)       // extract field 0
v4 = Load(v0, 8)       // extract field 1
RcDec(v0)
v5 = BinOp(v3, Add, v4)
Return(v5)
```

After SROA (today), if pair doesn't escape:

```
v0 = Pack([va, vb])    // register-resident Agg(2)
v3 = Extract(v0, 0)
v4 = Extract(v0, 1)
v5 = BinOp(v3, Add, v4)
Return(v5)
```

Tomorrow, lower emits directly:

```
v5 = BinOp(va, Add, vb)
Return(v5)
```

Three instructions instead of nine (today's heap path) or five (today's
post-SROA path). **No allocation, no Pack, no Extract — the tuple existed
only as a syntactic grouping at the source level.**

## Concrete file-level changes

### Core SSA

- `src/ssa/instruction.rs` — remove `ScalarType::Agg(usize)`, the
  `Pack` and `Extract` variants. Change `Inst::Call` to struct-style
  with `results: Vec<Value>`. Change `Inst::CowMoveOut` to struct-style
  with `results: [Value; 2]`. Add `dests()` / `dests_mut()`. Update
  `operands()` and `map_operands_mut()` to remove Pack/Extract arms.
- `src/ssa/mod.rs` — `Function::return_type: Vec<ScalarType>`.
- `src/ssa/eval.rs` — remove `Scalar::Agg`, the Pack/Extract handlers,
  the Agg-cascade in RcDec. Update Call handling: a Call instruction
  assigns one Scalar per result Value, in order.
- `src/ssa/validate.rs` — drop Agg-arity checks. Add: `Return.values.len()
  == func.return_type.len()` and per-position type match. `Call.results.len()
  == callee.return_type.len()`. Block-join checks: each predecessor's
  `BlockEdge.args.len() == target_block.params.len()`.
- `src/ssa/display.rs` — drop Agg formatting, update Call/Return printing
  for multi-result/multi-value.
- `src/ssa/builder.rs` — update `add_inst` and call-builder helpers
  for multi-result.

### Lower stage

- `src/lower/mod.rs` — tuple literal, record literal, multi-value
  function return all produce N Values. Implement the emission
  decision table above. Tuple/record field access checks whether
  source is decomposed (look up in lower's local table) or heap
  (emit Load).
- `src/lower/pattern.rs` — destructuring is bind-N-Values instead of
  alloc + Extract. Patterns on heap records still emit Loads.
- `src/lower/rc_emit.rs` — drop the `Agg(_)` case in `needs_rc_emit`.
  RC emission applies only to `Ptr | RcPtr`. End-of-life of a
  decomposed tuple decrements each RcPtr-typed Value individually.
- `src/lower/call.rs` — emit calls with multi-result destinations.
  Caller-side: if the call returns multi-value, bind each result to
  its own local.
- `src/lower/walk.rs` — adjust traversal helpers.
- `src/lower/README.md` — update to document the decomposition model
  and the emission decision table.

### Opt passes

- `src/opt/sroa.rs` — biggest rewrite. Today it's "alloc → Pack."
  Tomorrow it's "materialize-to-heap on escape" — but if lower's
  emission decision is good, much of this may be unnecessary.
  **Survey first**: how often does today's SROA fire on a decomposable
  pattern that lower could have caught earlier? If most cases, sroa
  shrinks dramatically or deletes. If few, it stays as the materialize-
  on-escape pass.
- `src/opt/inline.rs`, `src/opt/jump_threading.rs`,
  `src/opt/const_eval.rs`, `src/opt/const_fold.rs` — adjust any
  pattern-matches on `Pack` / `Extract`. Should mostly just delete
  cases.
- `src/opt/static_promote.rs` — review for Agg assumptions.

### Closures

- `src/passes/lambda_specialize.rs` — `__apply_K` dispatchers take
  expanded capture sigs. Each closure shape specializes to N param
  slots instead of one Agg. Closures whose env contains tuples need
  N captures per tuple; closures with heap-typed env stay as today
  (one RcPtr capture).
- `src/passes/lambda_lift.rs`, `src/passes/lambda_solve.rs` — adjust
  capture-shape representation. The shape decision (decomposed vs
  heap env) may itself depend on how long the closure lives —
  long-lived closures probably want heap env to avoid blowing up
  the dispatch table.

### Mono / specialization

- `src/passes/mono.rs` — verify nothing assumes Agg-typed args/returns
  in specialization. The mangled name for a polymorphic function
  taking `(I64, Ptr)` becomes the same as taking `I64, Ptr` (since
  those produce the same expanded sig at the SSA layer).

### Documentation

- `CLAUDE.md` — currently documents `Agg(N)` prominently in the SSA
  representation section. Rewrite that section to describe the
  decomposed model. Lines to find: "Two value kinds: **`RcPtr`**...
  and **`Agg(N)`**..." — that whole paragraph needs replacing.
- `src/lower/README.md` — update per above.
- `src/opt/README.md` — update SROA description.

### Tests

- `src/test_frontend.rs` — many tests will pass through unchanged.
  Look for tests that assert specific SSA shapes (Pack/Extract in dumps,
  `peak_live` counts that depend on Agg vs heap promotion). Update
  assertions where the new shape is structurally different.
- Snapshot/audit tests under `tests/` may need regeneration.
- `audit_ssa_cleanliness*` ignored tests inspect SSA structure; will
  likely need updating.

## Order of operations

Each stage must compile and tests must pass before moving on. **Stop
at each stage boundary and confirm with the user before proceeding.**

1. **Multi-result `Inst::Call` infrastructure.** Change `Inst::Call`
   to struct-style with `results: Vec<Value>`. Update eval, builder,
   validator, display. **Don't change any callsites yet** — keep them
   producing single-element `results: vec![v]`. Verify test suite
   still passes. This is pure plumbing.

2. **`Function::return_type: Vec<ScalarType>` and `Terminator::Return(Vec<Value>)`.**
   Pure plumbing, single-element for now.

3. **`Inst::CowMoveOut` to struct-style with `[Value; 2]`.** Update
   the one site that emits it and the one site in eval. Verify tests.

4. **Decompose tuples in lower.** Tuple literal lowering produces N
   parallel Values. Tuple destructuring binds to those Values. Tuple
   field access (where source is decomposed) is name resolution, no
   instruction emitted. Tuple-passed-as-arg / tuple-as-return:
   expand into multi-slot. Test suite should still pass with the
   new shape.

5. **Decompose records in lower.** Same treatment for non-escaping
   record literals.

6. **Closures and `lambda_specialize`.** Update capture shapes.
   Decide per-closure whether to use decomposed or heap env (see
   "Risk areas" below).

7. **Delete `ScalarType::Agg`, `Pack`, `Extract`, `Scalar::Agg`.**
   At this point nothing should produce them; the deletion is just
   removing dead code. Update `dests()` to lose the Pack/Extract
   arms. Update `display.rs` similarly.

8. **SROA: survey and either shrink to materialize-on-escape or
   delete entirely.** Depends on what lower's emission decision
   already covers.

9. **Update `CLAUDE.md`, `src/lower/README.md`, `src/opt/README.md`.**
   Document the new model.

## Verification beyond `cargo test`

Tests passing is necessary but not sufficient. After each non-trivial
stage, also run:

- **AoC programs:** `cargo run -- programs/aoc/201501.ori`,
  `programs/aoc/201502.ori`, etc. They should produce identical output.
  These exercise tuple-heavy parser stdlib code.
- **MD5 benchmark:** `cargo run -- programs/bench_md5.ori` (if present).
  Hashrate should not regress; if it improves significantly, that's
  the decomposition paying off. If it regresses, lower's emission
  decision is missing cases.
- **`peak_live` smoke check:** `run_with_heap` in `test_frontend.rs`
  tracks `heap.peak_live`. Programs that previously hit `peak_live` of
  ~25 (md5-like) should stay low or get lower. A regression here means
  the decomposition isn't actually avoiding heap allocations.
- **SSA dump sanity:** pick a few small programs and dump SSA (via
  `--dump-ssa` if it exists, or inspect via a unit test). Confirm
  Pack/Extract are absent and Call/Return have the expected multi-
  result shape.

Use `cargo test --quiet -- --ignored` to also run the audit tests
(`audit_ssa_cleanliness*`); they're a good structural check.

## Risk areas / open questions

- **Multi-result instruction representation.** Decided above: struct-style
  with `results: Vec<Value>` for `Call`, `[Value; 2]` for `CowMoveOut`.
  Single-result instructions keep their `Value` field. `dests()` returns
  `&[Value]` uniformly. Verify when implementing whether any pass
  needs a "single-result fast path" — most callers iterating over dests
  is fine.

- **Closure capture expansion.** A closure capturing a 4-tuple env
  becomes a `__apply_K` with 4 expanded param slots. Two design points
  to confirm during stage 6:
  - **Does this blow up the closure dispatch table?** Each closure
    shape specializes. If a function captures 5 different tuples-of-3,
    that's 5 specializations. Probably fine — `lambda_specialize`
    already does this — but verify.
  - **Should long-lived closures heap-materialize their env?** A
    closure escaping into a list of closures probably wants heap env
    (one RcPtr capture) rather than blowing up the param list. Likely
    yes; this is the escape decision applied to closure envs.

- **Recursive types via heap.** Lists of records: each element is a
  heap allocation. That stays. Records that contain RcPtr children
  *can* still be decomposed if they don't escape — each RcPtr child
  is its own Value, still RC-tracked individually. Only escape
  triggers heap materialization.

- **FBIP for records.** Today `record.x = newval` lowers to
  `cow_store_dyn` on the record's RcPtr. After decomposition, if the
  record is N parallel Values, the update is pure value substitution
  (replace `value_k` with `newval`). The COW path is only used for
  records on heap (escaped / shared / list-element). This means FBIP
  applies in fewer cases — but in the cases where it applied before,
  the post-decomposition version is *strictly faster* (no rc check,
  no store, just register update). The shrinking of FBIP's domain is
  net good.

- **`__main` ABI.** `__main` returns `RcPtr` (a Result). That stays
  — it's the eval driver boundary. Just don't decompose the return
  value of `__main`. Its `return_type` is `vec![RcPtr]` (one entry).

- **Mixed-use names.** A let-bound tuple where some uses destructure
  locally and other uses pass it to a heap-storing context. The
  decision table says "conservatively heap-materialize." A future opt
  could do per-use analysis, but defer.

- **Display/dump verbosity.** Functions with expanded sigs will be
  noisier in SSA dumps. If this bites readability hard, consider
  adding optional "groups" metadata (purely cosmetic) so dumps can
  show `foo: (I64, {I64, Ptr}) -> {I64, Ptr}` while the IR itself
  has the flat shape. Not load-bearing — defer until needed.

## What this enables

- **Cleaner validation.** Every Value has a primitive type. Pack/Extract
  arity gap disappears.
- **Easier targeting.** Cranelift backend has near-1:1 mapping. WASM
  backend free-rides. LLVM backend can either pass multi-value or
  reaggregate via `insertvalue`.
- **Simpler runtime.** `Scalar` enum shrinks; no recursive `Vec<Scalar>`
  variant; eval gets faster on tuples (no heap allocation on the env
  side either).
- **Honest FBIP scope.** COW machinery applies only to genuinely-shared
  heap data; in-flight value updates are just substitutions.

## What this doesn't enable

- This is **not** a codegen project. Targeting Cranelift/LLVM/WASM
  comes after this lands. This refactor just sets the shape.
- **No language-level changes.** Source-level tuples, records, opaque
  types behave identically. Only the SSA layer changes.

## Getting started in a fresh session

1. Read this file (the whole thing).
2. Read `CLAUDE.md` for language overview — note that the "SSA
   representation" section is about to change.
3. Read `src/ssa/instruction.rs` for current ScalarType / Inst shape.
4. Read `src/ssa/mod.rs` for Function/Block/Terminator.
5. Read `src/ssa/eval.rs` for Scalar and the eval handlers that need
   updating.
6. Read `src/lower/README.md` for lower's semantic guarantees.
7. Read `src/opt/sroa.rs` since it's the biggest pass affected (and
   may be deleted at the end).
8. Run `cargo test --quiet` to confirm 229 passing baseline.
9. Start stage 1 (`Inst::Call` to struct-style). Land it. Confirm
   with user before moving to stage 2.

The full test suite is `cargo test --quiet` (currently 229 passing,
4 ignored audit tests). Run `cargo test --quiet -- --ignored` for the
audit tests separately.
