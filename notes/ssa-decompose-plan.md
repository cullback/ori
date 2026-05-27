# Plan: decompose aggregates out of SSA (Cranelift-style)

Status: planning, not started. Land this as the next major SSA refactor.

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

## Target IR shape

After the refactor:

### ScalarType (simpler)

```rust
pub enum ScalarType {
    I8, U8, I16, U16, I32, U32, I64, U64, F64,
    Ptr,    // raw 8-byte pointer (no RC)
    RcPtr,  // heap pointer, RC-tracked
}
```

No `Agg(n)`. Every Value has a primitive type. Hash/eq/Copy stay cheap.

### Instructions

- **Delete `Inst::Pack`.** Multi-Value bundles aren't constructed —
  they just exist as parallel Values from the start.
- **Delete `Inst::Extract`.** A Value that was Extract result is now
  one of the original parallel Values; uses reference the source Value
  directly.
- **Multi-result calls.** `Inst::Call` produces N result Values, not
  one. The instruction shape probably becomes
  `Call { target, args, results: Vec<Value> }` or similar; pick a
  representation that matches eval's `assign_inst_results` shape.

### Block params and function sigs

- A block param that was `Agg(n)` becomes n parallel params.
- A function param/return slot that was `Agg(n)` becomes n parallel
  slots. `foo: (I64, Pair) -> Pair` becomes `foo: (I64, I64, Ptr) -> (I64, Ptr)`.

### Runtime

- Delete `Scalar::Agg(Vec<Scalar>)`. Eval never sees a multi-value
  bundle as a single Scalar.
- RC cascade simplifies: only heap objects cascade through their
  RcPtr-typed slots (which the heap object's layout already describes).

### Escape analysis inverts

Today: lower emits heap allocations; SROA (`src/opt/sroa.rs`) promotes
non-escaping ones to register Aggs.

Tomorrow: **lower emits decomposed parallel Values by default**; if a
value escapes (captured by a long-lived closure, returned through an
opaque function pointer, stored in a heap collection), it gets
materialized to heap via an explicit allocation step.

This is "default to fast path, opt out for escape" instead of "default
to slow path, opt in for non-escape." Simpler and more honest about
what's actually fast.

## Concrete file-level changes

### Core SSA

- `src/ssa/instruction.rs` — remove `ScalarType::Agg(usize)`, the
  `Pack` and `Extract` variants. Update `Inst::Call` to multi-result.
- `src/ssa/eval.rs` — remove `Scalar::Agg`, the Pack/Extract handlers,
  the Agg-cascade in RcDec. Update Call handling for multi-result.
- `src/ssa/validate.rs` — drop Agg-arity checks; type checking becomes
  trivial (every Value primitive).
- `src/ssa/display.rs` — drop Agg formatting, update Call printing.

### Lower stage

- `src/lower/mod.rs` — tuple literal, record literal, multi-value
  function return, multi-value block param all produce N Values.
- `src/lower/pattern.rs` — destructuring is bind-N-Values instead of
  alloc + Extract.
- `src/lower/rc_emit.rs` — drop the `Agg(_)` case in `needs_rc_emit`.
  RC emission applies only to `Ptr | RcPtr`.
- `src/lower/call.rs` — emit calls with multi-result destinations.
- `src/lower/walk.rs` — adjust traversal helpers.

### Opt passes

- `src/opt/sroa.rs` — biggest rewrite. Today it's "alloc → Pack."
  Tomorrow it's "materialize-to-heap on escape." Connected-components
  escape analysis stays useful; the action it takes inverts. Might
  even shrink overall since the "Pack" half disappears.
- `src/opt/inline.rs`, `src/opt/jump_threading.rs`,
  `src/opt/const_eval.rs`, `src/opt/const_fold.rs` — adjust any
  pattern-matches on `Pack` / `Extract`. Should mostly just delete
  cases.
- `src/opt/static_promote.rs` — review for Agg assumptions.

### Closures

- `src/passes/lambda_specialize.rs` — `__apply_K` dispatchers take
  expanded capture sigs. Each closure shape specializes to N param
  slots instead of one Agg.
- `src/passes/lambda_lift.rs`, `src/passes/lambda_solve.rs` — adjust
  capture-shape representation.

### Mono / specialization

- `src/passes/mono.rs` — verify nothing assumes Agg-typed args/returns
  in specialization.

### Tests

- `src/test_frontend.rs` — many tests will pass through unchanged once
  lower emits the new shape. Look for tests that assert specific SSA
  shapes (Pack/Extract in dumps, `peak_live` counts that depend on Agg
  vs heap promotion).
- Snapshot/audit tests under `tests/` may need regeneration.

## Order of operations

Suggested staging — each stage compiles and tests pass before moving on.

1. **Multi-result `Inst::Call` infrastructure.** Don't change anything
   else yet; just thread `results: Vec<Value>` through Call. Today
   calls produce one Value (possibly typed `Agg`); make them produce
   one or more. Get the eval, validator, and dumps all happy with this.

2. **Decompose tuples in lower.** Tuple literal lowering produces N
   Values instead of one Agg. Destructuring binds N names from N
   Values. Most tests should continue to pass because tuples that
   would have been Agg are now multi-Value; nothing else changes
   semantically.

3. **Decompose records in lower.** Same treatment for non-escaping
   record literals. This is harder because records use field names,
   not positions. The decomposition is "Value per field in declaration
   order." Field access becomes "pick the i-th Value."

4. **Block params expand.** When control-flow joins produce
   multi-value, the join block has N params and each predecessor
   passes N args.

5. **Function sigs expand.** Functions returning or taking
   multi-Value get expanded sigs.

6. **Closures and lambda_specialize.** Update capture shapes.

7. **Delete `ScalarType::Agg`, `Pack`, `Extract`, `Scalar::Agg`.**
   At this point nothing should produce them; the deletion is just
   removing dead code.

8. **Invert SROA.** Today's "promote heap to Agg" becomes
   "materialize register Values to heap when they escape." Connected-
   components analysis stays; the action inverts.

## Risk areas / open questions

- **Multi-result instruction representation.** `Inst::Call` producing
  N results changes the value-id-assignment story. Some passes assume
  one instruction = one Value. Survey first; pick a shape that fits.
  Likely candidates: `Vec<Value>` field on Call, or a wrapper
  `MultiInst` that knows its result count.

- **Closure capture expansion.** A closure capturing a 4-tuple env
  becomes a `__apply_K` with 4 expanded param slots. The dispatch
  table that today indexes by closure ID needs to know each closure's
  expanded shape. Probably already specialized by `lambda_specialize`,
  but verify.

- **Recursive types via heap.** Lists of records: each element is a
  heap allocation. That stays. Records that contain RcPtr children
  ALSO stay on heap (they're not pure scalar bundles). The
  decomposition only applies to records whose fields are all scalar
  primitives or to short-lived in-flight records that don't reach a
  collection.

  Actually — even records with RcPtr fields can be decomposed if they
  don't escape. The RcPtr children are still RC-tracked individually
  (each is its own Value). Only escape triggers heap materialization.

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
  value of `__main`.

- **`Scalar::Agg`'s removal from eval.** Make sure no eval helper
  relies on it (search for `Scalar::Agg`, `is_agg`, etc.).

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

1. Read this file.
2. Read `CLAUDE.md` for language overview.
3. Read `src/ssa/instruction.rs` for current ScalarType / Inst shape.
4. Read `src/lower/README.md` for lower's semantic guarantees.
5. Read `src/opt/sroa.rs` since it's the biggest pass affected.
6. Start with stage 1 (multi-result `Inst::Call`). Run tests after
   each meaningful change. The full test suite is `cargo test --quiet`
   (currently 229 passing, 4 ignored audit tests).
