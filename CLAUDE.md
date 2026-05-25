# Ori

A total, pure, strict functional language whose thesis is **static memory
management** — Perceus-style refcounting plus FBIP, not as an
optimization but as the runtime model.

## Defining characteristics

- **Total** (System T family). No general recursion; structural recursion
  via `fold` over inductive types only. Termination is guaranteed by
  construction.
- **Pure and immutable.** No source-level mutation. All "updates" are
  functional; RC and FBIP manage memory invisibly.
- **Strict, left-to-right.** No laziness.
- **Lambda-lifted.** Every `Inst::Call` has a known top-level target by
  the time SSA runs. Call graph is acyclic except for self-loops from
  structural recursion — no mutual recursion across user functions.

## Memory and RC

- **Perceus refcounting.** Each heap object carries an `rc`; reaching 0
  frees it and cascade-rc_decs every RcPtr child field.
- **Auto-rc on Store and Load.** `Store(ptr, off, val)` with `val.ty ==
  RcPtr` auto-`rc_inc`s `val`; `Load`/`LoadDyn` of an RcPtr auto-`rc_inc`s
  the loaded value. Explicit `rc_inc`/`rc_dec` (placed by
  `lower/rc_emit`) balance these around consuming uses and scope ends.
- **FBIP** ("Functional But In-Place"). `list.append`, `list.set`, etc.
  lower to `cow_move_out` / `cow_store_dyn` / `cow_resize_dyn`. Runtime
  check: `rc == 1` → mutate in place; `rc > 1` → clone.

## SSA representation

- Two value kinds: **`RcPtr`** (heap object) and **`Agg(N)`** (register-
  resident tuple; `Pack` and static-index-only `Extract`). Lists and
  Strs are always `RcPtr` — two-tier `[len, cap, data_ptr]` header plus
  a dynamic data buffer. `Str = List(U8)`; there is no separate string
  primitive.
- Interpreter at `src/ssa/eval.rs`. Heap objects in `heap.objects[idx]`
  (rc-tracked, slot-reused via `free_list`). Aggs in `heap.aggs[handle]`
  (no rc, no lifecycle).
- `__main` is the ABI boundary to the Rust eval driver. Its return
  type must stay `RcPtr` (a `Result`); sig-changing optimizations must
  exclude it.

## `lower/` vs `opt/`

**`lower/` establishes the language's behavior. `opt/` only makes it
faster.** Deleting every pass under `opt/` leaves a correct, slower
program — this is a hard invariant, not a goal.

Concretely:

- Semantic guarantees (FBIP, leak-free RC, total termination, strict
  evaluation order) are enforced **by `lower/`'s emission choices.**
  If a behavior matters for correctness, the lowering must produce it
  directly — never rely on an opt pass to clean up.
- `opt/` passes find emergent patterns *within* the natural lowering
  (dead alloc elimination, scalar replacement, branch folding, rc
  fusion, cross-function sig changes). Each pass should be independently
  deletable.
- Anything that "looks like" an optimization but is semantically
  required (e.g. FBIP via `ReuseOrClone` / `cow_*`) belongs in `lower/`.
  Anything that recognizes a static-analysis opportunity (e.g. SROA
  promoting non-escaping allocs to `Pack`) belongs in `opt/`.

The motivation: keep the semantic surface in one place, so adding or
deleting opt passes is a low-risk activity and reasoning about
correctness doesn't span the whole pipeline. See `src/lower/README.md`
and `src/opt/README.md` for the per-module details.
