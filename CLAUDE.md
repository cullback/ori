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

## Surface syntax

- **Three type-declaration kinds**, distinguished by the operator:
  - `Foo : T` — **alias**, sugar with no nominal identity.
  - `Foo := T` — **transparent** newtype: nominal, but `T`'s internals
    are visible everywhere `Foo` is.
  - `Foo :: T` — **opaque** newtype: callers see `Foo` as its own
    type; `T` is hidden outside the methods block.
- **`.( methods )` block on a type decl.** `Foo := T.(...)` or
  `Foo :: T.(...)` attaches methods. Inside the block, *parameters and
  return values typed `Foo` auto-unwrap to `T`* — "opaque outside,
  transparent inside." This is the only way to define methods on a
  newtype.
- **Pattern matching** is `if expr : pat then body : pat then body
  else default`. There is no separate `match` keyword.
- **Guards** are introduced with `and` after a pattern:
  `: [x] and x > 0 then body`.
- **Return arms.** An arm can end in `return` instead of `then`. The
  body's value then returns from the *enclosing function*, not the
  match expression. (`?` desugars to a match where the `Err` arm is
  `return`.)
- **`?` operator** on a `Result` desugars to
  `if expr : Ok(v) then v : Err(e) return Err(e)` — yields the Ok
  payload, returns the function on Err.
- **`expect <bool>`** lines at module level are inline test
  assertions, executed by `ori test foo.ori`.

Implementation note: the "opaque outside / transparent inside"
semantics is implemented in inference, not lowering. `::` types are
registered in `engine.transparent` only for the duration of their own
method-body inference and removed immediately after. By the time
`InferResult.transparent` is exposed to lower/mono, only `:=` types
remain — so the field name is accurate (it is in fact transparent
types only), and `resolve_transparent` correctly returns the input
unchanged for opaque types at lower time. The "inside the `.()`
block" view never escapes inference.

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

- Two pointer kinds: **`RcPtr`** (heap object, rc-tracked) and **`Ptr`**
  (raw pointer; statics use this via the sentinel-rc convention).
  Scalar value kinds (`I8`–`U64`, `F64`) round it out — no aggregate
  type at the IR level.
- **Decomposed aggregates.** Tuples, records, single-variant tag unions,
  and closure environments lower to **parallel SSA Values**, not heap
  objects. A `(I64, Str)` is two Values; a record `{a: I64, b: I64}` is
  two Values; a single-variant `Wrapped(I64, Str)` is three Values.
  Multi-result `Inst::Call` and `Terminator::Return(Vec<Value>)` carry
  these across function boundaries. Heap stays for: variable-length
  buffers, multi-variant tag union payloads, and anything that escapes.
- **Lists and Strs.** `(len: U64, cap: U64, data: RcPtr)` decomposes
  into three parallel Values. The data buffer's elements are inlined
  per their decomposed shape: a `List(Record{a:I64, b:I64})` buffer
  has 16-byte slots; `List(Str)` has 24-byte slots. `Str = List(U8)`;
  no separate string primitive.
- **Multi-variant tag unions** lower to `(tag: U64, payload_ptr: RcPtr)`
  — two parallel Values. The payload heap object holds variant-specific
  fields with no tag slot inside. Void variants use a null payload.
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
  (dead alloc elimination, branch folding, rc fusion, cross-function
  sig changes). Each pass should be independently deletable.
- Anything that "looks like" an optimization but is semantically
  required (e.g. FBIP via `ReuseOrClone` / `cow_*`, decomposed
  aggregate emission) belongs in `lower/`. Anything that recognizes
  a static-analysis opportunity belongs in `opt/`.

The motivation: keep the semantic surface in one place, so adding or
deleting opt passes is a low-risk activity and reasoning about
correctness doesn't span the whole pipeline. See `src/lower/README.md`
and `src/opt/README.md` for the per-module details.
