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
  `Foo :: T.(...)` attaches methods. Inside the block, _parameters and
  return values typed `Foo` auto-unwrap to `T`_ — "opaque outside,
  transparent inside." This is the only way to define methods on a
  newtype.
- **Pattern matching** is `if expr : pat then body : pat then body
  else default`. There is no separate `match` keyword.
- **Guards** are introduced with `and` after a pattern:
  `: [x] and x > 0 then body`.
- **Return arms.** An arm can end in `return` instead of `then`. The
  body's value then returns from the _enclosing function_, not the
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

## Pipeline layers

Each layer has one job. Code that doesn't fit a layer's job goes in
the wrong layer.

| Layer          | Job                                                                                |
| -------------- | ---------------------------------------------------------------------------------- |
| `src/syntax/`  | text → AST (grammar lives here)                                                    |
| `src/passes/`  | AST → AST transforms (`resolve`, `mono`, `lambda::lift`, `flatten_patterns`, etc.) |
| `src/types/`   | type inference + unification                                                       |
| `src/lower/`   | AST → SSA. **Establishes language semantics 1:1.**                                 |
| `src/opt/`     | SSA → SSA equivalence-preserving rewrites.                                         |
| `src/codegen/` | SSA → bytes (instructions + ELF/Mach-O container).                                 |

**`lower/` establishes the language's behavior. `opt/` only makes it
faster.** Deleting every pass under `opt/` leaves a correct, slower
program — this is a hard invariant, not a goal. Semantic guarantees
(FBIP, leak-free RC, total termination, strict evaluation order) are
enforced by `lower/`'s emission choices; never rely on an opt pass
to clean up.

`opt/` passes find emergent patterns _within_ the natural lowering
(dead alloc elimination, branch folding, rc fusion, sig changes).
Each pass is independently deletable. Anything that "looks like" an
optimization but is semantically required (e.g. FBIP via `cow_*`,
decomposed aggregate emission) belongs in `lower/`.

See `src/lower/README.md` and `src/opt/README.md` for module details.

## Where optimizations go

**Rule of thumb:** **all SSA-to-SSA equivalence-preserving rewrites
belong in `src/opt/`.** They benefit every downstream consumer — eval
today, aarch64-linux codegen, a future macOS or x86_64 codegen, a
future bytecode interpreter — without duplication.

`src/codegen/` only hosts work that **exists because of target-specific
representation choices**:

- **Instruction selection.** The peephole-style choice of *which*
  machine instruction implements an SSA op (e.g. `add reg,reg,#imm`
  vs `add reg,reg,reg`; `ldr` immediate-offset vs register-offset).
- **Register allocation** — only meaningful when "registers" exist.
- **ABI lowering** — calling-convention reg placement, frame layout,
  LR save/restore, callee-saved spills.
- **Branch displacement / layout** — turning block labels into
  PC-relative byte offsets.
- **Properties that exist only in the machine model.** E.g.
  `KnownZeroHigh(N)` reasoning about 64-bit-register bit patterns
  for narrow SSA types. At the SSA level a `U32` is 32 bits, full
  stop; "the upper 32 bits of a 64-bit register" is a codegen artifact.

**Anti-pattern:** any optimization that reasons about SSA shape but
appears under `src/codegen/`. If you find yourself adding const-prop,
dead-branch elim, common-subexpression elim, or any other SSA-to-SSA
rewrite at codegen, **strengthen the SSA pass instead** — every
backend gets the benefit. Codegen-level lattices that pre-derive SSA
facts (e.g. `Const(_)`, `StaticRef(_)`) duplicate work that belongs
upstream; the only codegen-level facts that are legitimate are the
ones the SSA can't represent (`KnownZeroHigh`, allocation-site
identity for free-helper dispatch, etc.).

## Invariants and validation

Each pass documents its **pre-** and **post-conditions** at the
function level. `ssa::validate::validate` runs at every pass
boundary (see `check(module, "<pass>")` in `main.rs`). Validator
catches: unterminated blocks, block-arg arity mismatch, use-before-def,
mismatched Call arity / Return arity, mismatched types at use sites.

When the validator can't enforce an invariant: add an `assert!` at
the pass entry with the invariant in the message, and a regression
test that trips it if violated.

## Make illegal states unrepresentable

Prefer encoding invariants in types over `// INVARIANT:` comments +
runtime assertions:

- **Newtypes for distinct concepts.** `BlockId(usize)`, `VReg(u8)`,
  `Label::{Data,Block,Func}` already do this. If you write
  `// idx into module.functions`, wrap it.
- **Enums to enumerate cases.** `Terminator` makes "block without a
  terminator" unrepresentable; `MInst` makes "operand with wrong
  shape" unrepresentable. Reach for an enum before adding a flag arg.
- **Avoid sentinel values when an enum would do.** Eval-mode's
  `RC_STATIC = u64::MAX` is the canonical anti-example — works,
  but lets you accidentally overflow into "valid" rc. An
  `Rc::{Static, Counted(u32)}` enum would catch the mistake.
- **`Result<T,E>` for fallible ops.** Don't return `T` with a magic
  error value; don't panic in library code a caller might recover from.
- **Distinct types for distinct kinds.** `Ptr` vs `RcPtr` in SSA.
  Don't merge them — the distinction enforces the static-vs-heap
  flow at compile time.

When the type system can't carry the invariant, a builder API that
rejects invalid construction at the call site is the next best move.

## Gold-standard checklist

Use this when reviewing a pass or module, or cleaning one up:

- [ ] **Single responsibility.** The module's docstring states it in
      one sentence.
- [ ] **Pre/post invariants documented.** Function-level docs say what
      input shape is expected and what's guaranteed on output.
- [ ] **No silent correctness traps.** `debug_assert!` is for
      perf-critical checks whose violation is a bug but not a memory
      corruption. For correctness checks, use `assert!`.
- [ ] **No HashMap iteration order in observable output.** If
      iteration order affects emitted bytes, sort first.
- [ ] **No duplication across layers.** Const-prop in `opt/` AND
      `codegen/` is a smell — pick one home and reuse.
- [ ] **Independently deletable** (for opt passes).
- [ ] **Test fails if the pass is removed** (for lowering). If you
      delete the pass and the suite still passes, the test coverage
      is wrong, not the pass.
- [ ] **Regression test for every fixed bug.**
- [ ] **Comments explain _why_, not _what_.** Well-named identifiers
      carry "what." Hidden constraints, subtle invariants, and
      workarounds need comments. Don't reference current task,
      caller, or fix history — that rots.
- [ ] **No back-compat shims after the migration completes.** If you
      build a "transitional" two-API thing, remove the old API in
      the same change that finishes the migration.
