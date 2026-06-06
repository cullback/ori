# Core IR

## Status

Shipped. Lives in `src/passes/core/`:

- `expr.rs` — Core `Expr` type (11 variants), `Pattern` (3 variants),
  `Literal` (2 variants), `MatchArm`.
- `lower.rs` — AST → Core. Establishes language semantics 1:1.
  Where SROA happens, where desugars happen, where the buffer trio
  gets stamped.
- `to_ssa.rs` — Core → SSA. Resource discipline (RC, FBIP) lives
  here. Knows about the buffer trio at a structural level; lowers
  via `cow_*` for FBIP.
- `rules.rs` — algebraic rewrites on Core. Today: dead-let elim,
  add-zero / mul-one. The empirical gate (see below) is the
  trigger for adding more.
- `pipeline.rs` — drives the whole module through AST→Core →
  optional simplify → Core→SSA.

The original motivation was fusion (`xs.map(f).walk(g)` compiles to
one zero-alloc loop). The empirical gate on fusion **has not fired
yet** — the infrastructure is in place but no fusion rule has
demonstrated a win on a real Ori program. Most of what shipped is
IR plumbing, not optimization.

## The problem this solves

Ori's design hands you language guarantees that mainstream optimizing
compilers fight thousands of lines of engineering to recover:
totality, purity, strictness, lambda-lifted first-order calls, a DAG
call graph (no mutual recursion; the only recursion is structural
via `fold`), and **no aggregate identity** (no pointer-takes, no
record-by-reference equality, no FFI opacity, no varargs).

Those guarantees enable algebraic rewriting — fusion, case-of-case,
free theorems, hylomorphism deforestation, whole-program
specialization, compile-time evaluation of arbitrary closed terms —
to be **unconditional**. No side conditions, no ⊥-safety arguments,
no fixpoint over the call graph.

These rewrites are most naturally expressed on the **algebraic
structure of the program**: terms like `Map(f, Map(g, xs))`. By the
time we reach SSA, that structure is flattened. Aggregates are
decomposed into parallel `Value`s. Folds are loops with block params.
The map-of-map is two loop-with-buffer patterns separated by an
allocation. Recovering the algebra at the SSA layer is the SCEV
problem in miniature — a substantial engineering investment to
reconstruct what was thrown away.

Core sits between AST and SSA. The algebraic structure is still
visible. Rewrites operate on it directly.

## Architecture

Three rewriting paradigms, each at the level where its information
is visible:

| Layer          | Job                  | Style                       | Examples                                                |
| -------------- | -------------------- | --------------------------- | ------------------------------------------------------- |
| `passes/core/` | Algebraic rewriting  | Pattern rewriting on Core   | fusion, beta, eta, case-of-case, banana, free theorems  |
| `src/opt/`     | Scalar dataflow      | Local SSA peephole          | const-fold, branch-fold, DCE, GVN, rc-fusion, LICM      |
| `src/lower/`   | Resource discipline  | Declarative emission        | FBIP via cow_*, RC traffic, aggregate decomposition     |

The bottom layer is *not* a rewrite layer — it's where the source's
semantics get expressed as IR. The middle layer is local dataflow
rewriting where the SSA shape is natural. The top layer is
algebraic rewriting where the term structure is natural.

**Rule of thumb:** if a rewrite's natural form is `Map`, `Cata`,
`Con` — i.e. the algebra of the source — it goes in `passes/core/`.
If its natural form is "find a chain of `Binary` instructions and
constant-fold" — i.e. SSA shape — it goes in `src/opt/`. Putting
either at the wrong layer forces the SCEV pattern: reconstructing
structure the layer above threw away.

## The IR

Eleven `Expr` variants. The design rule: a primitive earns its keep
when either (a) it's load-bearing for a memory invariant the rest of
the IR can't express, or (b) it can't be source-defined without
circularity. Everything else is `App` to a builtin or stdlib
function.

```rust
enum Expr {
    // Universal — present in any sane IR
    Var    { sym: SymbolId, ty: Type },
    Lit    { value: Literal, ty: Type },
    App    { target: SymbolId, args: Vec<Expr>, ty: Type },
    Let    { binders: Vec<SymbolId>, value, body, ty },

    // Algebraic structure — rewrites pattern-match on these
    Match  { scrutinee_slots, scrutinee_ty, arms, ty },
    Cata   { fold_fn, target_slots, target_ty, init, captures,
             elem_ty, early_exit, ty },
    Con    { tag, args, field_slot_counts, ty },

    // Buffer trio (List = Str = (len, cap, data))
    BufLit    { elements, elem_ty, ty },
    BufLoad   { buf, idx, ty },
    BufAppend { buf_slots, val_slots, elem_ty, ty },
    BufSet    { buf_slots, idx, val_slots, elem_ty, ty },
}

enum Pattern { Constructor { tag, binders }, Wildcard, Binding(sym) }
enum Literal { Int(i64), Float(f64) }
```

### Why each variant earns its keep

| Variant     | Justification |
|-------------|---------------|
| `Var`       | Trivial — reference a binding. |
| `Lit`       | Scalar literals (Int, Float). `Str` literals desugar to `BufLit` of byte Lits at AST→Core; `Str = List(U8)`, no separate string. |
| `App`       | First-order call. After lambda-lift + mono, every call has a known top-level target. `target: SymbolId`; the name is recovered via `symbols.display()` at Core→SSA. |
| `Let`       | Binding. Preserves binding structure for let-floating, CSE, dead-binding elimination. |
| `Match`     | Non-recursive case analysis on tag unions. Distinct from `Cata` because not every case-of is a fold (`Maybe`, `Result`, single-variant unions are non-recursive). |
| `Cata`      | The **only iteration primitive**. Source-defining a fold would be circular (you'd need a fold to define fold). After `fold_lift` runs, every source `fold` becomes a call to a `__fold_N` helper; AST→Core promotes those calls into `Cata` so algebraic rewrites can see them. `early_exit: bool` distinguishes the `walk_until` shape. |
| `Con`       | Tag-union constructor. Explicit, not folded into `App`. Critical for `case-of-known-constructor`: `Match(Con(tag, args), arms) → arms[tag][args]` is a syntactic rewrite. |
| `BufLit`    | `[1, 2, 3]` and `"abc"` — buffer literals. Could desugar to chained `BufAppend` but every literal would then alloc-thrash. Zero-cost literal is load-bearing. |
| `BufLoad`   | `xs.get(idx)` — bounds-checked index returning `Result(T, OutOfBounds)`. Could be a stdlib method; primitive avoids the call. |
| `BufAppend` | `xs.append(y)` — produces new trio via `cow_resize_dyn` (in-place when rc=1, clone when rc>1). **Source can't express in-place mutation**, so this primitive is load-bearing for FBIP. |
| `BufSet`    | `xs.set(i, y)` — same FBIP justification via `cow_store_dyn`. |

### What's *not* a primitive (anymore)

Things that look primitive but lower as `App` to a bodyless builtin
SymbolId (dispatched at to_ssa via `BuiltinRegistry::classify`):

- **Arithmetic / comparison / bitwise** (`Add`, `Sub`, `Mul`, ..., `Eq`, `Lt`, ..., `And`, `Or`, `Xor`, `Shl`, `Shr`, `Max`). To_ssa emits `Inst::BinOp(op, lhs, rhs, ty)`. `Eq` / `Neq` on buffer trios delegates to `buf_eq` (length check + elementwise loop).
- **Numeric conversion** (`cast`, `bitcast`). Destination scalar type is read off the App's result `ty`.
- **`List.range(start, end)`** — anamorphism (unfold). To_ssa emits the counter-driven fill loop returning the trio.

The unification rule: **a builtin App is a "function the CPU handles
directly" — no SSA function body, no `Inst::Call`, just inline
emission.** Regular App targets resolve to functions with bodies and
emit `Inst::Call`.

### How aggregates flow without IR nodes for them

Records and tuples are **not** Core variants. They live at the AST
(source structure) and at SSA (decomposed parallel `Value`s + memory
layout) — never at Core. The IR is SROA-ed.

- `lower_expr_slots(ctx, ast) -> Vec<Expr>` — one Core Expr per slot
  of the AST expression's type. Slot count is
  `expand_slots(ast.ty)`, deterministic from type.
- Scalars: 1-element Vec. Records/tuples: N-element Vec.
- `ExprKind::Tuple` / `ExprKind::Record`: concatenate child slot
  lists.
- `ExprKind::FieldAccess`: take the record's slot list, pick the
  slice at the field's offset.
- `Pattern::Record` / `Pattern::Tuple`: flatten_patterns runs before
  Core and rewrites these into per-slot bindings.

Records and tuples don't participate in algebraic rewriting — fusion
laws operate on `Cata`, `Match`, `Con`. Keeping them as Core nodes
would make every rewrite walk past inert plumbing. SROA-ing them
out matches Core's purpose exactly: every primitive has an
algebraic role, nothing inert.

This is sound **only because** Ori has no aggregate identity. In
any language with pointer-takes or by-reference equality on
records, this SROA would be unsound. See `notes/language-properties.md`.

### Aggregate-producing control flow

When an `If` or `Match` returns a multi-slot type, the construct is
duplicated per slot. `if c then {a:1, b:2} else {a:3, b:4}` lowers
to two parallel `Match` expressions:

- slot 0 (`a`): `Match(c, True → 1, False → 3)`
- slot 1 (`b`): `Match(c, True → 2, False → 4)`

The condition `c` is duplicated. **Pure + total → semantically
free.** The runtime cost (re-evaluating `c`) is a future CSE/GVN
target at the Core opt layer.

`Match.scrutinee_slots: Vec<Expr>` and `MatchArm.body: Vec<Expr>`
carry the parallel slot lists. At to_ssa each Vec lowers to N
parallel SSA `Value`s; the merge block has N block params.

### Buffer trio

`List(T)` and `Str` (alias for `List(U8)`) decompose to a 3-slot
trio at every layer:

```
(len: U64, cap: U64, data: RcPtr)
```

Functions take and return the trio (`call_multi`). Pattern binders
bind three SSA values. Payload `Con`s store the trio inline (one
RcPtr slot per source field; the field's wrapper holds the trio
contents). The only place the trio collapses to a single header
pointer is the `__main` ABI boundary, where it's an explicit
materialization.

Element layout in the data buffer: each source-level element
occupies `slot_count * 8` bytes. A `List(I64)` strides 8 bytes;
`List({a: I64, b: I64})` strides 16. `BufLoad` / `BufAppend` /
`BufSet` know the stride from `elem_ty`.

`cap` is intentionally ignored by structural equality (`buf_eq`):
`[1, 2, 3]` and a longer-capacity buffer holding `[1, 2, 3]` are
equal. `cap` is an allocation detail, not part of the value.

## AST → Core (what gets desugared)

Lower-time rewrites that happen so Core stays small:

| Source shape                          | Becomes                                          |
|---------------------------------------|--------------------------------------------------|
| `a + b`, `a == b`, …                  | `App(builtins.add, [a, b])` etc.                 |
| `x.to_u8()`, `x.to_bits()`            | `App(builtins.cast, [x])` / `bitcast`            |
| `List.range(s, e)`                    | `App(builtins.range, [s, e])`                    |
| `"abc"` (`StrLit`)                    | `BufLit { elem_ty: U8, elements: [97, 98, 99] }` |
| `: 5 then body` (`Pattern::IntLit`)   | `: v and v == 5 then body`                       |
| `: "foo" then body` (`Pattern::StrLit`)| `: v and v == "foo" then body`                  |
| `f(...)` to `__fold_N`                | `Cata { fold_fn, … }`                            |
| `crash(msg)`                          | `App(__crash, [msg])`                            |

Records and tuples flatten via `lower_expr_slots`; nested patterns
flatten via `flatten_patterns` (runs before infer).

## Core → SSA

`to_ssa` lowers each Core variant to SSA instructions. The
interesting bits:

- **App dispatch.** `Expr::App { target }` first asks
  `ctx.builtins.classify(target)`. If it's a builtin (Binary, Cast,
  Bitcast, Range), emit inline (`Inst::BinOp`, `Inst::Cast`, …) via
  `emit_builtin_single_slot` / `emit_builtin_range`. Otherwise
  resolve the target's display name and emit `Inst::Call`.
- **`buf_eq`.** Binary `Eq` / `Neq` on 3-slot operands (List, Str)
  doesn't go through `Inst::BinOp(Eq, ...)` — that's scalar only.
  Instead `buf_eq` emits length check + elementwise loop, returning
  a Bool. `cap` is ignored.
- **Cata dispatch.** `Expr::Cata` checks if the target is a `List`;
  if so, `lower_list_cata` emits a counter-driven loop (with
  optional `early_exit` Continue/Break dispatch for `walk_until`).
  Otherwise it emits `Inst::Call` to the `__fold_N` helper which
  contains the structural recursion.
- **Con boundary.** For multi-variant payload unions (Result, Maybe,
  user unions), the per-source-field grouping is encoded in the
  Con's `field_slot_counts`. To_ssa regroups the flat args back into
  field-shaped wrappers via `group_args_by_field`. See "Reverts"
  below for why this isn't derivable.
- **Match dispatch.** All-Constructor multi-arm: `SwitchInt` on the
  scrutinee's tag. All-Binding (from literal-pattern desugar):
  `SwitchInt` on a const-0 with all arms sharing tag 0, so they
  chain via `next_same_tag` guard fall-through — effectively a
  guard chain.

## What we explicitly reject

- **CCC-style combinators (`id, ∘, fst, snd, ...`).** Beautiful for
  fusion but far from source; debugging output incomprehensible.
- **ANF as Core form.** Cleaner for dataflow but buries the algebra
  under naming. Better: ANF-transform *before* lower-to-SSA as a
  separate pass; keep Core direct-style.
- **CPS.** Wrong shape for algebraic rewriting; right shape for
  compilation. Same answer: not as Core.
- **Sea-of-nodes.** Wrong layer; V8 is moving away from it anyway.
- **de Bruijn indices for binders.** Tempting (alpha-equivalence is
  free, useful if we ever adopt e-graphs). But less readable, harder
  to debug. Defer; can add a canonicalize pass later.
- **`BinOp` / `Cast` / `Range` as dedicated variants.** They
  were primitives in the original design; we collapsed them to
  builtin `App` because the algebraic rewrite system never matched
  on them. The dispatch table is the seam between "function with a
  body" and "function the CPU handles directly."
- **`Record` / `Tuple` as Core variants.** SROA-ed at AST→Core.
  Sound only because Ori has no aggregate identity (see above).

## What we defer

- **e-graphs / equality saturation.** Our laws are mostly monotonic
  (fusion strictly improves cost), so fixpoint application of
  hand-rolled rules produces the same result as cost-based extraction.
  Signal to adopt: phase-ordering pain in practice (e.g. we end up
  with a Core-level `run_full_pipeline` calling `apply_rules` four
  times). Until then, hand-rolled is faster per-rule and easier to
  debug.
- **Effects / I/O.** We're pure today. If/when we add I/O, an
  effect annotation on `App` (or separate `EffApp`) is the likely
  shape. The pure subset stays as-is.
- **Higher-rank polymorphism past mono.** Would need type
  abstractions in Core. We mono first, so this is moot for now.

## The empirical gate

The original plan: gate fusion-rule investment on a real benchmark
showing a meaningful win. The first deliverable was supposed to be
one end-to-end fusion case (`Cata(f, z, Map(g, xs)) → Cata(λ. f acc
(g x), z, xs)`) with a measured allocation + runtime delta.

**Status: the gate has not fired.** Today's `rules.rs` has
add-zero / mul-one identity rules and a dead-let-eliminator. No
actual fusion rule has been written. All the infrastructure (Core
IR, AST→Core, Core→SSA, BuiltinRegistry, App dispatch, simplify
plumbing) is in place; the gate is the next missing piece.

If the gap on real Ori programs turns out to be small (≤2× on
`xs.map(f).walk(g)`), the question becomes whether the Core IR
infrastructure earns its keep at all. FBIP plus AST-level
`range.walk` recognition might capture most of the win on its own.

## Reverts and corrections from prior work

Mistakes from the journey, recorded so the next attempt at each
reads the lesson first.

- **`stream_fuse` and `loops.rs` SCEV-style reconstruction**
  (`21c4335`, `8ed81c8`) — reverted. We tried recovering algebraic
  structure at the SSA layer. The IR layer was the right home;
  Core exists because of this lesson.
- **`Con.field_slot_counts` derivation at to_ssa** (`b2cc924`) —
  attempted, reverted. The natural derivation walks the
  constructor's scheme substituted against `Con.ty`. But `Con.ty`
  is stamped from `constructor_return_types` which holds the
  *polymorphic* scheme return (`Result(Var, Var)`) so that closure
  constructors get a meaningful union-shaped type — substituting
  against polymorphic ty is identity, every field collapses to 1
  default slot. The monomorphic info derivation needs is in the
  AST args' types at the call site, which Core doesn't carry. The
  field stays. If you want to retry this, fix `Con.ty` to always
  carry the monomorphic instantiation first (distinguish closure
  constructors from declared at lower time).
- **`Pattern::IntLit` / `Pattern::StrLit` decomposition** — landed.
  Both desugared to `Binding(fresh) + Eq guard` at AST→Core.
  Tradeoff: lost the `SwitchInt` jump-table for dense int matches
  (the `Binding`-arms chain is a sequential guard test). Recoverable
  as an SSA-opt pass that rebuilds `SwitchInt` from chained
  `Binding + Eq(x, lit)` arms; not yet written.

## Open questions

- **Stdlib marking story.** For fusion to fire, stdlib `List.map`,
  `List.filter`, `List.walk` need to be recognizable as `Cata` /
  `Map` / `Build` at Core. Options: (a) annotate in source
  (`@cata`, `@build`); (b) recognize by name in the lowerer;
  (c) write these stdlib functions in Core directly. Probably (c) —
  stdlib is the bridge between user surface syntax and Core
  primitives.
- **Fix `Con.ty` to be monomorphic.** Today the polymorphic-ty
  workaround for closure constructors infects everything. The
  fix is to distinguish closure tags from declared tags at lower
  time and stamp `ast.ty` (monomorphic) for the latter,
  `constructor_return_types` (synth TagUnion) only for the former.
  Standalone win — makes one of the IR's invariants honest —
  and unblocks the `field_slot_counts` derivation as a follow-up.
- **Switch-table recovery at SSA-opt.** Today's IntLit-pattern
  decomposition trades the dense-int-match jump table for a guard
  chain. An SSA pass that recognizes `Binding + Eq(scrutinee, lit)`
  chains and rebuilds `SwitchInt` recovers the perf without
  re-introducing `Pattern::IntLit`.
- **`loops.rs`.** Currently unused. LICM is the obvious consumer
  once we have it; codegen could use it for hot-loop heuristics.
  Worth keeping but not maintained beyond what consumers demand.
- **ANF before SSA?** Probably yes — ANF naturalizes the SSA
  lowering (each subexpression names its intermediate). This would
  be a Core→ANF→SSA chain, not changing what Core is.

## Success criteria

Original: get to a Core with 3-5 fusion rules and demonstrate on a
benchmark that `xs.map(f).walk(g)` compiles to a single zero-alloc
loop (within a small constant factor of hand-written C).

**Where we are:** the IR exists, the rewriting infrastructure is
plumbed, but no fusion rule has been written. The next milestone
is firing the empirical gate — pick one fusion case, write the
rule, measure. The answer determines whether more rewrites are
worth the investment.
