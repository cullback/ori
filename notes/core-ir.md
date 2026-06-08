# Core IR

The Core IR sits between Ori's AST and its SSA. It exists because
the algebraic structure of an Ori program — `Map(f, Map(g, xs))`,
`Cata(f, z, Build(p))`, `Match(Con(tag, args), arms)` — is the
natural domain for the rewrites Ori's language properties make
unconditional, and that structure must be preserved past inference
and monomorphization for those rewrites to apply.

## Motivation

Algebraic rewrites — fusion, case-of-case, case-of-known-constructor,
free theorems, hylomorphism deforestation, whole-program
specialization, compile-time evaluation of arbitrary closed terms —
are **unconditional** in Ori. No side conditions, no ⊥-safety
arguments, no fixpoint over the call graph. Each is hundreds-to-
thousands of lines in LLVM or GHC; they exist there because the
source language doesn't provide the guarantees that make them safe.
Ori's does.

These rewrites operate on the **algebraic structure** of the
program — `Map`, `Cata`, `Con`, `Match`. By the time the program
reaches SSA, that structure is gone: aggregates decomposed into
parallel `Value`s, folds are loops with block params, map-over-map
is two loop-with-buffer patterns separated by an allocation.
Recovering the algebra at SSA is the SCEV pattern in miniature —
substantial engineering to reconstruct what the front-end already
knew. **Core exists to preserve the algebra past inference and mono
so the rewrites can run on the natural shape.**

Each section below names a guarantee Ori enforces and the
optimizations that fall out of it.

### Totality

Structural recursion only; every closed term reduces in bounded
time.

- Every equational rewrite preserves totality unconditionally.
- Compile-time evaluation works on any closed term, including
  user-defined recursive functions. The compiler can pre-execute a
  call like `factorial 10` and emit `3628800` directly — no
  termination analysis required, because the language guarantees
  termination.
- Hylomorphism deforestation works fully: `cata f ∘ ana g = hylo f g`
  eliminates the intermediate inductive type entirely.
- Free theorems via parametricity hold without side conditions
  (`length . map f = length`, `map id = id`).

### Structural recursion (no general recursion)

Loops are folds over inductive types — the data's shape is the
loop bound.

- Trip counts are syntactic; no SCEV needed.
- Fold fusion laws are universal, not heuristic.
- TCO isn't a separate analysis — folds *are* loops.
- Static unrolling over known-shape data: `Fold f z [a,b,c]`
  becomes `f(f(f(z, a), b), c)`, no loop emitted.

### Purity

No source-level mutation, no effects in the pure fragment.

- Memoization sound (compile-time and runtime).
- Speculative evaluation sound; reordering free.
- Dead-binding elimination needs no effect analysis.
- CSE needs no alias analysis.

### Strictness

Left-to-right, no laziness. Underwrites the deterministic
evaluation order the other guarantees assume; no distinct algebraic
payoff of its own.

### Lambda-lifted, first-order calls

Every `App` resolves to a known top-level target.

- All call edges statically known. No virtual calls;
  devirtualization is free.
- Inlining is purely syntactic substitution.

### DAG call graph

No mutual recursion across user functions.

- Single-pass bottom-up optimization. Topo-sort callees first; by
  the time `f` is processed, every callee is at its optimized
  form. No fixpoint iteration over the graph.
- Bounded inlining (in topological order).
- Bounded whole-program specialization (`callsites × shapes`
  variants per function).
- Whole-program escape analysis as a finite DAG walk.
- Cross-function CSE: inline, then dedupe.

### No aggregate identity

No pointer-take on records, no by-reference equality, no FFI
opacity, no varargs.

- Records and tuples SROA-able at the IR level (no observable
  difference between `r.x` and a let-bound slot).
- Aggregate-returning `If` / `Match` can be duplicated per slot
  (re-evaluating the condition is equivalent under purity).

## Architecture

Three rewriting paradigms, each at the level where its information
is visible:

| Layer          | Job                  | Style                       | Examples                                                |
| -------------- | -------------------- | --------------------------- | ------------------------------------------------------- |
| `passes/core/` | Algebraic rewriting  | Pattern rewriting on terms  | fusion, beta, eta, case-of-case, banana, free theorems  |
| `src/opt/`     | Scalar dataflow      | Local SSA peephole          | const-fold, branch-fold, DCE, GVN, rc-fusion, LICM      |
| `src/lower/`   | Resource discipline  | Declarative emission        | FBIP via cow_*, RC traffic, aggregate decomposition     |

The bottom layer is not a rewrite layer — it's where the source's
semantics get expressed as IR. The middle layer is local dataflow
rewriting where the SSA shape is natural. The top layer is algebraic
rewriting where the term structure is natural.

**The placement rule:** if a rewrite's natural form is `Map`,
`Cata`, `Con` — i.e. the algebra of the source — it belongs in
`passes/core/`. If its natural form is "find a chain of `Binary`
instructions and constant-fold" — i.e. SSA shape — it belongs in
`src/opt/`. Putting either at the wrong layer forces the SCEV
pattern: reconstructing structure the layer above threw away.

## The IR

```rust
enum Expr {
    Var    { sym: SymbolId, ty: Type },
    Lit    { value: Literal, ty: Type },
    App    { target: SymbolId, args: Vec<Expr>, ty: Type },
    Let    { binders: Vec<SymbolId>, value: Box<Expr>, body: Box<Expr>, ty: Type },

    Match  { scrutinee_slots: Vec<Expr>, scrutinee_ty: Type,
             arms: Vec<MatchArm>, ty: Type },
    Cata   { fold_fn: SymbolId, target_slots: Vec<Expr>, target_ty: Type,
             init: Vec<Expr>, captures: Vec<Expr>,
             elem_ty: Type, early_exit: bool, ty: Type },
    Con    { tag: TagId, args: Vec<Expr>,
             field_slot_counts: Vec<usize>, ty: Type },

    BufLit    { elements: Vec<Expr>, elem_ty: Type, ty: Type },
    BufLoad   { buf: Box<Expr>, idx: Box<Expr>, ty: Type },
    BufAppend { buf_slots: Vec<Expr>, val_slots: Vec<Expr>,
                elem_ty: Type, ty: Type },
    BufSet    { buf_slots: Vec<Expr>, idx: Box<Expr>,
                val_slots: Vec<Expr>, elem_ty: Type, ty: Type },
}

enum Pattern { Constructor { tag: TagId, binders: Vec<Vec<SymbolId>> },
               Wildcard,
               Binding(SymbolId) }

enum Literal { Int(i64), Float(f64) }
```

Direct-style (not ANF), typed at every node (`ty: Type` on every
variant), post-monomorphization.

### Types in Core

Every Core node carries `ty: Type`, the source-level type from
inference. The `Type` enum (defined in `types/engine.rs`):

- `Type::Con(name)` — primitive scalar (`I64`, `U8`, `Bool`, `F64`)
  or a named user type (`MyUnion`, `Box`).
- `Type::App(name, args)` — applied type constructor: `Result(I64,
  Str)`, `List(I64)`, `Maybe(T)`.
- `Type::Arrow(params, ret, lambda_set?)` — function type, with an
  optional lambda set (the closures that flow through this Arrow
  after row-polymorphic inference).
- `Type::Tuple(elems)` — anonymous product. Decomposed at AST → Core.
- `Type::Record { fields }` — named-field product. Decomposed at
  AST → Core.
- `Type::TagUnion { tags, rest }` — discriminated union.
- `Type::Var(tv)` — type variable. Should not appear in Core
  post-mono, **with one exception** (the polymorphic-`Con.ty`
  workaround below).

Transparent newtypes (`Str := List(U8)`) are registered in a side
table; `resolve_transparent` unwraps them at use sites. Opaque
newtypes (`Foo :: Bar`) aren't transparent — the underlying type is
hidden outside the methods block.

**The polymorphic-`Con.ty` footgun.** For declared constructors
(`Ok`, `Err`, user union tags), AST → Core stamps `Con.ty` from
`constructor_return_types`, which holds the *scheme's* return type
(`Result(Var(a), Var(e))`), not the monomorphic instantiation
(`Result(I64, Str)`). Why: closure constructors like `__lambda_K`
need a union-shaped type at the construction site, but the
surrounding AST's `ty` is just the closure's return type (`I64`).
`constructor_return_types` provides a union shape for both
declared and closure cases, at the cost of being polymorphic for
declared. Analyses that substitute against `Con.ty` get identity
subst and silently produce wrong results — the monomorphic info
lives in the AST args' types at the call site, which is why
`Con.field_slot_counts` is stored as derived data on the variant.
The real fix is distinguishing closure tags from declared tags at
lower time so declared `Con`s can stamp the monomorphic `ast.ty`;
not yet done.

### Evaluation order

Strict, left-to-right at the language level. At Core:

- **`App(f, [a, b, c])`** — args left to right, then the call.
  Same for builtin Apps.
- **`Let(binders, value, body)`** — `value` before `body`; binders
  come into scope for `body` only.
- **`Match(scrutinee_slots, arms)`** — scrutinee slots left to
  right; pattern dispatch picks an arm; guards left to right; arm
  body.
- **`Cata`** — target slots, then init, then captures, then the
  loop.
- **`Con(tag, args)`** — args left to right, then construction.
- **`BufLit { elements }`** — elements left to right, then the
  alloc + stores.

Purity makes evaluation order unobservable for most rewrites
(reordering pure expressions is sound). Order matters for `crash`
(the divergence happens at its source-level position) and for the
runtime sequencing of RC `inc` / `dec` operations.

### Earn-its-keep rule

A primitive earns its keep when at least one of:

1. **It can't be source-defined** without circularity. A `fold`
   defined as a `fold` would be circular; iteration must be primitive.
2. **It's load-bearing for a memory invariant** the rest of the IR
   can't express. In-place mutation (`xs.append(y)` reusing the
   buffer when `rc == 1`) is impossible to express in pure source;
   it must be a primitive.
3. **An algebraic rewrite matches on its shape.** Case-of-known-
   constructor needs `Con` to be a distinct shape from `App`.

Everything else — including arithmetic, casts, list ranges, scalar
comparisons — is `Expr::App` to a target that the lowering layer
recognizes as a builtin and emits inline. The mental model: **a
primitive is a function the CPU handles directly, with no body in
the module**. Regular `App` is a function the user (or stdlib)
defined.

### Per-variant rationale

| Variant     | Justification                                                                                                                                                                                                                                                                          |
| ----------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Var`       | Trivial — reference a binding.                                                                                                                                                                                                                                                         |
| `Lit`       | Scalar literal (Int, Float). String literals are not a Core node — they desugar to `BufLit { elem_ty: U8, elements: [byte Lits] }`. `Str ≡ List(U8)`; there's no separate string type.                                                                                                  |
| `App`       | First-order call. After lambda-lift + mono, every call has a known top-level target. `target` is a `SymbolId`; the mangled name is recovered via the symbol table at Core → SSA. **Bodyless builtin targets (arithmetic, cast, range) dispatch inline at the lowering layer.**         |
| `Let`       | Binding. Preserves binding structure for let-floating, CSE, dead-binding elimination. Multi-slot bindings carry N binders.                                                                                                                                                              |
| `Match`     | Non-recursive case analysis on a tag union. Distinct from `Cata` because not every case-of is a fold (`Maybe`, `Result`, single-variant unions are non-recursive). Critical for case-of-case and case-of-known-constructor: both are syntactic rewrites only if `Match` is a variant.   |
| `Cata`      | The **only iteration primitive**. Source-defining a fold would be circular. After fold-lifting, every source `fold` becomes a call to a `__fold_N` helper; AST → Core promotes those calls into `Cata` so the rewrite system can see them. `early_exit` distinguishes the `walk_until` shape. |
| `Con`       | Tag-union constructor. Explicit, not folded into `App`. Critical for case-of-known-constructor: `Match(Con(tag, args), arms) → arms[tag][args]` is a syntactic rewrite. **Footgun**: `Con.ty` for declared constructors carries the *polymorphic* scheme return type (`Result(Var, Var)`), not the monomorphic instantiation — see "Types in Core" below. |
| `BufLit`    | Buffer literal (`[1,2,3]`, `"abc"`). Could desugar to chained `BufAppend` from `[]`, but every literal would alloc-thrash. Zero-cost literal is load-bearing.                                                                                                                            |
| `BufLoad`   | Bounds-checked index, returning `Result(T, OutOfBounds)`. Could be a stdlib method; primitive avoids the call and lets the bounds check participate in algebraic simplification.                                                                                                       |
| `BufAppend` | Produces a new buffer trio. **Load-bearing for FBIP**: lowers to `cow_resize_dyn` — mutate in place when `rc == 1`, clone when `rc > 1`. Source can't express in-place mutation, so the primitive carries the invariant.                                                                |
| `BufSet`    | Same FBIP rationale, via `cow_store_dyn`. `[1,2,3].set(1, 99)` runs in place when the list isn't shared.                                                                                                                                                                                |

### `Cata` in detail

Cata is the only iteration primitive and the central rewrite target.
Each field plays a specific role:

| Field           | Meaning |
| --------------- | ------- |
| `fold_fn`       | SymbolId of the lifted recursive helper (`__fold_N`, or a stdlib fold). Holds the actual recursion. |
| `target_slots`  | The inductive value being consumed, as a parallel slot list. For `List`, the 3-slot trio. For `Lnk` / `Tree` / multi-variant unions, `(tag, payload)`. |
| `target_ty`     | Source-level type of the target, preserved separately because `target_slots[i].ty()` carries per-slot scalar placeholders that lose the inductive shape. |
| `init`          | Seed accumulator values for walk-style folds. Empty Vec for pure catamorphisms. |
| `captures`      | Free variables of the fold closure, threaded as parallel block params through the loop. |
| `elem_ty`       | For List-shaped Catas: the element type. Used by the data-buffer stride calculation. |
| `early_exit`    | When `true`, `fold_fn` returns `Step(b) = Continue(b) \| Break(b)`. Lowering emits Continue/Break dispatch. The `walk_until` shape. |
| `ty`            | Result type of the whole expression. |

**What rewrites can match syntactically:**

- Cata over `Range`: fuse into a counter loop without building the
  intermediate list.
- Cata over Cata (banana): nested folds over the same target,
  combine into one.
- Cata over a `Build`-form (deforestation): eliminate the
  intermediate inductive entirely (`cata f ∘ ana g = hylo f g`).
- Cata over a known-constructor scrutinee: unfold the recursion's
  first step at compile time.

**What rewrites can't easily match:** when `fold_fn` is a
user-defined `__fold_N`, the algebraic shape of *what the fold
computes* is hidden inside the helper body. Fusion that requires
seeing into the fold needs either:

- Core-level inlining of `__fold_N` (the helper body is available
  in the module), or
- A stdlib-recognition convention that names known fold shapes
  (`__List_map`, `__List_filter`, `__List_walk`) so the rewrite
  can pattern-match by name without inlining.

This is the **stdlib marking** question: for `xs.map(f).walk(g)` to
fuse, `map`'s underlying helper has to be recognized as `Map(f)`
rather than just "a fold." Three real options exist:

- **Source annotations** (`@map`, `@build`, `@cata`) — explicit
  intent at the stdlib declaration.
- **Name-based recognition** at AST → Core — match on `__List_map`
  by string convention.
- **Write stdlib fold-shaped functions directly in Core** — the
  stdlib bridges between user surface syntax and Core primitives.

Not yet decided; needed before the first real fusion rule lands.

### What is deliberately not a primitive

The following all look primitive at the surface but aren't Core
variants — they lower as `App` to a builtin `SymbolId` that the
lowering layer dispatches inline:

- **Arithmetic, comparison, bitwise, shifts** (`Add`, `Sub`, `Mul`,
  `Div`, `Rem`, `Eq`, `Neq`, `Lt`, `Gt`, `Le`, `Ge`, `And`, `Or`,
  `Xor`, `Shl`, `Shr`, `Max`). To_ssa emits `Inst::BinOp(op, lhs, rhs)`.
  `Eq` / `Neq` on buffer trios delegates to an inline length-check +
  elementwise loop.
- **Numeric conversion** (`cast`, `bitcast`). Destination scalar type
  is read off the `App.ty` at lowering time.
- **`List.range(start, end)`** — anamorphism. To_ssa emits a counter-
  driven fill loop returning the trio.

These could be Core variants — earlier iterations had them as
`Expr::BinOp`, `Expr::Cast`, `Expr::Range`. They aren't, because:

1. The algebraic rewrite system never matched on them. Fusion and
   case-of-case don't recognize `1 + 2` as a fusion site.
2. With dispatch driven by a `SymbolId`, user-defined types can
   override `+` by defining their own `add` method — the same path
   handles built-in scalar `add` (no function body) and user
   `Vec3.add` (a real function call). One mental model.
3. The IR stays smaller. Each additional variant is another arm
   every walker, every rewrite rule, and every type-equality check
   has to handle.

### Records, tuples, strings — not Core variants

Records and tuples are SROA-ed at AST → Core: the AST node becomes
parallel slot lists, not a Core node. A `Record { x: 1, y: 2 }`
typed `{ x: I64, y: I64 }` becomes two Core `Expr`s — one per slot.
A `Tuple(a, b, c)` concatenates the three children's slot lists.
`FieldAccess(record, field)` slices the record's slot list at the
field's offset. Pattern-matching on records is flattened before
Core into per-slot bindings.

This works for the same reason aggregate-returning `If` can be
duplicated per slot: **Ori has no aggregate identity**. There's no
observable difference between a record value and the parallel
sequence of its fields. In any language with pointer-takes,
by-reference equality, or FFI varargs, this SROA would be unsound.

Strings are not a Core variant either. `Str` is a transparent
alias for `List(U8)` at the type system; at Core, a string literal
desugars to a `BufLit` of byte-typed Int constants. `'a' + 'b' +
"hello"` is just buffer operations on `List(U8)`.

Eliminating these from Core matches the layer's purpose: every
variant has an algebraic role, nothing inert. Walkers and rewrites
don't waste cycles stepping past plumbing.

### Multi-slot bindings

`Var` and `Let` are slot-aware. When a binding's value is
multi-slot (a record, tuple, List trio, or multi-variant payload):

- **`Let { binders: Vec<SymbolId>, value, body }`** — the value
  produces N slots; `binders.len() == N`; each binder names one
  slot. The body references each binder as a single-slot `Var`.
- **`Var { sym, ty }`** — if `sym` is a multi-slot binding,
  `lower_expr_slots(Var)` looks `sym` up in `ctx.locals:
  HashMap<SymbolId, Vec<SymbolId>>` and expands to N parallel
  slot-Var references. The single-slot `lower(Var)` errors on
  multi-slot bindings — the caller must use `lower_expr_slots`.

Slot symbols are minted fresh by AST → Core when it encounters a
multi-slot binding site. The AST source name maps to the slot
symbol list via `ctx.locals`. Slot symbols carry source-derived
dotted paths (`r.x`, `r.b.c`, `t.0`) via `ctx.slot_paths` for debug
output.

**Invariant**: every `Var` reference at Core resolves to either
(a) a function parameter (1 SSA value), (b) a single-slot
let-binding (1 SSA value), or (c) a multi-slot let-binding (N SSA
values, where N is derivable from the binding's type). Walkers
matching on `Var` must know which case they're in.

### The buffer trio

`List(T)` and `Str = List(U8)` decompose to a 3-slot trio at every
layer where slots are visible:

```
(len: U64, cap: U64, data: RcPtr)
```

Functions take and return the trio (multi-result calls). Pattern
binders bind three SSA values. Payload `Con`s store the trio inline
(one wrapper-RcPtr slot per source field; the wrapper holds the
trio contents). The only place the trio collapses to a single
header pointer is the `__main` ABI boundary.

Element layout in the data buffer: each source-level element
occupies `slot_count(elem_ty) * 8` bytes. A `List(I64)` strides 8
bytes; `List({ a: I64, b: I64 })` strides 16. The `elem_ty` field
on `BufLit` / `BufAppend` / `BufSet` carries the stride info; the
SSA layer reads it.

**`cap` is intentionally not part of equality.** `[1, 2, 3]` and a
list with `cap = 16` holding `[1, 2, 3]` are equal values. `cap` is
an allocation detail, not part of the value. The structural
equality lowering (length-check + elementwise loop) ignores `cap`
by construction.

### Closures and higher-order functions

Ori has higher-order functions but no first-class closures *at Core*
— every closure becomes a tag-union value before Core sees it. The
front-end pipeline (`lambda_lift` → infer → `lambda::specialize` →
`lambda::narrow`) does the work:

1. **The lambda becomes a top-level function.** `lambda_lift`
   emits a `FuncDef` for `__lambda_K(captures..., args...)`. The
   lambda's free variables become leading capture parameters.

2. **The closure value is a `Con` over a synthesized tag union.**
   A new `__Closure_X` type is registered with one variant per
   closure that can flow through the relevant Arrow position. The
   value at the lambda site is `Con("__lambda_K_tag", [captures...])`.
   The closure's runtime representation is just the tag and its
   captures — same as any payload-carrying union.

3. **Calling a closure dispatches via `__apply_K`.** A call to a
   parameter `f: __Closure_X` lowers as `App(__apply_K, [f, args...])`.
   The synthesized `__apply_K` body is a `Match` on the closure tag
   forwarding to the right `__lambda_K`.

4. **Singleton lambda sets specialize to direct calls.** When
   inference proves only one closure can flow through a given Arrow
   position (the lambda set has exactly one element), `lambda::narrow`
   rewrites the call site as a direct `App(__lambda_K, [captures...,
   args...])` — no dispatch.

Consequences for Core:

- Higher-order functions look like any other tag-union consumer.
  `xs.map(f)` where `f` is a closure parameter compiles to a
  `Cata` whose `fold_fn` is `__apply_K` (or, in the singleton case,
  the `__lambda_K` directly) and whose `captures` include the
  closure value.
- The `Type::Arrow`'s `lambda_set` carries the set of closures that
  flow through that Arrow. Mono specializes on the lambda set,
  producing one variant per closure shape.
- Closures introduce no runtime indirection beyond a tag dispatch
  — the lambda set is closed at compile time.
- Pattern-matching rewrites on closure types work identically to
  any other multi-variant union; case-of-known-constructor on a
  fresh closure value collapses the dispatch.

### Aggregate-producing control flow

When `If` or `Match` returns a multi-slot value, the construct is
duplicated per slot. `if c then { a: 1, b: 2 } else { a: 3, b: 4 }`
becomes two parallel `Match` expressions:

- slot 0 (`a`): `Match(c, True → 1, False → 3)`
- slot 1 (`b`): `Match(c, True → 2, False → 4)`

The condition `c` is duplicated. **Pure + total ⇒ semantically
free** — re-evaluating `c` is equivalent to evaluating it once.
The runtime cost of duplicated work is a future CSE / GVN target
at the SSA layer.

`Match.scrutinee_slots` and `MatchArm.body` are `Vec<Expr>` for the
parallel slot lists. At Core → SSA, each Vec lowers to N parallel
`Value`s; the Match's merge block has N block params.

### Patterns

Patterns are restricted to three shallow shapes:

- `Constructor { tag, binders }` — match a tag-union variant with
  per-field bindings. `binders` is `Vec<Vec<SymbolId>>`: the outer
  Vec is per source-level field, the inner Vec is the slot symbols
  that field expands to.
- `Wildcard` — match anything, bind nothing.
- `Binding(sym)` — match anything, bind to `sym`.

Nested constructor patterns are flattened by a pre-Core pass into
`Constructor` arms with extra `is` guards. Literal patterns
(`Pattern::IntLit`, `Pattern::StrLit` in the AST) are desugared at
AST → Core to `Binding(fresh_sym)` with a synthesized
`Eq(fresh_sym, lit)` guard prepended to the arm's guard list — so
Core never needs to special-case literal patterns. Three shapes
cover everything.

**Return arms.** `MatchArm` carries `is_return: bool`. When `true`,
the arm's body short-circuits the *enclosing function* instead of
merging into the match's result. The `?` operator desugars to a
match whose `Err` arm is a return arm; explicit `: pat return body`
syntax produces the same. Rewrites that flatten nested matches
(case-of-case and friends) must preserve the short-circuit semantics
— a return arm exits the outer function, which may not be the
immediately surrounding match expression.

### Crash and divergence

`crash(msg)` is the only way an Ori program can fail to produce a
value (totality rules out infinite loops). At Core it's `App(__crash,
[msg])` to a runtime function that prints `msg` and exits.

Implications for rewrites:

- **Reordering past `crash` is unsound.** The divergence happens
  at the source-level evaluation point. A rewrite that moves an
  expression across a `crash` changes whether the expression runs.
- **Duplicating `crash` is sound.** Both copies diverge.
- **Eliminating a `crash` dominated by another `crash` is sound.**
  The dominated one never runs.
- **`crash`'s result type is whatever the surrounding context
  expects** (it never returns). No rewrite should depend on the
  "value" of a `crash`.

Algebraic rewrites treat `crash` as an evaluation barrier — sound
rewrites preserve which crashes happen and in what order relative
to other observable events.

### AST → Core (semantic desugaring)

Source shapes that don't survive into Core:

| Source                                | Core                                                |
| ------------------------------------- | --------------------------------------------------- |
| `a + b`, `a == b`, …                  | `App(builtins.add, [a, b])` etc.                    |
| `x.to_u8()`, `x.to_bits()`            | `App(builtins.cast, [x])` / `App(builtins.bitcast,...)` |
| `List.range(s, e)`                    | `App(builtins.range, [s, e])`                       |
| `"abc"` (`ExprKind::StrLit`)          | `BufLit { elem_ty: U8, elements: [Lit 97, Lit 98, Lit 99] }` |
| `[1, 2, 3]` (`ExprKind::ListLit`)     | `BufLit { elem_ty: I64, elements: [...] }`          |
| `: 5 then body` (`Pattern::IntLit`)   | `: v and v == 5 then body`                          |
| `: "foo" then body` (`Pattern::StrLit`)| `: v and v == "foo" then body`                     |
| `f(...)` where `f` is `__fold_N`      | `Cata { fold_fn, ... }`                             |
| `crash(msg)`                          | `App(__crash, [msg])`                               |

Records and tuples flatten into parallel slot lists via
`lower_expr_slots`. Nested patterns flatten via a pre-Core pass.

### Core → SSA

`to_ssa` emits SSA for each Core variant. The notable shapes:

- **App dispatch.** Before emitting `Inst::Call`, the App handler
  asks the builtin registry whether `target` names a builtin. If
  so, the builtin's kind (`Binary(op)`, `Cast`, `Bitcast`, `Range`)
  drives inline emission — `Inst::BinOp(op, args[0], args[1])` for
  Binary, the counter loop for Range, etc. Otherwise, regular
  `Inst::Call`.

- **Buffer equality.** Binary `Eq` or `Neq` whose operands are
  3-slot trios (List, Str) doesn't go through scalar `Inst::BinOp(Eq)`.
  It lowers to a length check followed by an elementwise loop. The
  loop reads from each buffer at index `i`, compares, and short-
  circuits to `False` on mismatch.

- **Cata dispatch.** If the Cata's target is a `List`, lower to a
  counter-driven loop directly (with optional Continue/Break
  dispatch when `early_exit` is set for `walk_until`). Otherwise
  emit a recursive helper `Inst::Call` to the `__fold_N` function
  that carries the structural recursion.

- **Con boundary.** Multi-variant payload unions (Result, Maybe,
  user-defined) materialize the constructor by allocating a
  payload, storing one wrapper per source-level field at
  consecutive 8-byte offsets, and returning `(tag, payload)`.
  Single-variant payload unions (Phase E shape) skip the wrapping
  entirely and return the variant's slots directly.

- **Match dispatch.** All-Constructor arms emit a `SwitchInt` on
  the scrutinee's tag. All-Binding arms (from literal-pattern
  desugar) use a constant-zero synth tag with all arms sharing
  that tag, so they chain via guard fall-through — a sequential
  guard test, conceptually.

## Refcounting, ownership, and reuse

Ori's runtime model is Perceus-style refcounting plus FBIP: every
heap object carries an `rc`, reaching zero frees it and recursively
decrements its `RcPtr` children; mutating primitives (`BufAppend`,
`BufSet`) lower to `cow_*` runtime checks that mutate in place when
`rc == 1` and clone when `rc > 1`. The question this section answers
is: **what part of that runtime model lives at Core, and what part
lives at SSA?**

The split is between **operations** and **analyses**.

### Operations live at SSA

The instruction-level mechanics of refcounting — `rc_inc`, `rc_dec`,
`cow_resize_dyn`, `cow_store_dyn`, a hypothetical `reuse_alloc` —
are per-instruction events. Each one corresponds to a specific point
in execution. Their natural home is SSA, where dominance and def-use
chains let you place them precisely.

Putting raw RC ops at Core would be a category error. Every algebraic
rewrite — fusion, beta, case-of-case — would have to thread `dup` /
`drop` through to keep refcounts honest, multiplying the surface
area of every rule by a factor of "RC bookkeeping" with no
algebraic benefit. The Core IR has no `Expr::Dup(sym)` or
`Expr::Drop(sym)` variants for this reason.

What does live at SSA:

- `Inst::RcInc` / `Inst::RcDec` for explicit refcount adjustments.
- Auto-rc-on-Store / auto-rc-on-Load conventions on `RcPtr` values
  (every owning slot is a duplication point by construction; every
  load of an owning reference is too).
- `cow_resize_dyn` / `cow_store_dyn` runtime calls — the FBIP path
  for buffer mutation.
- Whatever explicit RC traffic balancing the above conventions
  requires.

A conservative SSA emission strategy (rc_inc on every consuming
use, rc_dec at every scope end) is sufficient for correctness on
its own — the analyses below sharpen it.

### Analyses live at Core

Refcount optimizations — eliding the counter when ownership is
provable, recognizing reuse opportunities, inferring borrows,
specializing drops by constructor shape — want to see the
**algebraic structure** of the program. That structure is gone at
SSA (a `Con` is `alloc + N stores`; a `Match` is `SwitchInt + N
loads`). It's present at Core.

Each analysis is a walk over the Core term that produces an
annotation; SSA emission consumes the annotation to make a precise
choice instead of the conservative default.

| Analysis              | What it proves                                                          | What SSA does with it                                  |
| --------------------- | ----------------------------------------------------------------------- | ------------------------------------------------------ |
| Uniqueness            | This `RcPtr` is never aliased — no store, no escape, no capture        | Skip the counter entirely; treat as a stack value     |
| Borrow inference      | This function arg is only inspected, never stored or returned          | Caller skips the inc before the call                  |
| Reuse fusion (FBIP)   | This `Match` arm drops a `Cons` box and constructs a same-shape `Cons` | Emit a reuse-alloc instead of free + alloc            |
| Drop specialization   | This `drop x` is over `x: Result(I64, Str)`                            | Inline the type-directed drop instead of a generic call |
| Reuse-across-scopes   | This `alloc` follows a drop of a same-sized box in the same scope      | Reuse the freed memory                                |

The DAG call graph + lambda-lifted calls + no aggregate identity
mean every one of these analyses is a finite bottom-up walk per
function. No fixpoint, no escape-hatch handling.

### The variant-vs-annotation line

Some ownership-related semantics earn a Core *variant*. Others stay
as out-of-band annotations.

A variant earns its keep when **lowering needs to distinguish a
shape**. Two cases qualify today:

- **`BufAppend` / `BufSet`** carry mutation intent at the variant
  level. The lowering doesn't ask "could this be in-place?" — the
  variant says "this is an FBIP mutation site." Without the
  distinct variant, lowering would have to recognize `BufLit`-into-
  store patterns and reverse-engineer the intent.
- **`Cata`** carries iteration semantics. Lowering specializes RC
  handling for the loop (decrement-once-at-loop-exit instead of
  per-iteration) because it knows the shape is a fold.

An out-of-band annotation suffices when the analysis result is just
"this site is special" — no new lowering shape needed, just a
modifier on existing lowering. Uniqueness, borrow flags, and reuse
pairings all fit this — they're side tables produced by Core
analyses, consumed by the SSA emitter.

**A future variant earns its keep** if user-defined inductive reuse
becomes a thing: a hypothetical `Reuse(scrutinee_box, tag, fields)`
that says "build this constructor by reusing the dropped scrutinee's
memory" would be a genuinely different lowering shape than `Con` —
the alloc instruction is different. The annotation alternative
(just mark the `Con` with a side-table flag) is possible but
clunkier; the lowering would have to consult the table per `Con`
to decide between fresh-alloc and reuse-alloc.

### What Core IR enforces vs preserves

A common worry: with primitives this simple, can we really enforce
all the RC invariants — no double-free, no use-after-free, in-place
when safe?

The framing that resolves it: **Core doesn't enforce these
invariants at the variant level. Core preserves the structure that
lets downstream analyses prove them.** Enforcement is a property of
the runtime model + the type system (Perceus precision, total
purity), not of the Core IR itself.

Compare to records and tuples: Core has no "this record doesn't
escape" variant; instead, the IR has clean tree structure that an
escape analysis can walk. Same idea for RC. Clean scopes, clean
type info, clean constructor/match shapes — these are what
linearity, borrow, and reuse analyses operate on. The primitives
don't need a substructural type system; the analyses do the work.

The IR's job is to **not introduce escape hatches** that would
hide ownership flow from those analyses. The current variant set
doesn't — every `RcPtr`-producing site is one of the listed
primitives, every consuming use is visible in the tree, every
scope is a `Let` or a `Match` arm.

### The path from "conservative RC" to "precise RC"

The progression isn't all-or-nothing. Each piece is an analysis +
an emission refinement:

1. **Baseline (today's conservative emit).** Every `RcPtr`-typed
   value gets `rc_inc` on consuming uses, `rc_dec` at scope ends.
   Buffer primitives use `cow_*`. Correct, but verbose.
2. **Uniqueness analysis.** Mark bindings that don't escape and
   aren't aliased. Emission elides their RC traffic. Pure win, no
   IR changes.
3. **Borrow inference at call boundaries.** Function args that the
   callee only inspects don't need a caller-side inc. Annotation
   on the call site; emission omits the inc.
4. **Reuse fusion for user inductives.** Recognize `Match(x,
   Cons(h, t) → ... Con("Cons", ...))` syntactically; emit reuse
   instead of free + alloc. May warrant a `Reuse` variant.
5. **Drop specialization.** Type-directed expansion of generic
   drops. Pure Core rewrite; no new variants.

Each step is independently shippable. None require the IR to
become more complex than it is — at most, one or two new variants
when lowering genuinely needs a new shape.

## Soundness

The algebraic rewrites that Core enables are sound only because of
the language guarantees listed at the top:

- **Reorderings** (CSE, code motion, let-floating) are sound because
  Ori is pure. No expression's evaluation has an effect we'd need
  to preserve.
- **Compile-time evaluation** of any closed term is sound because
  Ori is total. The evaluator terminates by construction.
- **Eliminations** (dead-let, unreachable arm, case-of-known-
  constructor) are sound because Ori is total — there's no ⊥ to
  preserve. A dead `let` doesn't hide a divergence.
- **Aggregate SROA** is sound because Ori has no aggregate identity.
  No source program can observe the difference between a record
  value and the parallel sequence of its fields.
- **Fold fusion** (banana, deforestation) is sound because Ori's
  iteration is structural — every loop terminates by descending
  into smaller subterms of an inductive value. Fusion laws don't
  need a termination side-condition.

A rewrite added to Core inherits these properties — every rule
should preserve them without needing a per-rule soundness argument.
If a rule needs one, the layer is wrong or the rule is unsound.

## What we explicitly reject

Design choices that look attractive and that we deliberately don't
make:

- **CCC-style combinators (`id`, `∘`, `fst`, `snd`, …).** Pleasant
  for fusion but far from source; debugging output becomes
  incomprehensible.
- **ANF as the Core form.** Cleaner for dataflow but buries the
  algebra under naming. Better to ANF-normalize *before* SSA
  lowering as a separate pass; keep Core direct-style.
- **CPS.** Wrong shape for algebraic rewriting; right shape for
  compilation. Not Core's job.
- **Sea-of-nodes.** Wrong layer for algebra; V8 is moving away
  from it anyway.
- **de Bruijn indices for binders.** Alpha-equivalence becomes
  free, useful if we ever adopt e-graphs, but less readable and
  harder to debug. A canonicalize pass can add this if/when needed.
- **`Record` / `Tuple` as Core variants.** SROA-ed at AST → Core
  for the reasons above.
- **Arithmetic / cast / range as Core variants.** Their natural
  rewrite home is the SSA layer (constant folding), not Core. They
  flow through as builtin `App` targets.
- **e-graphs / equality saturation.** Ori's rewrite laws are mostly
  monotonic (fusion strictly improves cost), so hand-rolled rules
  applied to fixpoint match what cost-based extraction would find.
  The infrastructure isn't free, and the value over hand-rolled
  passes is empirically modest. Reach for e-graphs only if phase-
  ordering pain shows up in practice.
- **Effects / I/O at Core.** Ori is pure today. If/when I/O lands,
  an effect annotation on `App` is the likely shape. The pure
  subset stays as-is.
- **Higher-rank polymorphism past mono.** Would need type
  abstractions in Core. Mono runs before Core; this is moot.
