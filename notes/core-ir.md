# Core IR

The Core IR sits between Ori's AST and its SSA. It exists because
the algebraic structure of an Ori program — `Fold(f, Map(g, xs))`,
`Match(Con(tag, args), arms)`, `Fold ∘ Gen` — is the natural domain
for the rewrites Ori's language properties make unconditional, and
that structure must survive past inference and monomorphization for
those rewrites to apply.

## Motivation

Algebraic rewrites — fusion, case-of-case, case-of-known-constructor,
free theorems, hylomorphism deforestation, whole-program
specialization, compile-time evaluation of arbitrary closed total
terms — are **unconditional on total subtrees** in Ori. No side
conditions, no ⊥-safety arguments, no fixpoint over the call graph.
The soundness cost is paid once, at the language level, not at every
rewrite site.

These rewrites operate on the **algebraic structure** of the
program — `Map`, `Fold`, `Con`, `Match`. By the time the program
reaches SSA, that structure is gone: aggregates decomposed into
parallel `Value`s, folds are loops with block params, map-over-map
is two loop-with-buffer patterns separated by an allocation.
Recovering the algebra at SSA is the SCEV pattern in miniature —
substantial engineering to reconstruct what the front-end already
knew. **Core exists to preserve the algebra past inference and
mono so the rewrites can run on the natural shape.**

### The guarantees

Each property names what Ori enforces and the optimizations it
enables.

#### Totality

Structural recursion only; every closed term reduces in bounded
time. **The one allowed source of partiality is the explicit
`Crash` variant** — totality is therefore a *derived bit* on every
function and subtree, computed bottom-up over the DAG call graph
in a single pass.

- Every equational rewrite preserves totality unconditionally on
  total subtrees.
- Compile-time evaluation works on any closed total term —
  `factorial 10` becomes the literal `3628800`. Evaluation respects
  a fuel budget; total ≠ feasibly computable.
- Hylomorphism deforestation works fully: `Fold f z (Gen g b) → Hylo`
  eliminates the intermediate inductive type entirely.
- Free theorems via parametricity hold without side conditions on
  total subtrees (`length . map f = length` requires `f` total;
  on a crash-tainted `f`, the law holds modulo the inserted crash).

#### Structural recursion (no general recursion)

Loops are folds over inductive types — the data's shape is the
loop bound.

- Trip counts are syntactic; no SCEV needed at Core.
- Fold fusion laws are universal, not heuristic.
- TCO isn't a separate analysis — folds *are* loops at lowering.
- Static unrolling over known-shape data: `Fold f z [a,b,c]`
  becomes `f(f(f(z, a), b), c)`, no loop emitted.

#### Purity

No source-level mutation, no effects in the pure fragment.
`BufAppend` / `BufSet` are *cow* operations — they produce new
values; the runtime may reuse memory when `rc == 1` but the
observable semantics is functional.

- Memoization sound (compile-time and runtime).
- Speculative evaluation sound on total subtrees; reordering free
  there.
- Dead-binding elimination on a total `value` needs no effect
  analysis.
- CSE needs no alias analysis.

#### Strictness

Left-to-right, no laziness. Underwrites the deterministic
evaluation order the other guarantees assume; no distinct
algebraic payoff of its own. Strictness is what makes `Crash`'s
position observable (and therefore what makes totality a useful
derived property).

#### Lambda-lifted, first-order calls

Every `App` resolves to a known top-level target.

- All call edges statically known. No virtual calls;
  devirtualization is free.
- Inlining is purely syntactic substitution.

#### DAG call graph

No mutual recursion across user functions.

- Single-pass bottom-up optimization. Topo-sort callees first; by
  the time `f` is processed, every callee is at its optimized form.
  No fixpoint iteration over the graph.
- Bounded inlining (in topological order).
- Bounded whole-program specialization (`callsites × shapes`).
- Whole-program escape analysis as a finite DAG walk.
- The **totality bit** propagates over the DAG in one walk.
- Cross-function CSE: inline, then dedupe.

#### No aggregate identity

No pointer-take on records, no by-reference equality, no FFI
opacity, no varargs.

- **Core→SSA may unconditionally SROA every aggregate.** No escape
  analysis needed. Records, tuples, and the `List` trio are
  *single values at Core* and flatten at the lowering layer.
- Aggregate-returning `If` / `Match` at Core is a single `Match`
  producing a single value — no per-slot duplication at the
  algebraic layer. SROA at lowering produces the parallel-slot
  SSA.

This last property is the keystone: it lets Core preserve full
algebraic structure (values nest, `Con(record_fields...)` is just a
constructor, `Fold(Fold(...))` is direct nesting) while delivering
"no boxing by default" as a **lowering guarantee** rather than an
IR shape.

## Architecture

Three rewriting paradigms, each at the level where its information
is visible:

| Layer          | Job                  | Style                       | Examples                                                |
| -------------- | -------------------- | --------------------------- | ------------------------------------------------------- |
| `passes/core/` | Algebraic rewriting  | Pattern rewriting on terms  | fusion, beta, eta, case-of-case, banana, free theorems  |
| `src/opt/`     | Scalar dataflow      | Local SSA peephole          | const-fold, branch-fold, DCE, GVN, rc-fusion, LICM      |
| `src/lower/`   | Resource discipline  | Declarative emission        | FBIP via cow_*, RC traffic, aggregate decomposition     |

**The placement rule:** if a rewrite's natural form is `Map`,
`Fold`, `Con` — i.e. the algebra of the source — it belongs in
`passes/core/`. If its natural form is "find a chain of `Binary`
instructions and constant-fold" — i.e. SSA shape — it belongs in
`src/opt/`. Putting either at the wrong layer forces the SCEV
pattern: reconstructing structure the layer above threw away.

The bottom layer is not a rewrite layer — it's where the source's
semantics get expressed as IR. The middle layer is local dataflow
rewriting where the SSA shape is natural. The top layer is
algebraic rewriting where the term structure is natural.

## From source to Core

Core's variant set is small because the front end has done
substantial work to massage the AST into a shape where the
algebraic structure is uniform.

### Pre-Core passes

In source-to-Core order, each pass with the invariant it establishes:

1. **Parse → resolve.** Every identifier becomes a `SymbolId`;
   imports and declarations registered in the symbol table.
2. **`fold_lift`.** Every source `fold` expression becomes a Call
   to a synthesized top-level `__fold_N(target, captures...)`
   helper. *Establishes:* the only iteration form left is a known
   helper — `Fold` recognition becomes a structural match.
3. **`flatten_patterns`.** Nested constructor patterns and
   record/tuple patterns inside arms hoist into chained `is`-guards
   and per-field destructures. *Establishes:* every arm's top
   pattern is shallow.
4. **`lambda_lift`.** Every source lambda becomes a top-level
   `FuncDef` whose leading params are captures; the lambda site
   becomes a `Closure { func, captures }` placeholder.
   *Establishes:* no lambda expression survives — every call is
   `App` to a known top-level target.
5. **`topo`.** Topologically sorts the call graph. Mutual recursion
   is rejected. *Establishes:* the call graph is a DAG.
6. **`infer`.** Hindley-Milner with row-polymorphic lambda sets.
   *Establishes:* every AST `Expr` has a resolved `Type`; method
   calls have resolved targets.
7. **`mono`.** Full monomorphization. *Establishes:* every call
   site resolves to a monomorphic target; no `Type::Var` in
   expression positions.
8. **`lambda_solve` + `lambda_specialize`.** Solves lambda sets;
   specializes higher-order functions per set. *Establishes:* every
   `Arrow`'s lambda set is closed and concrete.
9. **`lambda_narrow`.** Singleton lambda sets rewrite to direct
   calls. *Establishes:* singleton-closure positions are zero-overhead.
10. **`reachable_prune`.** Drops definitions unreachable from
    `main`. *Establishes:* module contains only definitions that
    affect behavior.
11. **`totalize_builtins`.** Replaces partial builtin operations
    with their total counterparts (see *Crash and totality*).
    *Establishes:* the only partial construct is the user-visible
    `crash`.

After this pipeline, the AST is **monomorphic, fully resolved,
fold-lifted, lambda-lifted, defunctionalized, reachable-pruned,
and totalized.**

### AST → Core

Core lowering performs the final transformations that depend on
concrete types and resolved targets. Crucially, it does **not** do
SROA — aggregates stay as nested values.

- **Operator desugar.** `BinOp`, `Cast`, `Range` become `App` to
  interned builtin `FnId`s. `__builtin.*` intrinsics interned at
  compile init.
- **Literal pattern desugar.** `Pattern::IntLit` / `Pattern::StrLit`
  become `Binding(fresh)` plus a synthesized `Eq(fresh, lit)`
  guard.
- **String literal desugar.** `"abc"` becomes a `BufLit` of byte
  `Lit::Int`s (`Str ≡ List(U8)`).
- **Method-call resolution.** `MethodCall` / `QualifiedCall`
  become `App` with the mangled target interned to a `FnId`.
- **Closure construction.** Lambda-lift's `Closure { func,
  captures }` becomes `Con { tag: TagId::Closure(...), args:
  captures, ty }`.
- **Fold recognition + shape annotation.** Calls to `__fold_N`
  helpers become `Fold` nodes. If the helper's body matches a
  recognized algebra template (`Map`, `Filter`, `Scan`, ...), the
  resulting `Fold.shape` is `Some(MatchedShape)`; otherwise `None`.

### What Core can assume

By the time Core lowering completes:

- Every `App.target` is a `FnId` resolving to either a builtin
  (dispatched inline at lowering) or a top-level definition.
- Every type is monomorphic in expression positions. `CoreType`
  doesn't have a `Var` variant — type-variable values can't be
  expressed.
- Every iteration is a `Fold` (catamorphism) or `Gen`
  (anamorphism). General recursion is structurally absent.
- Every closure is a `Con` value with a `TagId::Closure(_)` tag.
- Every match arm is shallow; nested patterns are guard chains.
- The call graph is a DAG; topological order is meaningful.
- The module contains only reachable definitions.
- Every builtin operation is total. The only partial construct is
  `Crash`.

These invariants are what let Core stay small. Removing any
pre-Core pass would force Core to grow a variant or carry an
analysis to recover the lost structure.

## The IR

```rust
enum Expr {
    // Universal
    Var   { sym: LocalId, ty: CoreType },
    Lit   { value: Literal, ty: CoreType },
    App   { target: FnId, args: Vec<Expr>, ty: CoreType },
    Let   { binder: LocalId, value: Box<Expr>, body: Box<Expr>, ty: CoreType },

    // Algebraic structure
    Match { scrutinee: Box<Expr>, arms: Vec<MatchArm>, ty: CoreType },
    Con   { tag: TagId, args: Vec<Expr>, ty: CoreType },
    Fold  {
        kind: FoldKind,                  // Total | EarlyExit
        fold_fn: FnId,
        target: Box<Expr>,
        init: Vec<Expr>,
        captures: Vec<Expr>,
        shape: Option<FoldShape>,        // Map | Filter | ... — verified
        ty: CoreType,
    },
    Gen   {
        bound: Box<Expr>,                // bounded anamorphism
        step_fn: FnId,
        init: Vec<Expr>,
        captures: Vec<Expr>,
        elem_ty: CoreType,
        ty: CoreType,
    },

    // Divergence
    Crash { msg: StrLit, ty: CoreType },  // msg is a static string literal

    // Buffer primitives (single-valued; trio is an SSA story)
    BufLit          { elements: Vec<Expr>, elem_ty: CoreType, ty: CoreType },
    BufLoad         { buf: Box<Expr>, idx: Box<Expr>, ty: CoreType },
    BufLoadUnchecked{ buf: Box<Expr>, idx: Box<Expr>, ty: CoreType },
    BufAppend       { buf: Box<Expr>, val: Box<Expr>, ty: CoreType },
    BufSet          { buf: Box<Expr>, idx: Box<Expr>, val: Box<Expr>, ty: CoreType },
}

enum Pattern {
    Constructor { tag: TagId, binders: Vec<Binder> },
    Wildcard,
    Binding(LocalId),
}

enum Binder { Sym(LocalId), Wildcard }

enum TagId {
    Declared(DeclTagId),  // user-declared tag union
    Closure(ClosureTagId), // synthesized __Closure_X
}

enum CoreType {
    Prim(Scalar),                   // I8..I64, U8..U64, F32, F64, Bool
    Adt(TypeId, Vec<CoreType>),     // monomorphic constructed type (no Var)
}

enum FoldKind { Total, EarlyExit }   // EarlyExit returns Step(b)
enum FoldShape { Map, Filter, Scan, Zip, Take, Drop } // grows with rule set
enum Literal { Int(i64), Float(f64) }
```

Thirteen `Expr` variants. Direct-style (not ANF), typed at every
node, post-monomorphization, single-valued throughout.

### Earn-its-keep principle

A variant earns its keep when **erasure of its shape is
irreversible downstream**. Three cases manifest this:

1. **Source-circular to define.** `Fold` and `Gen` can't be expressed
   in pure source without general recursion.
2. **Load-bearing for a runtime invariant** the rest of the IR
   can't express. `BufAppend` / `BufSet` carry FBIP mutation intent;
   without them the SSA layer would reconstruct from alloc + store
   patterns.
3. **An algebraic rewrite matches on its shape**, and the shape is
   gone after lowering. `Match`, `Con`, `Fold`, `Gen`, `Crash` —
   collapsing into `App` makes case-of-known-constructor,
   case-of-case, fusion, hylo-deforestation, and crash-barrier-
   detection all recognize-by-convention, which is silent-miscompile-
   prone.

Every variant passes at least one. **Constant folding doesn't
qualify**: `1 + 2` is equally foldable at any layer, so `BinOp` is
not a variant — it's an `App` to a builtin `FnId`. Same for `Cast`
and `Range`'s scalar arithmetic.

### Types in Core

`CoreType` is **a separate enum from inference's `Type`**, by
construction unable to express `Type::Var`. AST → Core converts
and fails loudly on residual Vars. The polymorphic-`Con.ty` trap
the previous design suffered cannot occur — there's no surface
for it.

- `CoreType::Prim(Scalar)` — `I8`–`I64`, `U8`–`U64`, `F32`, `F64`,
  `Bool`.
- `CoreType::Adt(TypeId, Vec<CoreType>)` — a monomorphic
  constructed type. `Result(I64, Str)` is `Adt(Result, [I64, Str])`.

There's no `Arrow` variant. Function references at Core go through
`FnId`, which the symbol table maps to a signature; there's no
need to model the function type as a value carried by other terms,
because closures aren't values at Core (see *Closures*).

Transparent newtypes (`Str := List(U8)`) are resolved at AST → Core
— the underlying `Adt(List, [U8])` is what Core sees. Opaque
newtypes are likewise resolved; Core operates on the underlying
shape.

`TagId` is **kinded** — `Declared(_)` for user tag unions,
`Closure(_)` for the synthesized `__Closure_X` family. The two
paths share no code in lowering or rewriting; mixing them up is a
type error.

### Evaluation order

Strict, left-to-right. At each variant:

- `App(f, args)` — args left to right, then call.
- `Let(value, body)` — value before body.
- `Match(scrutinee, arms)` — scrutinee, pattern dispatch, then
  guards left to right, then arm body.
- `Fold` / `Gen` — target/bound, then init, then captures, then
  the loop.
- `Con(args)` — args left to right, then construction.

Purity makes evaluation order unobservable on total subtrees;
rewrites that reorder *total* expressions are unconditionally
sound. Order matters at `Crash` boundaries: a rewrite that moves
an expression across a `Crash` changes whether the expression
runs, so `Crash` is a syntactic barrier (see *Crash and totality*).

### Per-variant rationale

| Variant            | Justification                                                                                                                              |
| ------------------ | ------------------------------------------------------------------------------------------------------------------------------------------ |
| `Var`              | Trivial — reference a binding.                                                                                                            |
| `Lit`              | Scalar literal (Int, Float). Strings desugar to `BufLit`.                                                                                  |
| `App`              | First-order call. `target: FnId` resolves to a top-level definition or a builtin dispatched inline.                                       |
| `Let`              | Single-binder. Binding scope for let-floating, CSE, dead-binding elimination.                                                              |
| `Match`            | Non-recursive case analysis. Single scrutinee value; case-of-case and case-of-known-constructor are syntactic.                            |
| `Con`              | Tag-union constructor — including records (single-tag), tuples (single-tag), closures (`TagId::Closure(_)`). Case-of-known-constructor.    |
| `Fold`             | Catamorphism. `kind` separates total from `EarlyExit` (Step-returning); fusion laws differ between them. `shape` records verified algebra. |
| `Gen`              | Bounded anamorphism (range, replicate, tabulate). Enables hylo deforestation as a syntactic match against `Fold ∘ Gen`.                    |
| `Crash`            | Explicit divergence. The one partial construct; structural barrier for rewrites. Replaces name-recognition on `__crash`.                  |
| `BufLit`           | Buffer literal. Without it every literal would chain `BufAppend`s. Also: literal-to-static-data lowering matches on this shape.            |
| `BufLoad`          | Bounds-checked index, returning `Result<T, OutOfBounds>` shape. The check is observable in the IR; Core rewrites can elide it.            |
| `BufLoadUnchecked` | Produced by bounds-elimination rewrites that prove `idx < len`. **Never emitted by AST → Core.** The variant exists so the rewrite has a representable output. |
| `BufAppend`        | FBIP intent. Lowers to `cow_resize_dyn`. Without it the lowering layer would reconstruct mutation intent from alloc + store patterns.    |
| `BufSet`           | FBIP intent. Lowers to `cow_store_dyn`. Same rationale.                                                                                   |

### Fold in detail

`Fold` is the central rewrite target. Each field:

| Field      | Meaning |
| ---------- | ------- |
| `kind`     | `Total` (catamorphism, fold_fn returns `b`) or `EarlyExit` (fold_fn returns `Step(b) = Continue(b) \| Break(b)`). Lowering emits different shapes; fusion laws differ. |
| `fold_fn`  | `FnId` of the lifted helper. After fold-lift the body holds the structural recursion. |
| `target`   | The inductive value being consumed (single Expr; nested algebra preserved). |
| `init`     | Seed accumulator values. Empty for pure catamorphisms; populated for walk-style folds. |
| `captures` | Free variables of the fold closure, threaded as loop block params. |
| `shape`    | `Some(FoldShape)` when AST→Core verified the body matches a known algebra template; `None` when opaque. Drives rewrite matching. |
| `ty`       | Result type. |

**On `shape`**: AST → Core checks the synthesized fold body
against a closed set of algebra templates (the `FoldShape`
variants). A match stamps the shape; a near-miss is a developer
hint that gets surfaced when the user explicitly requested a
shape (the source-level `@map` annotation, when present, is a
*demand* — disagreement is a compile error, not a silent miss).

`FoldShape` is a **closed enum tied to the rewrite rule set**:
adding `Filter` to `FoldShape` is the same commitment as adding
the filter fusion rules. The enum never grows past what rules
exist; opaque folds always fall back to `shape: None` and still
work, just without seeing inside.

**Fusion laws differ by `kind`**: total folds satisfy
`fold/build`-style cata-fusion (Gill, Launchbury, Peyton Jones,
*A Short Cut to Deforestation*, FPCA 1993); early-exit folds
satisfy stream-fusion-style laws (Coutts, Leshchinskiy, Stewart,
ICFP 2007). Each rule lists the `FoldKind` it applies to.

### Gen in detail

`Gen` is the anamorphism — the unfold dual of `Fold`. Without it,
hylo deforestation couldn't be syntactic.

| Field      | Meaning |
| ---------- | ------- |
| `bound`    | Value computed before the loop that determines the maximum number of steps. Totality is preserved because `bound` is a finite value (e.g., the count for `List.range`). |
| `step_fn`  | `FnId` of the per-step function: `(i, captures) → elem`. |
| `init`     | Seed values threaded through if the generator is stateful (e.g., `iterate`). |
| `captures` | Loop-invariant free variables. |
| `elem_ty`  | Element type produced; `ty` is then `List(elem_ty)`. |

`List.range(start, end)` lowers as `Gen { bound: end - start,
step_fn: __range_step, init: [start], captures: [], elem_ty: I64,
... }`. The key fusion rule `Fold(f, init, Gen(bound, step, ...))
→ Hylo(...)` eliminates the intermediate list entirely.

### Match and Con: case-of-* are syntactic

Because values nest at Core, the classical algebraic rewrites
fire as direct pattern matches:

- **Case-of-known-constructor.** `Match(Con(tag, args), arms) →
  arms[tag][args]`. No analysis, no fixpoint.
- **Case-of-case.** `Match(Match(e, arms₁), arms₂) →
  Match(e, [{ pat, guard, body: Match(body, arms₂) } for arm in
  arms₁])`. Code duplication is bounded by join points (see
  *Future variants*).
- **Projection-of-known-constructor.** `Match(Con(field_pattern,
  binders), [pat → binder])` is just constructor injection +
  pattern projection canceling — a syntactic identity.

Records and tuples are `Con`s with a single tag (`TagId::Declared`
for the record/tuple's nominal type). Field access compiles to
`Match` with a single arm; the pretty-printer renders it as
projection. **No `Record` or `Tuple` variants** because the
syntactic shape is exactly `Con` over a one-variant union.

### Patterns

Three shallow shapes:

- `Constructor { tag, binders: Vec<Binder> }` — match a tag-union
  variant. `binders` is one entry per source-level field.
- `Wildcard` — match anything, bind nothing.
- `Binding(LocalId)` — match anything, bind to the local.

`Binder` is an enum (`Sym(LocalId) | Wildcard`), not a sentinel.
Wildcards-inside-constructors are structurally distinguishable
from real binders.

Literal patterns are gone — `Pattern::IntLit` / `Pattern::StrLit`
desugar to `Pattern::Binding(fresh)` plus a synthesized
`Eq(fresh, lit)` guard at AST → Core. Three shapes cover
everything.

**Return arms.** `MatchArm.is_return: bool` short-circuits the
enclosing function (`?` operator desugar). Rewrites that flatten
nested matches must preserve this — case-of-case in the presence
of return arms is a known sticky case where **join points** (see
below) are the principled future fix; for now, the rule
preservation is a *carried invariant* (validator-checked).

### Closures and HOFs

After `lambda_lift` + `lambda_specialize` + `lambda_narrow`, every
closure is a `Con` value with a `TagId::Closure(_)` tag:

1. **Each lambda becomes a top-level function.** `__lambda_K(captures..., args...)`.
2. **The closure value is a `Con`.** `Con { tag: Closure(K), args:
   captures, ty: Adt(__Closure_X, ...) }`. Same shape as any
   payload-carrying union.
3. **Calling a closure dispatches via `__apply_K`.** `App(__apply_K,
   [closure_value, args...])`. The synthesized `__apply_K` body is
   a `Match` over the closure tag forwarding to the right
   `__lambda_K`.
4. **Singleton lambda sets are direct calls.** `lambda_narrow`
   rewrites `App(__apply_K, [closure, args...])` to
   `App(__lambda_K, [captures..., args...])` when the lambda set
   has one element.

Higher-order functions look like any other tag-union consumer.
`xs.map(f)` where `f` is a closure compiles to a `Fold` whose
`fold_fn` is `__apply_K` (or, in the singleton case, the
`__lambda_K` directly) and whose `captures` include the closure
value.

### Crash and totality

Crash semantics is the design's hardest call. Three options
exist; this design takes the third.

1. **Poison (crashes as values)**: validates every rewrite but
   forces runtime tag-checks everywhere. Beautiful semantics,
   dishonest implementation.
2. **Imprecise exceptions**: GHC's choice. Recovers most
   reordering at the cost of "the program crashes with *some*
   crash from a set" semantics; in a strict language, dead-let
   elimination still needs a refinement direction.
3. **Track totality, totalize the builtins**: the partial constructs
   shrink to exactly one — the user's explicit `crash` — and a
   totality bit propagates over the DAG. Total subtrees get
   unconditional algebra; crash-tainted subtrees treat `Crash` as a
   syntactic barrier.

The third option requires two halves working together.

**Half one: totalize the builtins.** AST → Core's
`totalize_builtins` pass makes every builtin total at the source
level:

- **`x / 0 = 0`** and **`x % 0 = 0`**. Lean-style. Users who care
  pre-check the divisor (the type system can encode `NonZero(T)`
  for the unchecked form; `divChecked: I64 → I64 → Result(I64,
  DivByZero)` is the explicit-check form).
- **Integer overflow wraps** (two's-complement, C-style).
  Explicit `add_checked` / `mul_checked` return `Result(T,
  Overflow)`.
- **Cast saturates.** `cast::<U8>(-1)` is `0`. Explicit
  `try_cast: T → Result(U, CastError)` returns `Result` for the
  range-violating case.
- **`BufLoad` returns `Result<T, OutOfBounds>`**. Bounds violation
  is operationally distinct (the user needs to handle the failure
  with different control flow), so Result is the right shape.

After totalization, **the only partial construct in any Ori
program is `crash(msg)`**.

**Half two: `Crash` is a variant; totality is a derived bit.**
`Expr::Crash { msg: StrLit, ty: CoreType }`. The message is a
static string literal — guaranteeing `Crash` is a leaf node and
the rewrite-barrier semantics are simple.

Totality of a function/subtree is computed bottom-up:

```
total(Crash _) = false
total(App f args) = total(f) ∧ all total(args)
total(Match s arms) = total(s) ∧ all (total(arm.guards) ∧ total(arm.body)) for arms
total(Fold _ _ t i c _) = total(t) ∧ all total(i) ∧ all total(c)
... etc, recurse through fields
```

A function's `total` bit is `total(body)`; the bit propagates
over the DAG call graph in one walk. With this, every law in the
*Motivation* section gets the honest statement:

- "Equational rewrites preserve totality unconditionally" — on
  total subtrees.
- "Dead-binding elimination needs no effect analysis" — when
  the bound value is total.
- "Free theorems hold without side conditions" — on total
  subtrees.

In crash-tainted subtrees, rewrites obey two contracts:

- **Reordering past `Crash` is unsound** — the divergence's
  source-level position is observable. Rewrites that move
  expressions across a `Crash` are barred.
- **Eliminating dominated `Crash`es is sound** — `Crash; Crash` is
  `Crash`.

The "is this a barrier?" check is a variant match (`is Crash`),
not a name comparison against `__crash`. Forgetting it is a
**compile error**, not a silent miscompile.

### The buffer trio (an SSA story)

`List(T)` and `Str = List(U8)` are **single values at Core**.
There is no slot list, no `(len, cap, data)` decomposition at the
algebraic layer. `xs.len()`, `xs.append(y)`, `xs == ys` all
operate on `List(T)` values.

The trio decomposition `(len: U64, cap: U64, data: RcPtr)`
happens at **Core → SSA**, at the function-boundary ABI. Multi-
result calls return the three slots; pattern binders bind three
SSA values; payload `Con`s store the trio inline. The only place
the trio collapses to a single header pointer is the `__main` ABI
boundary.

`cap` is intentionally not part of value equality at any layer —
two lists with the same length and elements are equal regardless
of allocated capacity. The structural equality lowering (length
check + elementwise loop) ignores `cap` by construction.

Element layout in the data buffer: each source-level element
occupies `slot_count(elem_ty) * 8` bytes. `List(I64)` strides 8;
`List({a: I64, b: I64})` strides 16. The `elem_ty` field on
`BufLit` / `BufAppend` / `BufSet` carries the stride info; SSA
reads it.

**Why this works at Core**: no Core rewrite needs the slots
separately. `len` laws (`len(xs.append(y)) = len(xs) + 1`) work
at the value level. Bounds elimination relates `idx` to `len`
within the same value (not across slots). The trio's consumers —
multi-result ABI, stride calculation, cow calls — are all SSA
concerns.

This is the *No aggregate identity* guarantee paying off: SROA at
Core→SSA is unconditionally sound, so Core gets to keep `List` as
a single value while still delivering "the trio doesn't box" as a
lowering guarantee.

## Refcounting, ownership, and reuse

Ori's runtime model is Perceus-style precise refcounting plus
FBIP: every heap object carries an `rc`; mutating primitives
(`BufAppend`, `BufSet`) lower to `cow_*` runtime checks; reaching
`rc == 0` frees and recursively decrements children.

The split between **operations** and **analyses** decides what
lives at Core vs. SSA.

### Operations live at SSA

Instruction-level mechanics — `rc_inc`, `rc_dec`,
`cow_resize_dyn`, `cow_store_dyn`, hypothetical `reuse_alloc` —
are per-instruction events with precise placement requirements.
SSA's dominance and def-use chains make this natural.

Putting raw RC ops at Core would force every algebraic rewrite to
thread `dup` / `drop` through to keep refcounts honest, with no
algebraic benefit. The Core IR has **no `Dup` / `Drop` variants**.

Auto-rc conventions at SSA: `Store(ptr, off, val)` with `val.ty ==
RcPtr` auto-`rc_inc`s `val`; `Load`/`LoadDyn` of an `RcPtr`
auto-`rc_inc`s the loaded value. Explicit `rc_inc`/`rc_dec` balance
these around consuming uses and scope ends.

### Analyses live at Core

Refcount optimizations want algebraic structure. That structure is
gone at SSA. Each analysis is a walk over the Core term producing
an annotation; SSA emission consumes the annotation to make a
precise choice instead of the conservative default.

| Analysis              | What it proves                                                          | SSA emission change                                    |
| --------------------- | ----------------------------------------------------------------------- | ------------------------------------------------------ |
| Uniqueness            | This value is never aliased — no store, no escape, no capture          | Skip the counter entirely; treat as a stack value     |
| Borrow inference      | This function arg is only inspected, never stored or returned          | Caller skips the inc before the call                  |
| Reuse fusion (FBIP)   | This `Match` arm drops a `Cons` box and constructs a same-shape `Cons` | Emit a reuse-alloc instead of free + alloc            |
| Drop specialization   | This `drop x` is over `x: Result(I64, Str)`                            | Inline the type-directed drop instead of generic call |
| Loop-invariant cow    | This `BufAppend` runs inside a `Fold` whose target is unique           | Hoist the rc check out of the loop; emit unchecked path inside |

**Reuse analysis is pinned as the final Core pass**, after the
rewrite fixpoint. Rewrites produced before reuse fusion can change
which alloc/drop pairs exist; running reuse mid-rewrite invalidates
its own results.

### Variants carry intent; annotations carry analysis output

A variant earns its keep when **lowering needs to distinguish a
shape**:

- `BufAppend` / `BufSet` carry mutation intent at the variant
  level. The lowering doesn't ask "could this be in-place?" —
  the variant says "this is an FBIP mutation site."
- `Fold` carries iteration semantics. Lowering specializes RC
  handling for the loop.
- `BufLoadUnchecked` carries the bounds-elimination result. The
  alloc site / load shape is genuinely different.

An out-of-band annotation suffices when the analysis result is
"this site is special" with no new lowering shape needed.
Uniqueness, borrow flags, loop-invariant-cow markers all fit this.

### Goal 5 honestly

"C-competitive" depends on uniqueness and reuse analyses landing.
Concretely:

- On unique-buffer code, FBIP delivers C-level performance — the
  cow check is a predictable branch on a cached header word.
- On shared-buffer code without uniqueness analysis, `xs.append`
  in a loop is O(n²) (Swift's COW arrays have this exact
  footgun). The analysis hoists the check out of the loop on the
  unique-target case; without it, the cliff is real.
- `BufLoad`'s bounds check has to fire at the Core layer
  (rewriting to `BufLoadUnchecked` when the index is provably in
  range) for tight loops to match C. Without it, every load pays
  the check + the Result-shape projection.

The Core IR makes these optimizations *expressible*; the work to
make them *happen* is in the analysis passes that produce the
annotations.

## Soundness

The algebraic rewrites that Core enables are sound only because of
the language guarantees:

- **Reorderings on total subtrees** (CSE, code motion,
  let-floating) are sound because Ori is pure and the subtree
  contains no `Crash`. The totality bit makes "is this subtree
  reorderable" a one-variant-match check.
- **Compile-time evaluation** of any closed total term is sound
  because Ori is total within the bit. The evaluator respects a
  fuel budget.
- **Eliminations** (dead-let, unreachable arm, case-of-known-
  constructor) on total values are sound; on crash-tainted values,
  the rewrite must preserve the crash's position.
- **Aggregate SROA at Core → SSA** is sound because Ori has no
  aggregate identity. No source program can observe the difference
  between an aggregate value and the parallel sequence of its
  slots.
- **Fold fusion** (banana, deforestation, hylo) is sound because
  Ori's iteration is structural and the bound on `Gen` is finite.
- **Crash barriers** make all of the above precise: a rewrite that
  preserves the crash set's content and ordering is sound; a
  rewrite that doesn't isn't.

Every Core rewrite either operates within a total subtree (where
laws are unconditional) or preserves crash position and content
(where laws are conditional but checkable).

## What we deliberately reject

- **Crashes as first-class values (poison).** Beautiful algebra,
  dishonest implementation.
- **CCC-style combinators (`id`, `∘`, `fst`, `snd`, ...).**
  Pleasant for fusion but far from source; debugging output
  incomprehensible.
- **ANF as the Core form.** Cleaner for dataflow but buries the
  algebra under naming. ANF-normalize at Core → SSA if needed.
- **CPS.** Wrong shape for algebraic rewriting; right shape for
  compilation. Not Core's job.
- **Sea-of-nodes.** Wrong layer; V8 is moving away from it anyway.
- **de Bruijn indices.** Alpha-equivalence becomes free but
  debugging suffers. Canonicalize pass can add this if/when needed.
- **`Record` / `Tuple` as Core variants.** Records are single-tag
  `Con`s; tuples are single-tag `Con`s; field projection is a
  one-arm `Match`. No inert plumbing.
- **`BinOp` / `Cast` / `Range` as Core variants.** Their natural
  rewrite home is the SSA layer (constant folding). They flow
  through as builtin `App` targets.
- **`Type::Var` in Core.** Structurally impossible to express via
  `CoreType`'s shape.
- **Arithmetic / cast / range as Core variants.** Builtin `App`s
  to bodyless targets the lowering layer dispatches inline.
- **Slot decomposition at Core.** Values nest; the trio and SROA
  happen at Core → SSA. The "no boxing by default" guarantee is
  delivered as a lowering guarantee, not an IR shape.
- **`Dup` / `Drop` / explicit RC ops.** Pollutes algebraic
  rewrites for no algebraic benefit. RC operations live at SSA;
  RC analyses live at Core; the seam is annotations.
- **`Type` as a value (System F-style).** Mono runs before Core;
  there are no type abstractions to move around.
- **e-graphs / equality saturation.** Our rewrite laws are mostly
  monotonic (fusion strictly improves cost). Hand-rolled rules to
  fixpoint match what cost-based extraction would find. Adopt
  e-graphs only if phase-ordering pain shows up in practice.
- **Effects / I/O at Core.** Ori is pure today. If/when I/O lands,
  an effect annotation on `App` is the likely shape. The pure
  subset stays as-is.
- **Higher-rank polymorphism past mono.** Mono runs before Core;
  moot.

## Future variants (reserved seats)

Two variants are planned but not in the initial set. Each closes a
hole the current design papers over with a *carried invariant*;
adding them is additive.

- **Join points.** `LetJoin { label, params, body, cont }` +
  `Jump { label, args }` — second-class continuations. Maurer,
  Downen, Ariola, Peyton Jones, *Compiling without Continuations*,
  PLDI 2017. Make case-of-case fire without code explosion. Match
  arm `is_return` is the interim; case-of-case in its presence is
  the current sticky case. Reserved seat in the IR's variant set.

- **Reuse / Reset.** `Reuse { box, tag, fields }` + `Reset { box,
  tag }` — explicit FBIP reuse for user-defined inductives.
  Lorenzen & Leijen, *Reference Counting with Frame-Limited
  Reuse*, ICFP 2022. Adds variants when reuse fusion for user
  inductives lands. Until then, reuse stays an annotation produced
  by the final Core pass and consumed by SSA emission.

Both are additive — they don't replace anything, and the existing
variants continue to work. The IR is designed with these seats
reserved so the eventual addition is a strict extension.
