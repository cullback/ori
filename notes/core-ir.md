# Core IR

## Status

Design note. We are committing to building this. The empirical gate
(measure fusion benefit on real programs before committing) is
*folded into the development plan itself* — the first end-to-end
demonstrable benefit is the gate that justifies more rules.

## The problem this solves

Ori's design hands you a set of language guarantees that mainstream
optimizing compilers fight thousands of lines of engineering to recover:
totality, purity, strictness, lambda-lifted first-order calls, and a
DAG call graph (no mutual recursion; the only recursion is structural
via `fold`). Those guarantees enable algebraic rewriting — fusion,
case-of-case, free theorems, hylomorphism deforestation, whole-program
specialization, compile-time evaluation of arbitrary closed terms — to
be **unconditional**. No side conditions, no ⊥-safety arguments, no
fixpoint over the call graph.

These optimizations are most naturally expressed on the **algebraic
structure of the program**: terms like `Map(f, Map(g, xs))`. By the
time we reach SSA, that structure has been flattened. Aggregates are
decomposed into parallel `Value`s. Folds are loops with block params.
The map-of-map is two loop-with-buffer patterns separated by an
allocation. Recovering the algebra at the SSA layer is the SCEV
problem in miniature — a substantial engineering investment to
reconstruct what was thrown away.

The fix is to put a layer between AST and SSA where the algebraic
structure is still visible and rewrite on it directly.

## What triggered this note

We built a fusion pass at the SSA layer (`src/opt/stream_fuse.rs`,
`src/ssa/loops.rs`) that detects writer/reader buffer pairs and
fuses them. It worked on a synthetic test case. Then we noticed:

- `loops.rs` reconstructs the IV + iteration domain from block-param
  patterns. The AST already had this; we threw it away in lowering.
- `stream_fuse` reconstructs "this is the same buffer flowing through"
  from def-use chains over decomposed aggregates. The AST had this too.
- The domain congruence check (`Const(k) ≡ Const(k)`) reconstructs
  "these loops iterate over the same range." The AST node literally
  *was* the range.

This is the SCEV pattern: do analysis to recover information that the
front-end already knew. Wrong layer.

## Git history

`efa77e8` ("refactor: eliminate Core IR, add typed SSA") deleted a
Core IR with seven primitives (`Var, Lit, App, Let, Match, Fold,
Record`). The commit message: "Collapse AST→Core→SSA pipeline into
direct AST→SSA lowering." At the time there was no optimization pass
exploiting Core's structure — Core was a pass-through. Removing it
was reasonable cleanup *then*. It's the wrong move *now* because
fusion is precisely the optimization that wants that layer back.

## What the language properties unlock

The architectural pitch isn't "we want deforestation." It's that the
list below becomes tractable *only if the Core layer preserves the
structure*. At SSA each item is either expensive or impossible.

**Enabled by DAG call graph (no mutual recursion):**
1. Single-pass bottom-up optimization over the call graph. Topo-sort
   callees first. By the time we process `f`, every callee of `f`
   is at its optimized form. No fixpoint iteration over the graph.
2. Inlining is bounded and tractable. Inline in topological order.
3. Whole-program specialization is bounded: at most
   `callsites_of_f × shapes` variants per function.
4. Whole-program escape analysis is a finite DAG walk.
5. Cross-function CSE: inline, then dedupe. No termination concern.

**Enabled by totality (no ⊥):**
6. Every equational rewrite preserves totality unconditionally.
7. **Compile-time evaluation terminates trivially.** Any closed term
   reduces in bounded time. We can pre-execute `length [1,2,3] = 3`,
   `map f (filter p xs)` on known data, anywhere in the program.
8. Hylomorphism deforestation works fully: `cata f ∘ ana g = hylo f g`
   eliminates the intermediate inductive type entirely.
9. Free theorems via parametricity hold without side conditions
   (`length . map f = length`, `id . f = f`, `map id = id`).

**Enabled by purity:**
10. Memoization is sound (compile-time and runtime).
11. Speculative evaluation is sound; reordering is free.
12. Dead-binding elimination doesn't need effect analysis.
13. CSE doesn't need alias analysis.

**Enabled by lambda-lift + defunctionalization:**
14. All call edges statically known. No virtual calls. Devirtualization
    is free.
15. Inlining is purely syntactic substitution.

**Enabled by structural fold (no general recursion):**
16. Trip counts are syntactic — the data's shape *is* the loop bound.
    No SCEV.
17. Fold fusion laws are universal, not heuristic.
18. Tail-call optimization isn't a separate analysis — folds *are*
    loops.
19. Static unrolling of folds over known-shape data — `Fold f z [a,b,c]`
    becomes `f(f(f(z,a),b),c)` and no loop is emitted.

Each of those is hundreds-to-thousands of lines in LLVM/GHC. They
exist because the source languages don't give them. Ours does.

## The architecture

Three distinct rewriting paradigms, each at the level where its
information is visible:

| Layer | Job | Style | Examples |
|---|---|---|---|
| `passes/core/` | Algebraic rewriting | Pattern rewriting on Core | fusion, beta, eta, case-of-case, banana, free theorems |
| `src/opt/` | Scalar dataflow | Local SSA peephole | const-fold, branch-fold, DCE, GVN, rc-fusion, LICM |
| `src/lower/` | Resource discipline | Declarative emission (no rewrites) | FBIP via cow_*, RC traffic, aggregate decomposition |

The bottom layer is *not* a rewrite layer. It's where the source's
semantics get expressed as IR. The middle layer is local dataflow
rewriting where the SSA shape is natural. The top layer is algebraic
rewriting where the term structure is natural.

The current code violates the layer rule once: `passes/lambda/`
contains rewrites that arguably belong at Core (defunctionalization
is a Core-level transformation). We can revisit that.

## The IR

Seven **structural** primitives + one **scalar** primitive, post-
lambda-lift, post-mono, typed, direct-style.

```rust
enum Core {
    // Structural — participate in algebraic rewrites
    Var(VarId),                            // typed variable reference (single slot)
    Lit(Literal),                          // typed scalar literal
    App(FuncId, Vec<Core>),                // first-order call to known top-level
    Let(VarId, Box<Core>, Box<Core>),      // let x = e1 in e2 (single-slot binding)
    Match(Box<Core>, Vec<MatchArm>),       // non-recursive case on tag union
    Cata(Box<Core>, Box<Core>, Box<Core>), // structural recursion (the ONLY iteration)
    Con(TagId, Vec<Core>),                 // tag-union constructor

    // Scalar — pass-through to SSA, never touched by fusion
    BinOp(BinOp, Box<Core>, Box<Core>),    // arithmetic / comparison / boolean
}
```

**No `Record`, no `Tuple`, no `FieldAccess`.** Aggregates exist at the
AST (source structure) and at SSA (decomposed parallel Values + memory
layout) — but not at Core. The IR is purely algebraic.

### How aggregates flow without IR nodes

Each Core `Expr` is conceptually **single-slot**. Multi-slot
aggregates exist as **parallel lists of Core expressions** at the
AST→Core boundary, not as IR nodes:

- `lower_expr_slots(ctx, ast) -> Vec<Expr>` — one Core Expr per slot
  of the AST expression's type. Slot count is `expand_slots(ast.ty)`,
  deterministic from type.
- Scalars: 1-element Vec. Records/tuples: N-element Vec.
- `ExprKind::Tuple` / `ExprKind::Record`: concatenate child slot lists.
- `ExprKind::FieldAccess { record, field }`: take `record`'s slot list,
  pick the slice at the field's offset/count (computed from `record.ty`
  and `field`).
- `Pattern::Record` / `Pattern::Tuple`: destructure into N bindings,
  one per slot.

### Aggregate-producing control flow

When an `If` or `Match` returns a multi-slot type, **the construct is
duplicated per slot**. `if c then {a:1, b:2} else {a:3, b:4}` lowers
to two parallel `Match` expressions:

- slot 0 (`a`): `Match(c, True → 1, False → 3)`
- slot 1 (`b`): `Match(c, True → 2, False → 4)`

The condition `c` is duplicated. **Pure + total → semantically free**
(no observable difference). The performance cost (re-evaluating `c`)
is recovered by future CSE/GVN at the Core opt layer.

### Slot symbols and debug names

When AST→Core decomposes an aggregate binding (`let r = {x:1, y:2}`),
it mints fresh **slot symbols** (`r_x`, `r_y`) via the symbol table
and tracks them in a per-binding slot map:

```rust
locals: HashMap<SymbolId, Vec<SymbolId>>   // AST sym → slot syms
```

A parallel `slot_paths: HashMap<SymbolId, String>` records each slot
symbol's source-derived dotted path (`r.x`, `r.b.c`, `t.0`). The
SSA display reads this table — debug output shows `v17<r.b.c>`
instead of `v17`. Same table powers error messages.

### Why this shape

Records and tuples don't participate in algebraic rewriting — fusion
laws operate on `Cata`, `Map`, `Build`, `Match`, `Con`. Keeping
`Record`/`Tuple` as Core nodes would make every rewrite walk past
inert plumbing. By SROA-ing them away at AST→Core, the Core IR
matches its purpose exactly: every primitive has an algebraic
rewrite home, nothing inert.

The cost lives in AST→Core (slot tracking, decomposition, duplication
for control-flow). It's substantial but localized — one pass with one
author writing it once. Downstream Core code stays minimal.

This is sound specifically because Ori has **no aggregate identity** —
no pointer-takes, no record-by-reference equality, no FFI opacity,
no varargs. See `notes/language-properties.md`. In any language with
those features, this SROA would be unsound.

Note on the scalar/structural split: `BinOp` could be expressed as
`App(intrinsic_sym, [lhs, rhs])`, matching GHC's approach where primops
are functions with special `Id`s. We chose the dedicated node instead —
`App` then unambiguously means "call a user or library function," and
we avoid needing an intrinsic-symbol registry for what's ultimately
pass-through to SSA. The algebraic rewrite system doesn't see `BinOp`
at all.

Plus the supporting types: `VarId`, `FuncId`, `TagId`, `FieldId`,
`Literal`, `MatchArm { pattern, body }`, `Pattern { constructor, binders }`.

**Why each primitive earns its keep:**

- `Var`: trivially needed.
- `Lit`: scalar literals. Distinct from `Var` because no environment.
- `App`: first-order call. After lambda-lifting + mono, every call is
  to a known top-level function. We don't need `Lam` (GHC keeps it
  because they don't lambda-lift; we do, so we don't).
- `Let`: binding. Preserves binding structure for let-floating, CSE,
  dead-binding elimination.
- `Match`: non-recursive case analysis on tag unions. Distinct from
  `Cata` because not every case-of is a fold. Keeping them separate
  makes `case-of-case` and `case-of-known-constructor` syntactic.
- `Cata`: structural recursion. **Refinement vs the historical
  `Fold`**: make it the generic catamorphism, not list-specific. Then
  deforestation laws apply uniformly across inductive types (lists,
  trees, Maybe, user-defined).
- `Con`: tag-union constructor. Explicit, not folded into `App`.
  Critical for `case-of-known-constructor`: `Match(Con(tag, args),
  arms) → arms[tag][args]` is a syntactic rewrite, no analysis.
- `Record`: non-tagged aggregate. Distinct from `Con` because no tag,
  no pattern matching against alternatives.

**Every primitive maps to algebraic laws** — this is the test of
whether the IR is "right." A node without a rewrite home is dead
structure.

| Node | Associated law(s) |
|---|---|
| `Let` | let-floating, dead-let-elim, beta (let-substitution) |
| `App` | inlining, specialization on argument shape |
| `Match` | case-of-case, case-of-known-constructor, case-of-let-floating |
| `Cata` | shortcut deforestation, banana (combine catas over same data), inlining-driven fusion |
| `Con` | case-of-known-constructor (the dual) |
| `Record` | field projection elimination, record-update fusion |

**Convergence evidence:** the 6-8 primitive count is the local
optimum across proof-language compilers: GHC Core (6 + Cast/Type),
Idris 2 TT, Lean 4 compiler IR, Coq's reductive language. That
multiple independent compilers landed near this shape is signal.

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

## What we defer

- **e-graphs / equality saturation.** Our laws are mostly monotonic
  (fusion strictly improves cost), so fixpoint application of
  hand-rolled rules produces the same result as cost-based extraction.
  HN discourse (47717192, 41968831) is genuinely split on whether
  e-graphs earn their keep — pizlonator's "pass ordering isn't a
  source of sweat" is real data from a real compiler engineer.
  PurpleUpbeat2820's measurement (rewrites fire 2.3%, 28% benefit,
  most are mul/shift) suggests the value is moderate, not stunning.
  Decision: start hand-rolled. The signal to adopt egg is phase-
  ordering pain in practice (e.g., we end up with a Core-level
  `run_full_pipeline` calling `apply_rules` four times). Until then,
  hand-rolled is faster per-rule and easier to debug.

- **Effects / I/O.** We're pure today. If/when we add I/O, an
  effect-annotation on `App` (or separate `EffApp`) is the likely
  shape. The pure subset stays as-is.

- **Higher-rank polymorphism past mono.** Would need type abstractions
  in Core. We mono first, so this is moot for now.

## The empirical gate

PurpleUpbeat2820's measurement discipline applied to Ori: before
building the full optimizer, verify that fusion's ceiling on real
Ori code is meaningful. The first deliverable is therefore not
"complete Core" but a single end-to-end fusion case:

1. Build Core IR (minimal — enough for one program).
2. AST→Core lowering for that program.
3. **One rewrite rule**: `Cata(f, z, Map(g, xs)) → Cata(λacc x. f acc (g x), z, xs)`.
4. Core→SSA lowering.
5. Compile a tiny benchmark with and without the rule. Measure
   allocations + runtime.

If the gap is meaningful (≥2-3× on relevant cases), proceed with more
rules. If the gap is small, reassess — maybe FBIP + AST-level
`range.walk` fusion already capture most of the win, and the
infrastructure isn't worth it.

This gate is *part of the development plan*, not a precondition. It
just means we commit to enough infrastructure for one measurement,
not to the full optimizer up front.

## Reverts and corrections from prior work

- `21c4335` (stream_fuse rewrite) — reverted. SCEV-style work at the
  wrong layer.
- `8ed81c8` (stream_fuse detection) — reverted. Same.
- `c998631` (loops.rs) — **kept**. Independently useful for LICM,
  unrolling, codegen heuristics. The mistake was building stream_fuse
  on top of it, not the analysis itself.
- `CLAUDE.md` rule "all SSA→SSA equivalence-preserving rewrites belong
  in opt/" — **amended**. Add the qualifier "whose natural form is
  SSA." Algebraic rewrites belong at Core.

## Open questions

- **Stdlib marking story.** For fusion to fire, stdlib functions like
  `List.range`, `List.map`, `List.walk` need to be recognizable as
  `Cata` / `Build` / `Map`. How? Options: (a) annotate in source
  (`@cata`, `@build`), (b) recognize by name in the lowerer, (c) write
  these stdlib functions directly in Core. Probably (c) — stdlib is
  the bridge between user surface syntax and Core primitives.

- **Where does `loops.rs` get used?** It's currently unused. LICM is
  the obvious consumer once we have it. Codegen could use it for
  hot-loop heuristics. Worth keeping but not maintained beyond what
  consumers demand.

- **ANF before SSA?** Most likely yes — ANF naturalizes the SSA
  lowering (each subexpression names its intermediate). But this is a
  Core→ANF→SSA chain, not changing what Core is.

- **Cost of the rebuild.** Resurrecting Core is ~1 week of mechanical
  work. AST→Core lowering reuses inference + mono info. Core→SSA
  lowering is largely the existing lower (with the algebra layer
  removed). The risk isn't the build; it's whether the optimizer pays
  off on real workloads.

## Success criteria

If we get to a Core IR with 3-5 fusion rules and demonstrate on a
benchmark that `xs.map(f).walk(g)` compiles to a single zero-alloc
loop (within a small constant factor of hand-written C), the
architecture is validated. If we can't get there, the empirical gate
is doing its job — better to know than to keep building.

The longer-term goal: every optimization on the "DAG + total + pure"
list above is buildable as a Core pass in 50-200 lines. The Core
infrastructure pays for itself by the third or fourth pass.
