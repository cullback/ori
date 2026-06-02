# Language properties → compiler simplifications

What Ori's language design buys the compiler. Each property removes a
class of complexity that mainstream optimizing compilers spend
significant engineering to handle.

This is a reference for "should we build X?" decisions — if X is solved
free by a language property, don't build it; if X is unsound in the
general case but sound in ours, the property is why.

Cross-references: `notes/core-ir.md` (the algebraic IR these properties
unlock), `CLAUDE.md` (the three-paradigm layer split).

## The properties

| Property | Source |
|---|---|
| **Total** (System T) | No general recursion. Structural recursion via `fold` over inductive types only. Termination guaranteed by construction. |
| **Pure** | No side effects in expressions. No mutation in source. |
| **Strict** | Left-to-right evaluation. No laziness, no thunks. |
| **Monomorphic** | Mono runs ahead of all post-frontend passes; polymorphism is fully erased by the time anything optimizes. |
| **Lambda-lifted** | Every `Call` at IR time targets a known top-level function. Defunctionalization eliminates higher-order indirection. |
| **DAG call graph** | No mutual recursion. Self-loops only (from structural recursion in `fold`-lifted helpers). |
| **No aggregate identity** | No pointer-takes, no record/tuple equality by reference, no FFI boundaries that observe pointer values, no varargs, no dynamic dispatch on aggregate shape. |
| **Closed structural types** | Tag unions are structural; by mono time every union is closed. Records are structural; by mono time field sets are concrete. |

## What each property removes from the compiler

### Total

- **Termination preserved by every rewrite, unconditionally.** GHC has
  to argue `⊥`-safety for each transformation. We don't.
- **Compile-time evaluation terminates trivially.** Closed terms
  reduce in bounded time, so we can pre-execute `length [1,2,3]`,
  `map f (range 0 10)`, anywhere in the program. Generalized
  constant folding becomes "interpret a sub-tree."
- **Fusion laws hold without side conditions.** `foldr f z (build g) = g f z`,
  `cata f . cata g = ...` — all universal, no per-rewrite proof
  obligation.
- **Hylomorphism deforestation works fully:** `cata f ∘ ana g = hylo f g`
  eliminates the intermediate inductive structure entirely. The
  totality assumption is exactly what makes the law sound.

### Pure

- **Memoization is sound** at compile time (precompute) and runtime
  (cache).
- **CSE doesn't need alias analysis** — two textually-identical
  expressions produce the same value, end of story.
- **Dead-binding elimination doesn't need effect analysis.** `let x = e`
  with `x` unused: drop `e` unconditionally.
- **Reordering / speculative evaluation is free.** The compiler can
  evaluate any pure subterm at any time without changing semantics.
- **No "effect ordering" passes.** GCC/LLVM spend real machinery
  modeling read/write/atomic ordering of side effects. We don't have
  side effects.

### Strict

- **Trip counts are known when the data is known.** A `Fold` over a
  list of length N runs N iterations. No "what if this fold gets
  forced under WHNF" analysis. SCEV-grade work just isn't needed.
- **Evaluation order is a property of the source.** Optimizations
  don't have to preserve a particular thunk-forcing order; they only
  have to preserve value equivalence.

### Monomorphic

- **No virtual dispatch.** All calls statically resolved. The
  `lambda::narrow` pass already exploits this.
- **No type-class dictionaries.** Type-class machinery has been fully
  resolved into specialized calls.
- **No generics-erasure performance cliffs.** Java's `List<Integer>`
  vs `int[]` distinction doesn't exist; everything specialized.

### Lambda-lifted

- **Every `Call` has a known target.** Inlining is purely syntactic
  substitution; no virtual-dispatch resolution needed.
- **Closures are tagged enum values after defunc.** Their dispatch is
  visible to `Match` and to call-site specialization.
- **No escape-analysis machinery for closures.** Captures are
  inspected statically.

### DAG call graph

- **Single-pass bottom-up optimization across the call graph.**
  Topo-sort callees first. By the time you process `f`, every
  callee is at its optimized form. No iterative call-graph
  fixpoint.
- **Inlining is bounded.** Inline in topological order without
  cycle-checks. `opt/inline.rs::cyclic_functions` is currently a
  safety check; in Ori it's always empty.
- **Whole-program specialization is bounded.** At most
  `callsites_of_f × shapes` specialized variants per function.
- **Interprocedural escape analysis = finite DAG walk.** No fixpoint
  over the graph.
- **Cross-function CSE is sound and tractable.** Inline first, then
  dedupe.

### Structural fold-only iteration

- **Tail-call optimization isn't a pass.** Folds *are* loops; lower
  emits them as such directly. No "detect TCO pattern" machinery.
- **Trip count is syntactic.** The fold's target's length / depth
  IS the trip count.
- **Static unrolling over known-shape data:**
  `Fold f z [a,b,c]` reduces to `f(f(f(z,a),b),c)` at compile time —
  no loop emitted at all.
- **Loop fusion laws are universal**, not heuristic.

### No aggregate identity

This is the property that unlocks the **decomposed-aggregates** thesis
in `CLAUDE.md`. Most languages can't SROA aggressively because:
- C structs: `&s` takes an address, escapes opacity required.
- Java objects: `==` compares references.
- Python: `is` compares identity.
- Rust: trait objects + `Any` allow dynamic dispatch on values.
- Most languages: FFI sees pointers with expected layouts.

Ori has none of these. **An aggregate's only observable semantics are
its field values.** Therefore:

- **Aggregates are always decomposable.** Records, tuples, single-variant
  unions emit parallel SSA Values with no heap object.
- **Memory layout is a convention enforced by store/load offsets**, not
  by an aggregate-as-single-Value in SSA.
- **The "aggregate" exists only at the type level and at the layout
  level.** It doesn't need to exist as an SSA node, an IR node, or a
  runtime descriptor.
- **Field access is a slot pick, not a load.** When the record is in
  registers, `r.x` is just the x-th parallel Value.
- **Memcpy is a codegen peephole**, not a semantic operation —
  recognize "N consecutive Stores with known constant offsets to the
  same buffer" and fuse into bulk-store.

This is *the* superpower of the design at the lower layer.

### Closed structural types

- **No row-polymorphism residue at lower time.** Every record has a
  concrete field list; every tag union has a concrete variant list.
- **Tag indices are deterministic** (alphabetical sort of structural
  variants, declaration order for named ones).
- **Pattern exhaustiveness is decidable at compile time** — every
  union's variants are known.

## Cross-cutting implications

### What we never need

| Mainstream compiler thing | Why Ori doesn't need it |
|---|---|
| **SCEV** (scalar evolution / loop induction analysis) | Folds carry the induction variable as a binding in the step function; trip count is syntactic. |
| **Alias analysis** for optimization | Purity removes write-aliasing concerns. |
| **Escape analysis as a separate pass** | DAG call graph + finite uses → bounded by use-def walk. |
| **Strictness analysis** | We're strict by default. |
| **`⊥`-safety arguments for rewrites** | Totality removes nontermination as a side condition. |
| **Virtual dispatch resolution / devirt** | Lambda-lifted + monomorphic. |
| **Polymorphism erasure / dictionary passing at IR time** | Mono runs ahead. |
| **Generational / interprocedural fixpoints** | DAG call graph means single-pass bottom-up. |
| **Iterative analysis over the call graph** | DAG. |
| **Phase-ordering scheduler** for rewrites | Most fusion laws are monotonic (each rewrite improves cost); fixpoint application reaches the optimum. |
| **Pointer-aware SROA** | No pointers escape, ever. |
| **Conservative aliasing for memcpy** | Memory writes are syntactically known sequences. |

### What we still need (because they're target-level)

- **Register allocation** (the SSA Values have to land somewhere)
- **Instruction selection** (peephole choice of which machine op)
- **Branch displacement / layout** (PC-relative offsets)
- **Calling convention / ABI lowering** (whose registers, whose stack)
- **Bit-pattern reasoning** for narrow types (`KnownZeroHigh`)

These aren't language-level; they exist because the *machine* has
constraints (registers, instruction encodings) that no source-language
property can eliminate.

## How this shapes IR design

(See `notes/core-ir.md` for the long form.)

1. **Three rewriting paradigms, three layers**:
   - `passes/core/` for algebraic rewrites (fusion, beta, eta,
     case-of-case, banana, free theorems)
   - `src/opt/` for scalar dataflow (const-fold, branch-fold, DCE, GVN)
   - `src/lower/` for declarative resource discipline (FBIP, RC,
     decomposition)
   - Each at the level where its information is visible.

2. **Core IR is small.** Eight structural primitives + one scalar
   (`BinOp`). Every primitive has an algebraic rewrite home.

3. **Aggregates exist as IR nodes at AST and Core, decompose at
   Core→SSA**, then live as parallel Values + memory-layout convention.

4. **Fusion is unconditional** — no per-rewrite soundness proof.

5. **Optimization passes can be type-agnostic at SSA**, since by then
   the structural distinctions are gone.

## When to revisit this note

When considering adding any of: an escape analyzer, an alias analyzer,
SCEV, a `⊥`-safety argument, a phase-ordering scheduler, a generic
type-erasure shim. Each is something Ori's design says shouldn't be
needed — if you find you need it, either the design has slipped (a
new feature broke a property) or the optimization is being done at
the wrong layer.

## Open questions

- **What other free-theorem rewrites do we want to encode?**
  `length . map f = length`, `id . f = f`, `map id = id`, are obvious;
  there are probably ~10-20 more worth having.
- **Where does the codegen-side memcpy peephole live?** Probably
  `src/codegen/aarch64/select.rs` once we encounter "N consecutive
  Stores at constant offsets" in real generated code.
- **Recursive types (Lists, Trees) — when do they break decomposed
  aggregates?** They don't (the payload bundle is the variant fields;
  list-of-record is record-fields-laid-out-in-list-slot), but the
  exact boundary is worth examining as we add larger inductive types.
