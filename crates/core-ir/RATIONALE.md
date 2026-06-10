# Why these variants?

This doc answers: given that Haskell's GHC Core gets by with six
core term variants, why does Ori Core have eleven? Are we
overweight, or do we have reasons?

The answer is **we have reasons specific to our goals**, and most
of the difference is forced by those goals. The "minimal IR" target
is meaningless without saying minimal *for what*.

## What Ori Core is for

Five goals drive every variant decision. Each one shows up in the
table below as a justification for at least one variant.

1. **Correctness by construction.** Totality (no infinite loops),
   purity (no hidden effects), strictness (deterministic order).
   The IR must not let you write a program that violates these,
   and it must preserve the structure that makes the guarantees
   provable.

2. **Algebraic rewrites on natural shapes.** Fusion, case-of-case,
   case-of-known-constructor, deforestation. Each operates on a
   syntactic shape: `Cata`, `Match`, `Con`. If those shapes are
   collapsed into a generic `App`, every rewrite has to recognize
   them by name or convention. The rewrites get tractable only
   when their target is a Core variant.

3. **Perceus refcounting + FBIP.** The runtime model is
   Perceus-style precise RC; mutating primitives reuse the buffer
   when `rc == 1` (cow_*). The IR must mark mutation sites
   syntactically — otherwise the SSA layer is reconstructing FBIP
   intent from alloc+store sequences.

4. **No boxing by default.** Records and tuples are SROA-ed at
   AST→Core. The IR doesn't have `Record` or `Tuple` variants;
   aggregates flow as parallel slot lists. Sound because Ori has
   no aggregate identity (no pointer-take, no by-ref equality).

5. **Competitive with C.** Scalar ops compile to single
   instructions, not function calls. Buffer indexing is direct
   memory access after bounds-elimination. Loops are loops, not
   recursive calls. The IR doesn't introduce overhead that would
   need to be optimized away.

Three of these (1, 2, 3) push *toward* having more variants — they
need syntactic distinctions. Two (4, 5) push *away* — they want
the IR to not impose layout or dispatch overhead.

The eleven variants are what these forces balance to.

## Reference points

Comparing variant counts in isolation is misleading because each
compiler's IR makes different choices about what to bake in:

- **GHC Core (Haskell).** ~6 term variants: `Var`, `Lit`, `App`,
  `Lam`, `Let`, `Case`. Plus type-system machinery: `Cast`,
  `Type`, `Coercion`, `Tick`. GHC has general recursion, laziness,
  and IO; mutation goes through `IORef` / `ByteArray#` primops at
  the surface, not Core variants. Records exist as datatypes, not
  a dedicated Core node.

- **MLton SSA / SXML.** SXML (an A-normal-ish IR) has ~10
  expression forms: `Var`, `Const`, `App`, `Case`, `Con`,
  `Handle`, `Let`, `PrimApp`, `Profile`, `Raise`. MLton has
  effects (refs, exceptions, IO), no laziness, whole-program
  defunctionalized.

- **Idris 2 TT.** Even more variants — pattern-matching is a
  dedicated form, types are first-class, dependent types push the
  variant count up.

- **Lean 4 IR.** Several layers; the lowest pre-codegen IR has
  ~8-10 forms including explicit `Reuse` / `Reset` for in-place
  mutation analogous to our FBIP intent.

So six variants (GHC) is the floor for "pure functional lazy with
runtime-mediated mutation." Eleven (Ori) is in line with strict
languages that surface mutation intent (Lean has a similar count
for similar reasons).

## What each variant earns

For each Core variant, the table below names which goal demands it
and what would happen without it.

| Variant     | Serves                          | What we'd lose without it                                                                                                                                                                |
| ----------- | ------------------------------- | -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Var`       | All                             | Can't reference bindings. Nothing.                                                                                                                                                       |
| `Lit`       | Goal 5                          | Scalar constants would have to be one-off `App`s; pretty-print becomes opaque; constant folding loses its primary input shape.                                                            |
| `App`       | All                             | Can't call functions. Foundational.                                                                                                                                                      |
| `Let`       | Goal 2                          | Binding scope disappears. Either inline everything (code explosion) or thread environments through `App` arguments. Let-floating and dead-binding elimination need it as a syntactic target. |
| `Match`     | Goals 1, 2                      | Could collapse into `App` to a synth dispatch function, but case-of-case and case-of-known-constructor stop being syntactic. Every rewrite that targets a tag-union case has to recognize it by name. Loses the totality invariant that every case is exhaustive. |
| `Cata`      | Goals 1, 2                      | Could be a `Call` to `__fold_N`. The recursive helper is still there. But "this is structural recursion" becomes a name-recognition exercise. Fusion (the central algebraic rewrite) loses its primary target. Totality stays guaranteed (the helper is still total) but the *structure that makes fusion easy* is gone. |
| `Con`       | Goals 1, 2                      | Could be `App` to a constructor function. Case-of-known-constructor stops being syntactic — every rewrite has to know "this App target is actually a constructor" via the symbol table. Loses the syntactic distinction between calls and value construction. |
| `BufLit`    | Goal 5                          | Could desugar to chained `BufAppend` from empty. Cost: every literal pays `cap == 0 → resize → store` per element instead of one alloc + N stores. The literal `[1, 2, 3]` becomes three allocations.                                                                                |
| `BufLoad`   | Goals 1, 5                      | Could be a stdlib method call. Pays per-load function-call overhead; loses the syntactic shape that bounds-elimination would match on. The bounds check itself is required (Goal 1); the *primitive* lets it be elided when the index is provably in range. |
| `BufAppend` | Goal 3                          | Without it, FBIP intent is lost. The SSA layer would have to recover "this alloc-then-write-then-overwrite-old-binding pattern is a mutation site" by alias analysis. The primitive's mere existence is a syntactic flag that this slot wants `cow_resize_dyn`. **Load-bearing** for the runtime model. |
| `BufSet`    | Goal 3                          | Same FBIP rationale as `BufAppend`. Without it, `xs.set(i, y)` looks like alloc + copy + store at SSA, with no way to know it should reuse.                                                                                                                                            |

Three variants are arguably "could go either way": `Match`, `Cata`,
and `Con` could each collapse into `App` with a recognition
convention. The reason they don't is goal #2 — syntactic rewrites.
The cost of recognition-by-convention is paid by every rewrite
rule, every time, forever; the cost of three distinct variants is
paid once in the IR definition and shows up in walkers.

Three variants are *strictly* load-bearing: `BufAppend`, `BufSet`
(FBIP intent) and `Cata` (the only iteration primitive, since
source-defining a fold would be circular without general
recursion). If we removed any of these, the IR couldn't express
something the language semantics require.

## What we deliberately don't have

Five variants from other functional IRs are deliberately absent
from Core. The absence is as load-bearing as the presence — each
one is a choice that flows from the goals.

**`Lam`** (lambda abstraction). GHC keeps it because it doesn't
lambda-lift. We lambda-lift in the front-end; every closure becomes
a top-level `FuncDef` + a `Con` over a synthesized closure tag
union. Higher-order function calls go through `App(__apply_K,
[closure, ...args])`. Without `Lam`, Core's call shape is uniform —
everything's an `App` to a known top-level target.

**`Record` / `Tuple`.** SROA-ed at AST→Core. A `Record { x: 1, y: 2 }`
becomes two parallel Core `Expr`s; `FieldAccess` becomes a slice
into the slot list. Sound because of goal #4 (no aggregate
identity) — no source program can observe the difference between
a record value and the parallel sequence of its fields. Without
this, every algebraic rewrite would have to step past inert
record-construction and field-projection nodes that contribute
nothing algebraically.

**`Cast` / `Coercion` / `Type` (as a value).** GHC needs these
because System F has explicit type abstractions and coercions
move them around. Ori is post-mono before Core — all type
abstractions are gone, all coercions resolved. No surface for
these to live in.

**`Lit::Str`** (string literal). `Str ≡ List(U8)` is a transparent
alias at the type level. A string literal at Core is a `BufLit`
of byte-typed `Lit::Int`s. No separate string variant; no separate
runtime representation.

**`BinOp` / `Cast` / `Range`** (as Core variants). Earlier
iterations had these. They're now `App` to builtin SymbolIds that
the lowering layer dispatches inline. Three variants gone for one
unified mental model: "a primitive is a function the CPU handles
directly, with no body in the module." Arithmetic and user-defined
methods go through the same `App` shape.

**`Dup` / `Drop` / `Reuse`** (explicit RC operations). Perceus
inserts these in its source calculus. Ori keeps them implicit —
the SSA layer derives them from linearity of the Core tree. The
analyses that need explicit ownership info (uniqueness, borrow,
reuse fusion) live at Core and produce annotations, not IR nodes.
Adding `Dup`/`Drop` as variants would pollute every algebraic
rewrite with bookkeeping for no algebraic benefit.

## The principle

> An IR variant earns its keep when:
>
> 1. It can't be source-defined without circularity (`Cata`), **or**
> 2. It's load-bearing for a runtime invariant the IR can't
>    otherwise express (`BufAppend`, `BufSet`), **or**
> 3. An algebraic rewrite matches on its shape (`Match`, `Con`).
>
> Everything else is an `App` to a known target, or doesn't exist.

This is the test that produced today's variant set. Every variant
in `expr.rs` passes at least one of the three conditions. Removing
any one would either (a) require a downstream analysis to recover
what was lost, or (b) make a class of rewrites recognize-by-
convention rather than recognize-by-shape.

The eleven variants are minimal *for Ori's goals*. They are not
minimal for "any pure functional IR" — that's GHC Core's six, and
Ori would have to give up either fusion-as-syntactic-rewrite or
FBIP to reach it.

## What this means for v1

Two implications for the prototype in this crate:

- **Don't shrink the variant set below eleven unless a goal
  changes.** Each variant has a specific rewrite or runtime
  invariant it carries. Collapsing without changing what we want
  the IR to do means trading one form of complexity (variant
  count) for another (recognition-by-convention).

- **Do shrink the *fields* on the variants we have where derivation
  is possible.** The existing implementation stores derived data
  (`Con.field_slot_counts`) because the polymorphic-`Con.ty` trap
  blocks derivation. V1's chance to fix that trap upstream and
  drop the field. Same opportunity for `Match.scrutinee_slots` and
  `MatchArm.body` (pre-decomposed `Vec<Expr>` that lowering could
  expand from a single `Expr`).

The variant set is settled. The variant *shape* is what v1 gets
to revisit.
