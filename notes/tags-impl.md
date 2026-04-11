# Structural tag unions — implementation plan

Companion to `tempo-notes/gold/tags.md`, which specifies the
user-visible language feature. This document answers the
implementation-level questions that the language note leaves open
and stages the work so it can be picked up across sessions.

## Goal

Every tag union in an Ori program is a structural type: constructors
like `Red`, `Ok(x)`, `None` don't need to be declared before use.
Inference builds an open tag row from usage, closes it at function
boundaries and match exhaustiveness, and monomorphization specializes
each closed row to a concrete layout. At runtime, non-recursive tag
unions are stack-allocated and laid out with per-specialization
discriminants so that `[None, Some(T)]` has the same representation
as Rust's `Option<T>`.

## Design decisions (answers to the note's open questions)

### 1. Runtime tag representation

Per-specialization dense indices, assigned at layout-selection time.
No global tag interner.

Consequence: the compiler chooses the discriminant width per closed
union. A 2-tag union uses a 1-bit tag (or niche), a 200-tag union
uses a u8. Tag `Red` in `[Red, Green]` has a different runtime value
from tag `Red` in `[Red, Green, Blue]`, because they live in
different types.

### 2. Monomorphization keys

Mono's existing `(SymbolId, Vec<Type>)` key is extended so that
`Type::TagUnion { tags, rest }` normalizes identically to records:
- `rest` must be closed (None) — open rows never reach mono
- `tags` are sorted by tag name for canonical ordering
- Payload types inside tags are recursively normalized

Two call sites with the same normalized closed tag row share a
specialization; different rows produce different specializations.

### 3. Closure rules in inference

Closure happens in three places:

- **Match exhaustiveness.** When a match covers every tag in an open
  row, the row closes. If the match has fewer tags and no default,
  it's a type error ("non-exhaustive match on closed union").
- **Type annotation.** `foo : Str -> Color` closes `foo`'s inferred
  open row to `Color`'s tag set. Annotations are closure points.
- **Function boundaries (generalization).** At let-generalization,
  an open row on a function's inferred type is closed to exactly the
  tags it mentioned, unless the row variable is generalized (row
  polymorphism through the call graph, like record rows).

At call sites, widening follows OCaml-polyvariant semantics:
`f : [Red, Green] -> I64` called with a `Red` value works (the
narrower inferred type flows into the wider expected type); `f`
called with a `Blue` value is a type error.

### 4. Payload type unification

`Red(I64)` and `Red(Str)` fail to unify. Tag names are structural
but payload types are nominal — the same tag name with different
payload types is two different constructors that happen to collide.
The error message: "tag `Red` has payload type `I64` here but `Str`
there."

`Red(I64)` and `Red` (nullary) also fail to unify. A tag's arity is
part of its identity.

### 5. Interaction with `Result(a, err)`

`Result(a, err) : [Ok(a), Err(err)]` becomes a transparent alias. In
the new system it's defined in the standard library as a type alias
(`:`), not a built-in. The `?` operator desugars to an inline match
that propagates the `Err` case by returning from the enclosing
function; the enclosing function's error row grows to include the
propagated tag. This is the error-composition story in the language
note, implemented via row polymorphism.

### 6. Migration of existing nominal types

Today's `Color : [Red, Green, Blue]` is an opaque-ish declaration
that registers `Red`, `Green`, `Blue` as global constructor names.
In the new system:

- `:` (alias) becomes a transparent alias for the structural tag
  union — `Color` and `[Red, Green, Blue]` are interchangeable types.
- `:=` (transparent nominal) creates a distinct type whose internals
  are visible. `Shape := [Circle, Rect]` behaves like the current
  nominal declaration.
- `::` (opaque nominal) creates a distinct type whose internals are
  hidden outside the `.()` block.

The existing `TagDecl` machinery and `decl_info::register_tag_union`
are repurposed: for `:=` and `::` declarations, they still register
the tags as belonging to the nominal type; for `:`, the tags are
registered as pure structural aliases.

### 7. Exhaustiveness diagnostics

First pass: be conservative. Every match on a closed union must
cover every tag, or have an explicit `else`. Error message points at
the match site and lists the missing tags.

Later: warnings for redundant arms, smart fix-it suggestions for
common mistakes. Not v1.

### 8. The `?` operator

Out of scope for this implementation. Track it as a separate feature
that builds on structural tags. Tag unions must land first.

### 9. Interaction with existing passes

- `flatten_patterns`: no change needed. The pass works on pattern
  shapes, not on tag-union row types.
- `mono`: extend `normalize_type` to handle `Type::TagUnion` like it
  handles `Type::Record`.
- `defunc`: no change. Lambdas and closures don't touch tag types.
- `reachable::prune`: no change.
- `decl_info`: constructor registration is reworked to handle
  structural tags — every tag-name occurrence in a type expression
  contributes to the global constructor scheme table.
- `ssa::lower`: layout per specialization is new; fetched from a new
  `Layout` table populated by the layout selection pass.

## 10-step implementation plan

Each step lands as its own commit with passing tests. Steps are
ordered so the codebase stays compilable and test-green throughout.

### Step 1 — `Type::TagUnion` variant (engine-only)

Add `Type::TagUnion { tags: Vec<(String, Vec<Type>)>, rest: Option<Box<Type>> }`
to `src/types/engine.rs`. Update `map_children`, `occurs_in`,
`collect_free_vars`, `display_type` to handle it. **No** integration
with inference, resolution, or the rest of the pipeline yet — the
variant exists but no code constructs it.

Unit tests inside engine.rs exercise the new variant's traversal.
Rest of the codebase compiles because no `match Type` statement sees
it (at this stage, the only consumer is the engine itself).

### Step 2 — Tag-union unification

Add `unify_tag_unions` symmetric to `unify_records`. Wire it into
`unify()`. Unit tests: common tags same payloads, open + closed,
open + open merge, closed + closed exact match, closed + closed
mismatch error, payload-type mismatch error.

### Step 3 — Consumer boilerplate

Every exhaustive match on `Type` in the codebase gets a `TagUnion`
case, most of which are `unreachable!()` or structural-recurse
stubs. Affected files: `ast.rs`, `ast_display.rs`, `infer.rs`,
`mono.rs`, `decl_info.rs`, `flatten_patterns.rs`, `ssa/lower.rs`.

At this point the whole test suite still passes because no
inference code produces a `Type::TagUnion` — the stubs are never
reached at runtime.

### Step 4 — Inference: bare constructor references produce open rows

In `infer_expr_inner`, when resolving `ExprKind::Name(sym)` or
`ExprKind::Call { target, args }` where the symbol is a constructor,
produce a `Type::TagUnion { tags: [(con_name, arg_types)], rest: Some(fresh_var) }`
with a fresh row variable.

Pattern matching on an `Is` expression or match arm against a tag
closes its row to exactly the covered tags (or flows them into an
open row if `else` is present).

This is the biggest step. At the end of it, the user's example
(`a = |text| if text == "red" then Red else Green`) should infer
`Str -> [Red, Green]`.

### Step 5 — Structural constructor registration

Today's `decl_info::constructors` is populated by walking
`TypeAnno` declarations. Extend it: walk every type expression in
the module looking for constructor references, and populate a
secondary table of "structural constructors" whose schemes are
derived from their usage context. Named `TagDecl` constructors
continue to take precedence.

### Step 6 — Inference closure rules

Match exhaustiveness closes rows. Type annotations close rows.
Function-boundary generalization decides whether a row is closed or
kept polymorphic (analog to record row polymorphism at let
boundaries).

Error messages for non-exhaustive matches on closed unions.

### Step 7 — Mono: tag-row normalization and specialization

Extend mono's specialization key to include normalized closed tag
rows. Extend `normalize_type` to sort tags and recursively normalize
payloads. Mono now produces multiple specializations for functions
called with different tag row closures.

### Step 8 — Layout selection pass

New pass between mono and `ssa::lower`. Walks every concrete type
in the monomorphized module and assigns a `Layout` per unique
normalized type. Initial layouts:

- Single-variant (regardless of payload): unwrap to payload
- All-zero-payload, N ≤ 256: u8 discriminant only
- Mixed payload, discriminant only: tag + max(payload)
- Niche (deferred): detect unused bit patterns in payload

Produces a `LayoutTable: HashMap<NormalizedType, Layout>` consumed
by lowering.

### Step 9 — SSA lowering uses LayoutTable

`ssa::lower`'s constructor emission and match compilation read from
the new `LayoutTable` instead of hardcoding tag index 0 at slot 0.
Different specializations of the same function now emit different
loads/stores based on their layout.

Match compilation for closed exhaustive unions drops the
else-fallthrough block.

### Step 10 — Migration of existing programs

Sweep through `programs/`, `standard/`, and test programs to make
sure everything still works under the new semantics. Update
`notes/compiler-phases.md` to include the layout pass. Regenerate
snapshots that might have type-display changes.

## Staging notes

- **Steps 1–3 are foundational but behaviorally inert.** They add
  infrastructure without changing what the compiler does. Land them
  as quickly as possible to get the codebase ready.
- **Step 4 is the big one.** It changes observable inference
  behavior. Test it against the user's example first, then the
  existing nominal declarations.
- **Steps 5–7 need to land together.** Once inference produces
  structural rows, mono and decl_info must be ready to consume them.
  Don't leave a half-state where inference produces rows that mono
  panics on.
- **Step 8 is isolated.** It's a pure function from concrete types
  to layouts. Easy to test in isolation.
- **Step 9 is where bugs hide.** SSA changes have to match the
  layout decisions exactly. Test with exhaustive programs.
- **Step 10 is cleanup.** Budget a half-day for snapshot
  regeneration and rough edges.

Rough LOC estimate: **1400–1800 lines added, 300–500 modified**.

## Open questions that will show up during implementation

These aren't blockers — they're the kinds of things that will come
up and need small design decisions on the fly:

- How does generalization handle row variables? Let-polymorphism on
  tag rows works the same as record rows, but the interaction with
  `infer_func_body`'s self-registration trick needs verification.
- When an `Is` expression with an unknown-row scrutinee matches
  against `Ok(x)`, does it narrow the scrutinee's type, or does it
  produce a fresh row? Probably narrow (OCaml semantics).
- What's the behavior of `if x is Red then ... else ...` when `x`
  has an open row? The `else` branch sees `x`'s row minus `Red` —
  which is another open row. Needs `negative` row handling, or the
  simpler answer "else branch re-opens the row." Simpler first.
- Layout niche detection is recursively defined: `[None, Some([None, Some(T)])]`
  can niche both levels. First pass can skip recursive niches and
  just do the shallow case; recursion is a follow-up optimization.

## Not in v1

- Niche optimizations beyond the shallow case (null pointers,
  NonZero).
- Exhaustiveness warnings for redundant arms.
- Row polymorphism at function boundaries (all rows close at
  function signatures in v1; polymorphism follows later).
- The `?` operator.
- Separate-compilation-friendly mono (Ori is whole-program today).
