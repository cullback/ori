# Tags

Tag unions are Ori's sum types — values that can be one of several variants.

## Tag unions

Tags are values. You don't need to declare them — just use them:

```ruby
color = Red
result = Ok(42)
```

The compiler infers the type as an open tag union — `Red` has type `[Red, ..]`, meaning "a union containing at least `Red`, and possibly other tags." This is what makes error handling compose naturally — each function declares only the error tags it can produce, and the error type grows as you chain operations:

```ruby
parse : Str -> Result(I32, [ParseErr(Str)])
validate : I32 -> Result(I32, [ValidationErr(Str)])

# Combined error type is the union of both:
#   Result(I32, [ParseErr(Str), ValidationErr(Str)])
```

No `map_err` or error type conversion needed — the `err` type parameter is an open tag union that grows to include all error tags that could flow through. See [functions](functions.md#error-propagation-with-) for the `?` operator that makes this work in practice.

### When unions close

Tag unions close in three situations:

1. **Exhaustive matching** — when you cover all cases, the compiler knows the full set:

```ruby
# Compiler infers color : [Red, Green, Blue] (closed)
if color
    : Red then "#FF0000"
    : Green then "#00FF00"
    : Blue then "#0000FF"
```

2. **Type annotation** — explicitly naming a closed union:

```ruby
Color : [Red, Green, Blue]

color : Color
color = Red  # open union closes to Color
```

3. **Code generation** — open rows are a *compile-time-only* phenomenon.
   By the time a program reaches code generation, every tag union has
   been closed to a concrete set of tags, either via inference closure
   at function boundaries or via monomorphization at call sites. This
   is what makes the performance story work — see [performance](#performance).

### Open unions in type annotations

Use `..` to write an open union in a type annotation — "at least these tags, possibly more":

```ruby
# Accepts any union containing Ok — error tags don't matter
unwrap : Result(a, [..]) -> a
unwrap = |result|
    if result is Ok(val) then val
    else crash("unwrap called on non-Ok")
```

Without `..`, the annotation is closed and the compiler enforces exhaustive coverage.

### Tag payloads

Constructors are functions — tag payloads use function call syntax:

```ruby
Circle(5.0)
Rgb(255, 128, 0)
Cons(1, Cons(2, Nil))
```

For named fields, pass a record:

```ruby
Event : [Click({ x: F64, y: F64 }), KeyPress({ key: Str, shift: Bool })]

if event
    : Click({ x, y }) then handle_click(x, y)
    : KeyPress({ key, .. }) then handle_key(key)
```

### Passing constructors as functions

Because constructors are functions, they can be passed directly to
higher-order functions without wrapping in an explicit lambda:

```ruby
# Wrap every element in Ok, producing a list of Result values.
wrap_all : List(I64) -> List(Result(I64, [ParseErr]))
wrap_all = |xs| List.map(xs, Ok)

# Pair corresponding elements of two lists. `Pair` doesn't need
# to be declared anywhere — a structural tag works just as well.
zip : List(a), List(b) -> List([Pair(a, b)])
zip = |xs, ys| List.map2(xs, ys, Pair)
```

This works uniformly for declared constructors (`Ok`, `Err`, or
any variant of a `:` / `:=` / `::` declaration) and for structural
tags used on the fly. The compiler infers the constructor's arity
from the expected argument type at the call site, the same way it
infers any other polymorphic function instantiation.

In a context that doesn't expect a function, a bare constructor
name still refers to its nullary-value form. So:

```ruby
color = Red              # the value [Red, ..] — nothing to apply
f = Pair                 # the value [Pair, ..] — not a function
# f(1, 2)                # COMPILE ERROR — [Pair] isn't callable
```

The rule: if the surrounding context expects a function, the
constructor becomes one; otherwise it's a value. There's no order-
dependent inference and no ambiguity — every reference decides
locally based on its immediate usage.

If you want to bind a constructor to a name for later use as a
function, wrap it explicitly:

```ruby
make_pair = |a, b| Pair(a, b)    # named function value
```

### Tag identity

A tag is identified by its name together with its payload shape.
Two occurrences of the same name with different arities or
different payload types are different constructors — they don't
unify. This can happen across a program:

```ruby
# Two unrelated uses of `Pair`. Each works in its own context.
single = Pair(1)         # type: [Pair(I64), ..]
both = Pair(1, "hello")  # type: [Pair(I64, Str), ..]
```

Both lines compile because the two tag union types never meet.
But as soon as they would — for example, as elements of the same
list — unification would try to reconcile them and fail:

```ruby
# bad = [Pair(1), Pair(1, "hello")]   # COMPILE ERROR
# tag `Pair` has 1 payload here but 2 there
```

Within a single tag union type, a tag name appears at most once,
and every occurrence must agree on payload shape. If you need two
variants with the same conceptual meaning but different data,
give them distinct names (`PairInt`, `PairStr`) or wrap the
differing data in a discriminator.

## Type declarations

```ruby
Color : [Red, Green, Blue]      # alias — just a name for an existing type
Color := [Red, Green, Blue]     # transparent nominal — internals exposed
Color :: [Red, Green, Blue]     # opaque nominal — internals hidden outside .() block
```

Mnemonic: `:` means "is", `:=` means "is defined as" (you see the definition — transparent), `::` means "has type" (you see the interface, not the definition — opaque). The `=` is the definition; removing it hides the internals.

| | Syntax | Distinct type? | Internals visible? | `.()` block? |
|---|---|---|---|---|
| Alias | `:` | no | yes | no |
| Transparent | `:=` | **yes** | yes | **yes** |
| Opaque | `::` | **yes** | **inside `.()` block only** | **yes** |

Nominal and opaque types can attach methods in a `.( )` block, which defines [dot dispatch](methods.md):

```ruby
Color := [Red, Green, Blue].(
    to_hex : Color -> Str
    to_hex = |color|
        if color
            : Red then "#FF0000"
            : Green then "#00FF00"
            : Blue then "#0000FF"

    equals : _
    hash : _
)
```

## Constructor access

Transparent nominal types use context-based construction — bare values (tags, records, tuples) unify with the nominal type when the context expects it. No special wrapping syntax is needed. This applies uniformly to all transparent nominal types: [tags](#transparent-nominal-types), [records](records.md#nominal-and-opaque-records), and [tuples](tuples.md#nominal-and-opaque-tuples). Opaque types hide construction outside the `.( )` block — only the public API can produce values.

How you construct and access tag values depends on the type declaration:

**Alias** — tags are plain structural values. No namespacing, no prefix:

```ruby
Color : [Red, Green, Blue]

color = Red                        # just use it
colors = [Red, Green, Blue]
```

**Transparent nominal** — constructors go through the type name:

```ruby
Shape := [Circle(F64), Rect(F64, F64)].(
    area : Shape -> F64
    area = |shape|
        if shape
            : Circle(r) then 3.14 * r * r
            : Rect(w, h) then w * h
)

my_shape = Shape.Circle(5.0)
two_by_three = Shape.Rect(2.0, 3.0)
```

From another module:

```ruby
import shape exposing [Shape]

my_shape = Shape.Circle(5.0)       # constructor through the type
area = Shape.area(my_shape)        # method through the type

# Type context also works — bare tag unifies with Shape
make_circle : F64 -> Shape
make_circle = |r| Circle(r)
```

**Opaque** — inside the `.( )` block, the type is transparent. Outside — even in the same module — only the public API is available:

```ruby
# color.rb
exports [Color]

Color :: [Red, Green, Blue].(
    to_hex : Color -> Str
    to_hex = |color|
        if color
            : Red then "#FF0000"
            : Green then "#00FF00"
            : Blue then "#0000FF"
)

# Same module, outside the block — no access to internals
# Red                              # COMPILE ERROR — variants hidden
# if c is Red then ...             # COMPILE ERROR — can't pattern match
Color.to_hex(my_color)             # method — works
```

```ruby
# another module — same restrictions
import color exposing [Color]

Color.to_hex(my_color)             # method — works
# Red                              # COMPILE ERROR — variants hidden
# if c is Red then ...             # COMPILE ERROR — can't pattern match
```

**Pattern matching** — always uses bare tags. The value's type provides context:

```ruby
import shape exposing [Shape]

describe = |s|
    if s
        : Circle(r) then "circle with radius ${r}"
        : Rect(w, h) then "${w} by ${h} rectangle"
```

No `Shape.Circle(r)` in patterns — the compiler knows `s` is a `Shape` and resolves the tags from there.

The `.( )` block is the visibility boundary for opaque types. Inside the block, the type is fully accessible. Outside — even in the same module — only the public API is available. This means code behaves identically regardless of which module it's in, and avoids name collisions when a module defines multiple types with same-named methods.

## Transparent nominal types

Transparent nominal types (`:=`) create a distinct type with methods. Internals are visible everywhere — inside and outside the module:

```ruby
# shape.rb
exports [Shape]

Shape := [Circle(F64), Rect(F64, F64)].(
    area : Shape -> F64
    area = |shape|
        if shape
            : Circle(r) then 3.14 * r * r
            : Rect(w, h) then w * h
)
```

```ruby
# another module
import shape exposing [Shape]

my_shape = Shape.Circle(5.0)                    # construct through the type
result = if my_shape is Circle(r) then r         # pattern match with bare tag
```

The type is distinct — `Shape` and `[Circle(F64), Rect(F64, F64)]` are different types. But because the internals are transparent, constructors and pattern matching work from anywhere. Use transparent nominal when every possible value of the underlying structure is valid — there are no invariants to protect.

Nominal unions are closed — no extension variables. You cannot write `Shape := [Circle(F64), ..a]`. This is fundamental: a nominal type is a complete definition, not a template for extension.

> Considering: `..ConcreteAlias` as copy-paste sugar — `Color := [Red, Green, Blue, ..OtherColor]` where `OtherColor` is a concrete alias would desugar to inlining those tags. The union is still closed. Only concrete aliases, never type variables.

## Opaque types

Opaque types (`::`) hide their internals outside the `.( )` block. The block is the trust boundary — inside it, the type is transparent. Outside — even in the same module — only the public API is available.

```ruby
# username.rb
exports [Username]

Username :: Str.(
    from_str : Str -> Result(Username, [InvalidUsername])
    from_str = |s|
        if s.count_graphemes() > 0 and s.count_graphemes() <= 20
            then Ok(s)              # Str wraps to Username (return type provides context)
            else Err(InvalidUsername)

    to_str : Username -> Str
    to_str = |s| s                  # Username unwraps to Str (block can see internals)
)

# Free helper in the same module — no access to internals
normalize = |s| s.trim().to_lowercase()  # takes Str, not Username
```

```ruby
# another module — same restrictions as the module body
import username exposing [Username]

name = Username.from_str("alice")       # must use the API
# "alice"                               # COMPILE ERROR — can't construct Username from Str
# if name is s then ...                 # COMPILE ERROR — can't unwrap Username
```

Use opaque when you need to guarantee invariants — the public API becomes the only way in, so validation can't be bypassed. The `.( )` block is the trust boundary, not the module. This means code copied between modules works identically — no module-specific privileges.

## Mutually recursive types

A module can define multiple types. Mutually recursive types must be in the same file:

```ruby
exports [Foo, Bar]

Foo := [Nothing, Other(Bar)].(equals : _)
Bar := [Nothing, Other(Foo)].(equals : _)
```

## Recursive types

Recursive types refer to themselves at one or more positions. The compiler detects recursive positions (same syntactic name check used by [fold](fold.md)) and handles their memory representation automatically — no annotation needed:

```ruby
Tree(a) := [Leaf(a), Node(Tree(a), Tree(a))].(
    sum : Tree(I64) -> I64
    sum = |t| fold t
        : Leaf(val) then val
        : Node(left, right) then left + right
)

LinkedList(a) := [Nil, Cons(a, LinkedList(a))].(
    equals : _
    to_str : _
)
```

```ruby
# Building a tree
leaf = Leaf(1)
tree = Node(Leaf(2), Leaf(3))
```

Non-recursive types are stack-allocated by default. Recursive types require heap indirection at the recursive position — the compiler inserts this automatically. The programmer writes clean type definitions; the compiler chooses the optimal representation (heap-allocated nodes, contiguous buffers, or plain integers depending on the [fold compilation strategy](fold.md#what-fold-compiles-to)).

## Performance

Structural tag unions are designed to compile to the same code as Rust
enums in the common case. The ergonomic benefits of open rows (error
propagation without `map_err`, inline variant return types) don't come
at a runtime cost, because open rows exist only during type inference.

Three commitments preserve this:

**Open rows are compile-time only.** By the time code generation runs,
every tag union has been closed to a concrete set of tags. Inference
uses open rows for composition (unifying `Red` and `Green` into `[Red |
Green]`, growing error types through a `?` chain). Monomorphization
closes every remaining open row at function boundaries before layout
is selected. The SSA layer never sees open rows.

**Monomorphization specializes per closed tag row.** Two call sites
with different closed tag sets — `parse_color` called in a context
expecting `[Red, Green]` vs. one expecting `[Red, Green, Blue]` —
produce two specializations with distinct layouts, same as
monomorphization on record rows or generic types. The compiler may
instead emit a tag-index remap at the call site if specialization
budget is tight, but the default is specialize.

**Runtime tag indices are per-specialization, not global.** The tag
`Red` in `[Red, Green]` has index 0; the tag `Red` in `[Red, Green,
Blue]` also has index 0 (or whatever the normalized order picks).
There is no global tag interner — each closed union assigns its own
indices 0..N, dense. This enables compact representations: a tag of
type `[None, Some(T)]` occupies exactly as much space as a Rust
`Option<T>`, and gets niche optimizations where `T` permits them.

Together, these commitments let the compiler emit:

- **Stack-allocated tagged values** for non-recursive unions (already
  the default — see [recursive types](#recursive-types))
- **Compact discriminants** (`u8` for unions with ≤256 variants, or
  `u2` where bit-packing helps)
- **Niche optimizations** — `[None, Some(&T)]` uses the null pointer
  as `None`, no extra byte; `[None, Some(NonZero(u8))]` uses the zero
  byte; etc.
- **Jump-table match compilation** for exhaustive matches on closed
  unions — no default fallthrough
- **Single-variant elimination** — a closed union with one variant is
  just the variant's payload, no tag at all

The one cost to be aware of: helpers that take open-row arguments (for
instance, generic error-propagation combinators) may specialize more
than once when called with different concrete error sets. Practically
this is the same price paid for any generic function in a
monomorphizing compiler.

## Design rationale

> Why `[...]` brackets for tag unions instead of pipes (`Red | Green | Blue`)?

The `[...]` bracket notation enables attaching methods directly: `Color := [Red, Green, Blue].( ... )`. With pipe syntax, there's no natural place to attach the `.( )` block. The brackets also visually distinguish type declarations from pattern matching — `[A, B, C]` defines a closed set of variants, `A | B` matches alternatives within an existing set.

> Why are tag unions open by default?

Open-by-default eliminates the most tedious part of error handling in typed functional languages: converting between error types at composition boundaries. `Result(ok, err)` is `[Ok(ok), Err(err)]`, and the `err` parameter is itself an open tag union. When you chain `parse` (which can produce `ParseErr`) with `validate` (which can produce `ValidationErr`), the error type grows automatically to `[ParseErr(Str), ValidationErr(Str)]`. No `map_err`, no wrapper types, no boilerplate.

The tradeoff: inferred types can be large open unions that are harder to read. Type annotations on public functions help — they document the expected variants and close the union at API boundaries.

> Why discriminated tags instead of arbitrary type unions (`Str | I32`)?

TypeScript-style unions combine existing types without a tag: `string | number | null`. The runtime value carries no discriminant — dispatch relies on `typeof` checks, and subtyping can cause the wrong branch to match (C#'s `OneOrMore<T>` demonstrates this: a `List<T>` matches the `IEnumerable<T>` branch before the single-element branch because a list is-an enumerable). Ad-hoc untagged unions also have no discrete type to attach documentation to, no place for methods, and no way to distinguish two structurally identical cases (`type UserId = string; type Email = string` — `UserId | Email` collapses to `string`).

Ori's tag unions avoid all three problems. Every variant carries a constructor name (`Ok(42)`, `Err(msg)`) that serves as the discriminant — pattern matching is exact, not subtype-based. Tags compose ad-hoc (no declaration needed for structural tags) but remain discriminated, so `[UserId(Str), Email(Str)]` keeps the two cases distinct. And when you need methods or invariants, `:=` and `::` provide a named type with a `.( )` block.

> Why automatic boxing instead of explicit `Box`?

Recursive positions always need heap indirection — it's not optional. The compiler already identifies recursive positions (for [fold](fold.md) semantics), so requiring the programmer to annotate the same information is redundant. Automatic representation also gives the compiler freedom to choose optimal layouts: a `Nat` can be a plain integer, a `List` a contiguous buffer, a `Tree` heap-allocated nodes. Explicit `Box` would lock in a pointer-based representation and add noise to every recursive type definition.

> Why three declaration forms instead of one?

C# 15 shipped unnamed unions as a first step, with named discriminated unions, anonymous unions, and closed hierarchies planned as separate features across future versions. Each addresses a different point in the design space (ad-hoc vs. nominal, open vs. closed, methods vs. plain data), so the language accumulates distinct mechanisms over time.

Ori's `:` / `:=` / `::` cover the same space with one syntax that varies in a single dimension — how much the type hides. `:` gives a structural alias (ad-hoc, open). `:=` adds a nominal boundary with methods (closed, transparent). `::` adds an encapsulation boundary (closed, opaque). The three forms compose with the same tag syntax, same pattern matching, and same `.( )` block — no separate feature for each combination of naming and visibility.
