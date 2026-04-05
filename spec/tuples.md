# Tuples

Tuples are positional, fixed-length groupings of values. They're for short-lived, unnamed data where field names would be ceremonial — `zip` results, multiple return values, pattern matching on multiple things at once.

```ruby
pair = (1, 2)
origin = (0.0, 0.0)
rgb = (255, 128, 0)
```

## Arity

Tuples always have 2 or more elements:

- `(a, b)` — 2-tuple
- `(a, b, c)` — 3-tuple
- `(expr)` — grouping / block, never a tuple

There are no 1-tuples. `(x)` is always parenthesized grouping. This avoids the `(x,)` trailing-comma hack that Python and Rust need, where a single trailing comma changes the meaning of an expression.

## Unit type

The unit type is `{}` — the empty record. It represents "no meaningful value."

```ruby
greet : Str -> {}
greet = |name| print("hello ${name}")

now : {} -> Time
```

Using `{}` as unit instead of `()` has several advantages:

- **Tuples have no gaps.** With `()` as unit, tuple arities would be 0, 2, 3, 4... but not 1. With `{}` as unit, tuples are cleanly 2+ and parens are always grouping.
- **`()` is unambiguous.** `foo()` always means "call foo with no arguments." No confusion between "passing unit" and "passing nothing."
- **Zero-arg functions.** `() -> Time` reads as "takes no arguments, returns Time." The visual connection between calling `now()` and its type `() -> Time` is preserved without `()` being a value.

The tradeoff: `Str -> {}` looks slightly odd vs `Str -> ()`. Minor aesthetic cost for a cleaner type system.

## Destructuring

Tuples are always destructured via pattern matching. There is no positional access (`.0`, `.1`, `.2`):

```ruby
(a, b) = make_pair()
(q, r) = divmod(10, 3)

// In function args
pairs.map(|(k, v)| process(k, v))

// In match arms
if result
    : (Ok(x), Ok(y)) then combine(x, y)
    : (Err(e), _) then handle(e)
    : (_, Err(e)) then handle(e)
```

> Why no `.0`, `.1`?

Positional access is unreadable — `result.2` says nothing about what the third element means. Requiring destructuring forces the programmer to name the components at the use site. If you're reaching for `.0`, use a record instead.

This also avoids open tuples in the type system. If `.0` existed, `|t| t.0` would need a type like `(a, ..) -> a` — an open tuple that can match any length. Open tuples add complexity for marginal benefit.

## Tuples as arguments

Tuples should not be used as function parameters. Use multiple named parameters instead:

```ruby
// Bad: caller has to construct a tuple
distance : (I64, I64), (I64, I64) -> I64

// Good: named parameters
distance : I64, I64, I64, I64 -> I64

// Better: records
distance : { x: I64, y: I64 }, { x: I64, y: I64 } -> I64
```

Tuples are useful as return values and in pattern matching — places where the caller names the components at the use site.

## When to use tuples vs records

Use tuples when you'd struggle to name the fields — generic pairs from `zip`, multiple return values from `divmod`, coordinates that are immediately destructured. Use records when fields carry meaning or the type appears in APIs.

```ruby
// Tuple: positional, generic, immediately destructured
zip : List(a), List(b) -> List((a, b))
divmod : I64, I64 -> (I64, I64)

// Record: named, meaningful, passed around
User : { name: Str, age: I64 }
Config : { port: U16, host: Str }
```

## Type syntax

```ruby
pair : (I64, I64)
triple : (I64, I64, I64)
nested : (I64, (Bool, Bool))

transform : (I64, I64) -> (I64, I64)
```

## Design rationale

> Why have tuples at all? Records can do everything.

Records can express anything tuples can, but with syntactic overhead. `List((Str, I64))` from a `zip` is natural. `List({ first: Str, second: I64 })` forces you to invent meaningless names. Without tuples, people create inconsistent workarounds: `T a b`, `Pair a b`, `Tuple a b` — all incompatible with each other. The Roc community tried life without tuples and concluded they're needed.

> Why not structural tuples that are secretly records?

Keeping tuples and records as distinct types is simpler — tuples are positional, records are named, no implicit conversion between them. Roc compiles tuples as records with numeric field names, which adds complexity for interop. Separate types, separate purposes.

> Why `{}` for unit instead of `()`?

See the unit type section above. `{}` eliminates the 1-tuple gap, makes `()` unambiguous as zero-arg call syntax, and is conceptually clean — unit is the product of zero fields, just like a record with no fields.
