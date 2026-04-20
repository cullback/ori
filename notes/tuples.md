# Tuples

Tuples are positional, fixed-length groupings of values. They're for short-lived, unnamed data where field names would be ceremonial — `zip` results, multiple return values, pattern matching on multiple things at once.

```ruby
pair = (1, 2)
origin = (0.0, 0.0)
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

default : {} -> Config
```

Using `{}` as unit instead of `()` has several advantages:

- **Tuples have no gaps.** With `()` as unit, tuple arities would be 0, 2, 3, 4... but not 1. With `{}` as unit, tuples are cleanly 2+ and parens are always grouping.
- **`()` is unambiguous.** `foo()` always means "call foo with no arguments." No confusion between "passing unit" and "passing nothing."
- **Zero-arg functions.** `() -> Config` reads as "takes no arguments, returns Config." The visual connection between calling `default()` and its type `() -> Config` is preserved without `()` being a value.

The tradeoff: `Str -> {}` looks slightly odd vs `Str -> ()`. Minor aesthetic cost for a cleaner type system.

## When to use tuples vs records

Use tuples when you'd struggle to name the fields — generic pairs from `zip`, multiple return values from `divmod`, coordinates that are immediately destructured. Use records when fields carry meaning or the type appears in APIs.

```ruby
# Tuple: positional, generic, immediately destructured
zip : List(a), List(b) -> List((a, b))
enumerate : List(a) -> List((U64, a))
divmod : I32, I32 -> (I32, I32)

# Record: named, meaningful, passed around
User : { name: Str, age: I32 }
Config : { port: U16, host: Str, debug: Bool }
```

Tuples should not be used as function parameters — use multiple named parameters or records instead:

```ruby
# Bad: caller has to construct a tuple
distance : (I32, I32), (I32, I32) -> I32

# Good: named parameters
distance : I32, I32, I32, I32 -> I32

# Better: records
distance : { x: I32, y: I32 }, { x: I32, y: I32 } -> I32
```

Tuples are useful as return values and in pattern matching — places where the caller names the components at the use site.

## Type syntax

```ruby
pair : (Str, I32)
triple : (F64, F64, F64)
nested : (Str, (I32, Bool))

transform : (F64, F64) -> (F64, F64)
```

## Destructuring

Tuples are always destructured via pattern matching. There is no positional access (`.0`, `.1`, `.2`):

```ruby
(a, b) = make_pair()
(q, r) = divmod(10, 3)
(first, rest) = split_at(items, 1)

# In function args
pairs.map(|(k, v)| process(k, v))

# In match arms
if result
    : (Ok(x), Ok(y)) then combine(x, y)
    : (Err(e), _) or (_, Err(e)) then handle(e)
```

## Nominal and opaque tuples

Tuples can be declared as transparent nominal (`:=`) or opaque (`::`) types, following the same rules as [tag unions](tags.md#type-declarations).

**Transparent nominal** — a distinct type, but elements are accessible everywhere:

```ruby
# coord.rb
exports [Coord]

Coord := (F64, F64).(
    origin : Coord
    origin = (0.0, 0.0)

    distance : Coord, Coord -> F64
    distance = |(x1, y1), (x2, y2)| ((x2 - x1) ** 2 + (y2 - y1) ** 2).sqrt()
)
```

```ruby
# another module
import coord exposing [Coord]

c = Coord.origin
(x, y) = c                  # destructuring works — internals visible

# Construction via type context — bare tuple unifies with Coord
make_coord : F64, F64 -> Coord
make_coord = |x, y| (x, y)

# Same when passing to a function that expects Coord
distance((0.0, 0.0), (3.0, 4.0))
```

**Opaque** — inside the defining module, the type is transparent. Outside, only the public API is available:

```ruby
# sorted_pair.rb
exports [SortedPair]

SortedPair :: (I32, I32).(
    new : I32, I32 -> SortedPair
    new = |a, b| (a.min(b), a.max(b))   # enforces first <= second

    first : SortedPair -> I32
    first = |(a, _)| a

    second : SortedPair -> I32
    second = |(_, b)| b
)
```

```ruby
# another module
import sorted_pair exposing [SortedPair]

p = SortedPair.new(5, 3)
SortedPair.first(p)          # through the API — returns 3
# (a, b) = p                 # COMPILE ERROR — can't destructure
```

The module is the visibility boundary — same model as [opaque tag unions](tags.md#opaque-types) and [opaque records](records.md#nominal-and-opaque-records).

## Design rationale

> Why have tuples at all? Records can do everything.

Records can express anything tuples can, but with syntactic overhead. `List((Str, I32))` from a `zip` is natural. `List({ first: Str, second: I32 })` forces you to invent meaningless names. Without tuples, people create inconsistent workarounds: `T a b`, `Pair a b`, `Tuple a b` — all incompatible with each other. The Roc community tried life without tuples and concluded they're needed.

> Why not structural tuples that are secretly records?

Keeping tuples and records as distinct types is simpler — tuples are positional, records are named, no implicit conversion between them. Roc compiles tuples as records with numeric field names, which adds complexity for interop. Separate types, separate purposes.

> Why no `.0`, `.1`?

Positional access is unreadable — `result.2` says nothing about what the third element means. Requiring destructuring forces the programmer to name the components at the use site. If you're reaching for `.0`, use a record instead.

This also avoids open tuples in the type system. If `.0` existed, `|t| t.0` would need a type like `(a, ..) -> a` — an open tuple that can match any length. Open tuples are strange (Brendan: "really weird to only specify the prefix of a tuple") and add complexity for marginal benefit.

> Why `{}` for unit instead of `()`?

`{}` eliminates the 1-tuple gap, makes `()` unambiguous as zero-arg call syntax, and is conceptually clean — unit is the product of zero fields, just like a record with no fields.
