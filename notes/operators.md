# Operators

All operators are syntactic sugar — they desugar to associated function calls or compiler special forms. No custom operator definitions, no operator overloading beyond what constraints provide.

## Desugaring

Each operator desugars to a method call with a **required signature shape**. The operator only works if the type has the named method with a matching signature. A method with the same name but a different signature is a regular method — it doesn't get operator syntax.

This means operators are predictable: `+` always combines two values of the same type, `==` always compares two values of the same type. No mixed-type operators.

### Arithmetic operators

```ruby
x + y    →  x.add(y)       # requires add : a, a -> a
x - y    →  x.sub(y)       # requires sub : a, a -> a
x * y    →  x.mul(y)       # requires mul : a, a -> a
x / y    →  x.div(y)       # requires div : a, a -> a
x % y    →  x.mod(y)       # requires mod : a, a -> a
```

For integers, `div` and `mod` panic on division by zero — the same way `add` panics on overflow. Use `div_checked` and `mod_checked` for recoverable handling (they return `Result`). For floats, `div` follows IEEE 754 (returns `Inf`/`NaN`, never panics).

Roc originally made `div`/`mod` return `Result`. The experiment failed — in practice, everyone defines a convenience function that unwraps the Result, because the caller almost always knows the divisor is non-zero. Panicking by default with checked variants available is the right tradeoff.

### Comparison operators

```ruby
x == y   →  x.equals(y)                  # requires equals : a, a -> Bool
x != y   →  !(x.equals(y))               # requires equals : a, a -> Bool
x < y    →  x.compare(y) is Lt           # requires compare : a, a -> Order
x > y    →  x.compare(y) is Gt           # requires compare : a, a -> Order
x <= y   →  x.compare(y) is (Lt or Eq)   # requires compare : a, a -> Order
x >= y   →  x.compare(y) is (Gt or Eq)   # requires compare : a, a -> Order
```

`!=` is always `!(x.equals(y))` — no separate `not_equals` method. Rust lets you override `ne` via `PartialEq`, but in practice nobody does, and when they do it's almost always a bug (inconsistent `eq`/`ne`). Clippy warns against it.

> Why does `compare` return `Order` instead of `Bool`?

Comparing two values has three outcomes, not two. `Order` (`[Lt, Eq, Gt]`) preserves the full result; a Bool-returning `less_than` loses information — `false` could mean equal or greater.

One function covers all four ordering operators (`<`, `>`, `<=`, `>=`). With Bool, you'd need two primitives (`less_than` + `equals`) or four separate methods.

Sorting needs one call per comparison, not two. With `less_than`, distinguishing "equal or greater" after `false` requires a second call to `equals`. With `compare`, one call resolves all three cases — this matters in tight sort loops.

Three-way results also compose naturally with pattern matching:

```ruby
if a.compare(b)
    : Lt then "less"
    : Eq then "equal"
    : Gt then "greater"
```

This is the standard design in languages with algebraic types: Haskell's `Ordering`, Rust's `Ordering`, OCaml's `int` convention, C++20's spaceship operator (`<=>`). Languages that use Bool for comparisons (Python's `__lt__`, Java's original `Comparable`) generally regret it or work around it.

### Bitwise operators

```ruby
x & y    →  x.bit_and(y)      # requires bit_and : a, a -> a
x | y    →  x.bit_or(y)       # requires bit_or : a, a -> a
x ^ y    →  x.bit_xor(y)      # requires bit_xor : a, a -> a
```

### Unary prefix operators

```ruby
-x       →  x.neg()           # requires neg : a -> a
!x       →  x.not()           # requires not : Bool -> Bool
```

Both require no space between the operator and operand: `-x` is negation, `- x` is a parse error.

### Why signature-matched desugaring?

A type can have a method called `add` without getting `+`. The operator only fires when the signature matches `a, a -> a`. This prevents accidental operator semantics:

```ruby
# Set.insert : Set(a), a -> Set(a)
# Even if named `add`, this doesn't match a, a -> a
# because Set(a) ≠ a. No `+` operator.

# Set.union : Set(a), Set(a) -> Set(a)
# This DOES match a, a -> a where a = Set(elem).
# set1 + set2 works — and that's the right semantics for + on sets.
```

What you give up: no mixed-type operators. `DateTime + Duration`, `Vector * Scalar`, `Matrix(m,n) * Matrix(n,p)` can't use operator syntax. Named methods are clearer for asymmetric operations anyway — `datetime.shift(duration)` and `vec.scale(2.0)` say what they mean.

### Try operator (special form)

```ruby
x?       →  if x is Err(e) return Err(e) else unwrap
```

`?` is a postfix operator on `Result`. It unwraps `Ok(val)` to `val`, or early-returns `Err(e)` from the enclosing function — not the enclosing block. `(x? + y?)` returns from the function, not the parenthesized expression. The enclosing function must return a compatible `Result` type.

```ruby
read_config! = |path| (
    content = File.read!(path)?
    parse(content)?
)
# read_config! : Str => Result(Config, [FileNotFound, PermissionDenied, ParseError])
```

The error types unify across `?` sites — the function's return type is `Result(a, e)` where `e` is the union of all possible errors. No manual error wrapping needed.

### Boolean operators (special forms)

```ruby
x and y  →  if x then y else False
x or y   →  if x then True else y
```

`and` and `or` are short-circuiting — `y` is only evaluated if needed. They cannot desugar to method calls because method arguments are always evaluated. These are compiler special forms.

### Pattern matching operator (special form)

```ruby
x is P   →  pattern match, returns Bool
```

`is` tests whether `x` matches pattern `P`. It binds pattern variables in the surrounding scope. Not a function call — the right operand is a pattern, not an expression.

## Naming

Operator method names use the established term for each operation — there is no artificial consistency rule like "all names must be 3 letters."

**Arithmetic ops use standard mathematical verbs.** `add`, `sub`, `mul`, `div`, `mod`, `neg`. These aren't abbreviations of longer words — they ARE the canonical terms, standard in mathematics, assembly, and dozens of languages (Rust, Zig, OCaml). They're called through operator symbols (`+`, `-`, `*`, `/`, `%`, prefix `-`), rarely by name. In the contexts where the name appears — constraint definitions, derived implementations — the standard mathematical term is the most natural. Collections use `insert` for element addition, not `add` — `add` is the `+` operator method (`a, a -> a`), and the naming collision with Java/C#/Python's `Collection.add` would be confusing.

**Comparison ops use full English words.** `equals`, `compare`. These are called by name regularly: passed as callbacks, referenced in `where` clauses, used in generic code. `x.equals(y)` reads as "x equals y." `list.sort_by(compare)` reads naturally.

> Why not `eq` / `cmp`?

`eq` collides visually with the `Eq` constraint — `a.eq` vs `a.Eq` differ by one character of case. `a.equals` vs `a.Eq` is clearly distinct. `cmp` saves 4 characters but is opaque outside C/Rust. Haskell, Java, Kotlin, and OCaml all use `compare`.

**Bitwise ops use `bit_` prefix for disambiguation.** `bit_and`, `bit_or`, `bit_xor`. The prefix prevents collision with the boolean `and`/`or` keywords. `bit_xor` doesn't technically collide with anything, but consistency within the group matters. Snake_case matches the rest of the stdlib (`keep_if`, `drop_if`, `div_checked`).

**Boolean ops are full words.** `not` is already 3 letters. `and`/`or` are keywords (short-circuiting special forms), not method names.

> Why not `plus` / `minus` / `times`?

These are names for the *symbols*, not the *operations*. "Add" is a mathematical verb — you add numbers. "Plus" is a conjunction — "three plus four." You'd never define a function called `plus`. Same problem with `times` (also means "occasions") and `slash`/`percent` (names of punctuation marks).

> Why not `subtract` / `multiply` / `divide` / `negate`?

`add`/`sub`/`mul`/`div`/`mod`/`neg` aren't abbreviations that should be expanded — they are the standard terms. Like `len` isn't short for `length`; it's the canonical name across Go, Rust, Python, and Zig. The 3-letter forms have been standard in mathematics and programming for decades. `subtract` and `multiply` are the pedagogical forms, not the terms programmers work with.

| Category | Names | Rationale |
| --- | --- | --- |
| Arithmetic | `add`, `sub`, `mul`, `div`, `mod`, `neg` | Standard mathematical verbs. Called via operators, rarely by name. |
| Comparison | `equals`, `compare` | Full English words. Called by name in generic code and callbacks. |
| Bitwise | `bit_and`, `bit_or`, `bit_xor` | Prefixed to disambiguate from `and`/`or` keywords. Snake_case for consistency. |
| Boolean | `not` | Full word, 3 letters. `and`/`or` are keywords, not methods. |
| Hashing | `hash` | Full word, 4 letters. No reason to abbreviate. |
| Display | `to_str` | Follows `to_*` conversion convention. |

## Precedence

Tightest to loosest:

| Precedence | Operators         | Associativity   |
| ---------- | ----------------- | --------------- |
| 0          | `?`               | postfix         |
| 1          | `is`              | non-associative |
| 2          | `*` `/` `%`       | left            |
| 3          | `+` `-`           | left            |
| 4          | `==` `!=`         | non-associative |
| 5          | `<` `>` `<=` `>=` | non-associative |
| 6          | `&` `\|` `^`      | left            |
| 7          | `and`             | left            |
| 8          | `or`              | left            |

## Division and modulo

Integer division (`div`) and modulo (`mod`) use **Euclidean** semantics. The remainder is always non-negative:

```ruby
 7.div(3)    #  2       7.mod(3)    # 1
(-7).div(3)  # -3      (-7).mod(3)  # 2
 7.div(-3)   # -2       7.mod(-3)   # 1
 7.div(0)    # panic: division by zero
```

### Why `mod`, not `rem`?

`rem` implies truncated remainder (C/Rust semantics). `mod` signals mathematical modular arithmetic. Ori provides only `mod` — one correct operation is better than two that invite confusion about which to use.

## Panics

Arithmetic should only panic in two cases:

1. **Integer overflow** — wrapping silently is a bug factory; checked arithmetic by default, with explicit `.wrapping_add()` etc. for intentional wrapping
2. **Integer division by zero** — `div` and `mod` panic; `div_checked` and `mod_checked` return `Result` for recoverable handling

Everything else — float division by zero (returns `Inf`/`NaN`), float overflow (returns `Inf`) — follows IEEE 754 and does not panic. Floats never panic.

## References

- [On div and mod](https://julesjacobs.com/2023/09/23/on-div-and-mod.html) — Jules Jacobs
- [Modulo of negative numbers](https://torstencurdt.com/tech/posts/modulo-of-negative-numbers/) — Torsten Curdt
- [The Euclidean definition of the functions div and mod](https://dl.acm.org/doi/pdf/10.1145/128861.128862) - RAYMOND T. BOUTE
- [Division and Modulus for Computer Scientists](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/divmodnote-letter.pdf) - Daan Leijen
