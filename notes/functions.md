# Functions

Functions are first-class values — they can be assigned to variables, passed as arguments, and returned from other functions. Functions are lambdas assigned to names. Calls use parens and commas:

```ruby
# Named function (body is always a single expression)
add = |x, y| x + y

# Zero-arg function (deferred evaluation)
greet = || "hello"

# Multi-line body (block expression with parens)
process = |items| (
    filtered = items.keep_if(|x| x > 0)
    filtered.map(|x| x * 2)
)

# Calling
add(1, 2)
items.map(|x| x + 1)

# Higher-order
apply = |f, x| f(x)
apply(|x| x + 1, 5)
```

Function calls require the opening paren to touch the function name — no space allowed:

```ruby
foo(1, 2)     # function call
foo (1, 2)    # NOT a call — foo followed by a grouped expression
```

This prevents ambiguity when expressions appear on consecutive lines. Without this rule, the parser can't tell if a paren on the next line starts a new expression or continues a call from the previous line.

## Function types

The `->` separates arguments from return type. Multiple arguments use commas:

```ruby
add : I32, I32 -> I32
transform : List(a), (a -> b) -> List(b)
predicate : a -> Bool
default : {} -> Config
```

## Closures

Lambdas capture variables from their enclosing scope by value (since all values are immutable, this is always safe):

```ruby
make_adder = |n| (|x| x + n)
add5 = make_adder(5)
add5(3)  # 8
```

## Dot shorthand

A `.` in expression-start position (no receiver) creates a shorthand lambda — the implicit argument becomes the receiver:

```ruby
arr.map(.name)                    # |x| x.name
arr.keep_if(.is_active)            # |x| x.is_active
arr.filter(.lt(2))                # |x| x.lt(2)
arr.sort_by(.age)                 # |x| x.age
arr.keep_if(.genre.equals(Rock))  # |x| x.genre.equals(Rock)
```

The shorthand greedily consumes the full method chain — `.genre.equals(Rock)` is one lambda, not a method call on `.genre`. It ends when the parser hits something that isn't `.identifier` or `.identifier(args)`.

Only covers projections and method chains on a single argument. Anything more complex uses a full lambda:

```ruby
arr.map(|x| x + 1)                     # arithmetic — no shorthand
arr.map(|x| "${x.name}: ${x.age}")      # interpolation — no shorthand
arr.map(|x| x->Str.trim())              # pipe call — no shorthand
```

## Error propagation with `?`

The `?` operator unwraps a `Result` — on `Ok`, it extracts the value; on `Err`, it returns early from the enclosing function. Because error types are [open tag unions](tags.md#tag-unions), the error types compose automatically:

```ruby
parse : Str -> Result(I32, [ParseErr(Str)])
parse = |s|
    if s.to_i32() is Ok(n) then Ok(n)
    else Err(ParseErr(s))

validate : I32 -> Result(I32, [ValidationErr(Str)])
validate = |n|
    if n > 0 then Ok(n)
    else Err(ValidationErr("must be positive"))

# ? unwraps Ok or returns Err early
# Error type grows to include both: [ParseErr(Str), ValidationErr(Str)]
process : Str -> Result(I32, [ParseErr(Str), ValidationErr(Str)])
process = |s| (
    n = parse(s)?
    validate(n)
)
```

No `map_err` or error type conversion needed — `?` propagates the error as-is, and the open union in the return type absorbs it.

## Design rationale

> Why `|args|` instead of `\args ->` or `(args) ->`?

`\args -> body` (Haskell/Elm) is awkward on non-US keyboards, breaks Vim tooling, and spends weirdness budget on something no mainstream language uses. `(args) -> body` (JS/Java) conflicts with tuples — `(x, y)` could be a tuple or lambda args, requiring parser backtracking. Naked `x, y -> body` is ambiguous with comma-separated function args. `|` provides an unambiguous start-of-lambda delimiter — the parser sees `|` in expression-start position and immediately knows it's a lambda. Roc's community arrived at this syntax after extensive discussion of all alternatives.

> Doesn't `|` conflict with bitwise OR?

`|` is dual-duty but disambiguation is clean by position: expression-start → lambda params (`|x| x + 1`), infix between expressions → bitwise OR (`a | b`). Or-patterns use the `or` keyword instead, matching `and` for guards and keeping symbols (`&`, `|`, `^`) for bitwise operations and keywords (`and`, `or`) for logic and patterns.

> Why `name = |args| body` instead of `name(args) = body` or `name args = body`?

Functions are values — `add = |x, y| x + y` uses the same binding form as `pi = 3.14`. No separate "function definition" concept. This keeps `name = expr` as always a binding and `name(args)` as always a call — no lookahead needed to tell them apart. `name(args) = body` breaks this because the parser must see `=` before it knows `name(args)` isn't a call. `name args = body` (Haskell-style) assumes currying, which Ori doesn't have — without it, the syntax would be a special form that looks like application but isn't. It also conflicts with the no-space rule, where `foo (expr)` is explicitly not a call.

> Why `.foo` shorthand instead of a placeholder like `_` or `it`?

`.foo` reuses existing method syntax — it's visually identical to a method call with the receiver removed. No new keyword or sigil needed. The parser disambiguates by position: `.` after an expression is a method call, `.` at expression start is the shorthand. This keeps the grammar context-free and maintains grepability — `.foo(` still finds all method calls on `foo`, whether shorthand or not.
