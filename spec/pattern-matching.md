# Pattern matching

Everything is `if`. Boolean conditionals, pattern matching, early return, and fallible destructuring all use the same keyword. Multi-arm matching uses `:` to separate arms. `is`, `and`, and `or` are expression operators that work the same way everywhere.

**Keywords:** `if`, `is`, `and`, `or`, `then`, `else`, `return` (7 total).

## `:` and `is`

The `:` symbol means **"has shape"** in both type hints and pattern matching:

- **Type hint**: `x : I32` — "x has type I32"
- **Arm**: `: Circle(r) then ...` — "has form Circle(r)"

Types describe the shape of a value abstractly (at the type level). Patterns describe the shape of a value concretely (at the value level). The `:` connects them — it always introduces a description of what something looks like.

The `is` keyword means **"does this match?"** — it tests a value against a pattern and returns a boolean:

```ruby
# is asks a question (returns Bool)
valid = x is Ok(_)

# : introduces a case (starts a branch)
if x
    : Ok(val) then use(val)
    : Err(e) then handle(e)
```

Think of `:` as declarative ("this is what it looks like") and `is` as interrogative ("does it look like this?"). In type hints, `:` declares the type. In arms, `:` declares the form. In expressions, `is` tests the form.

```ruby
# Type hint — x has type Result(I32, Str)
x : Result(I32, Str)

# Pattern test — does x have form Ok(_)?
if x is Ok(_) then handle() else skip()

# Multi-arm — what form does x have?
if x
    : Ok(val) then use(val)
    : Err(e) then handle(e)
```

## Examples

```ruby
# --- Expression operators ---
valid = x is Ok(_)
both = a and b
either = a or b
check = x is Ok(_) or y is Ok(_)    # (x is Ok(_)) or (y is Ok(_))

# --- Boolean conditional ---
if condition then a else b
if a and x is Ok(val) then use(val) else default

# --- Early return ---
if condition return expr
if x is Ok(val) return val

# --- Fallible destructuring ---
if x is Ok(val) then val else default_value

# --- Multi-arm matching ---
if shape
    : Circle(r) then 3.14 * r * r
    : Rect(w, h) then w * h

# --- Catch-all ---
if status_code
    : 200 then ok()
    : 404 then not_found()
    else unknown()

# --- Guards ---
if command
    : Move(dist) and dist > 100 then move_fast(dist)
    : Move(dist) then move_slow(dist)
    : Stop then halt()

# --- Nested patterns ---
if result
    : Ok(Just(val)) then use(val)
    : Ok(Nothing) then fallback()
    : Err(e) then handle(e)

# --- List patterns (.. can appear once, in any position) ---
if items
    : [] then empty()
    : [only] then single(only)
    : [first, ..rest] then process(first, rest)
    : [first, ..] then just_first(first)
    : [.., last] then just_last(last)
    : [first, ..middle, last] then bookends(first, middle, last)
    : [first, second, ..] then at_least_two(first, second)

# --- Record patterns (tag + record sugar) ---
if event
    : Click{ x, y } then handle_click(x, y)
    : KeyPress{ key, .. } then handle_key(key)

# --- Or-patterns (in arm heads, `or` separates alternatives) ---
if shape
    : Circle(r) or Sphere(r) then area(r)
    : Rect(w, h) or Box(w, h) then w * h

# --- Or-patterns in expressions (require parens) ---
valid = x is (Circle(r) or Sphere(r))

# --- Successive destructuring (is binds, and carries bindings forward) ---
if x is Foo(y) and cat(y) is Bar(z) and z > 0 then use(z)

if input
    : Wrapper(inner) and inner is Ok(val) and val > 10 then big(val)
    : Wrapper(inner) and inner is Ok(val) then small(val)
    : Wrapper(inner) and inner is Err(e) then handle(e)

# --- Interleaved computation (match, compute, match the result) ---
if expr is Var(name) and ctx.get(name) is Some(value) then use(value)

if name.strip_prefix("_") is Some(rest)
    and rest.to_i32() is Some(index)
    and index >= 0 and index < arity
    then Right(index, name)
    else Left("invalid identifier: ${name}")

# --- Early return (guard clause, falls through) ---
if x is Ok(val) return val
# handle error below

# --- Early return in a multi-arm (still exhaustive) ---
if x
    : Ok(val) return val
    : Err(e) then handle(e)

# --- Irrefutable destructuring ---
{ name, age: _, .. } = record
```

## `if` disambiguation

After `if`, the parser reads a full expression, then disambiguates by lookahead: `:` → multi-arm matching, `then` → boolean conditional, `return` → early return. Since `:` is not an expression operator, the parser uses a single expression grammar everywhere — no restricted expression context needed.

## `is` and patterns

The `is` operator takes a single `pattern` as its right operand — not an `or_pattern`. This prevents ambiguity with boolean `or`:

```ruby
x is Ok(_)                     # single pattern — fine
x is Ok(_) or y is Ok(_)       # (x is Ok(_)) or (y is Ok(_)) — boolean OR
x is (Ok(_) or Err(_))         # grouped or-pattern — fine
```

In arm heads, or-patterns work without parens because the arm rule parses `or_pattern` directly — `or` is consumed in pattern-parsing mode and terminated by `and`, `then`, or `return`.

> Why does `is` take a single pattern instead of an or-pattern?

If `is` consumed `or_pattern`, then `x is Ok(_) or y is Err(_)` would be ambiguous — is `or` extending the pattern or a boolean operator? Making `is` take a single pattern keeps `or` available as boolean OR in expression context. Parens opt in to or-patterns explicitly: `x is (Ok(_) or Err(_))`.

## Guards and precedence

In arms, `and` binds tighter than `or` — matching boolean expression precedence. `or` separates alternatives, `and` attaches a guard to a pattern:

```ruby
# and binds tighter: guard only applies to Bar(x)
: Foo(x) or Bar(x) and x > 10 then ...
# → Foo(x) or (Bar(x) and x > 10)

# Guard on both alternatives: use parens
: (Foo(x) or Bar(x)) and x > 10 then ...

# Different guards per alternative
: Foo(x) and x > 0 or Bar(x) and x < 0 then ...
# → (Foo(x) and x > 0) or (Bar(x) and x < 0)
```

The guard expression does not consume bare `or` — `or` at the arm level always starts the next alternative. Boolean `or` inside a guard requires parens:

```ruby
: Foo(x) and (x > 0 or x < -10) then ...
```

Guards can chain `and` for multiple conditions — `and` within the guard is boolean AND:

```ruby
if input is Wrapper(inner) and inner is Ok(val) and val > 10 then big(val)
```

## Pattern flowing

`is` both tests and binds. Bindings from `is` flow forward through `and` chains and into `then`/`return` branches via short-circuit evaluation — if the `is` fails, the rest of the `and` chain doesn't execute, so unbound variables are never reached.

```ruby
# y is bound by the first is, used in the computation, z is bound by the second is
if expr is Var(name) and ctx.get(name) is Some(value) then use(value)
```

**Scoping rules:**

- **`and`** — bindings flow forward. `x is Some(y) and y > 0` works because `and` short-circuits.
- **`then` / `return`** — bindings from the entire condition are available in the branch body.
- **`or`** — bindings do **not** flow through. `x is Some(y) or y > 0` is a compile error — `y` is not guaranteed to be bound.
- **Bare expressions** — `valid = x is Some(y)` does not bind `y` in the enclosing scope. `is` only binds within `and`/`then`/`return` continuations.

This replaces nested matching with flat `and` chains for the common pattern of match → compute → match the result:

```ruby
# Without pattern flowing: nested and verbose
if expr
    : Var(name) then
        if ctx.get(name)
            : Some(value) then use(value)
            else fallback()

# With pattern flowing: flat and readable
if expr is Var(name) and ctx.get(name) is Some(value)
    then use(value)
    else fallback()
```

Inspired by "The Ultimate Conditional Syntax" (Cheng & Parreaux, 2024) — called "conditional pattern flowing" in that paper.

## Design rationale

> Why `:` for arms?

An earlier design used `is` to start each arm. This forced a restricted expression parser that excluded `is` and `and` from scrutinees and arm results — otherwise the expression parser would greedily consume `shape is Circle(r)` as a boolean before the grammar could use `is` as an arm delimiter. The restricted parser created a silent misparse: `then f(y) is Ok(z) then z` would split into two arms instead of chaining. This tension was inherent to any design where `is` is both an expression operator and an arm delimiter.

Using `:` for arms eliminates this entirely. `:` is not an expression operator, so the full expression grammar works everywhere. Arm results can freely contain `is`, `and`, and `or`.

The choice of `:` also creates a conceptual connection with type hints — `:` always means "has shape." In `x : I32`, it describes the shape abstractly (at the type level). In `: Circle(r) then ...`, it describes the shape concretely (at the value level). See [`:` and `is`](#-and-is) above.

> Why `:` + `then` instead of arrows (`->`, `=>`) or `|pattern|`?

Every match syntax needs an unambiguous boundary between the pattern and the body. Languages have tried several approaches — all have problems that `:` + `then` avoids:

**Arrows (`->`)** conflict with other uses. In Tempo, `->` is pipe dispatch (`x->Str.trim()`). A guard like `Ok(a) and a->is_valid()->process()` becomes ambiguous — is `->` a match arrow or pipe dispatch? Roc hit exactly this problem. Using `=>` instead avoids that specific collision, but now you have two arrows to remember (`->` for pipes/pure functions, `=>` for effectful functions and match arms) — Rust has this problem and it's a persistent paper cut.

**Pipes (`|pattern|`)** reuse lambda syntax for match arms. This looks elegant in simple cases but breaks down in practice:

```
# Roc's |pattern| experiment — lambdas in arm bodies create visual soup
|(GET, "/articles/${slug}")| auth_optional!(|opt_user_id| get!(opt_user_id, slug))

# Guards have no clear boundary
|Ok(num)| if num > 3 Big

# Returning a lambda from a match arm — which || is which?
|Ok(num) if num > 3| |num| num + 100
```

Roc's community tried this syntax on a real-world HTTP router and multiple people found the `|` characters "swimming together" — patterns and lambdas became visually indistinguishable. The consensus reverted to arrows.

**`:` + `then` avoids all of this.** `:` is not an expression operator (no collision with anything), and `then` is an unambiguous English-word boundary. Guards compose cleanly between them — `and` conditions after the pattern, before `then`. Returning a lambda is clear: `: Ok(num) and num > 3 then |num| num + 100`. The cost is a few extra characters per arm, but the syntax stays consistent regardless of complexity — simple arms and dense real-world code read the same way.

```ruby
# Dense real-world code stays readable
if (method, path)
    : (GET, "/articles/${slug}") then auth_optional!(|opt_user_id| get!(opt_user_id, slug))
    : (POST, "/articles") then auth_json!(|user_id, article| insert!(user_id, article))
    : (DELETE, "/articles/${slug}") then auth!(|user_id| delete!(user_id, slug))
```

> Why `or` for or-patterns instead of `|`?

`or` pairs naturally with `and` for guards — keywords for logic (`and`, `or`), symbols for bitwise operations (`&`, `|`, `^`). It also avoids visual clashing in arm bodies that use bitwise `|`. And it reads like English: `: Circle(r) or Sphere(r) and r > 0 then ...` is "if it's a Circle or Sphere(r) when r > 0, then..."

`|` would be triple-duty: lambda delimiter (`|x| x + 1`), bitwise OR (`a | b`), and or-patterns. Using `or` for patterns reduces `|` to dual-duty with clean positional disambiguation. Roc's community explored using `|` for both alternatives and lambda args — the interaction is genuinely ambiguous: `|Blue | Red | Green| Yellow` could be two branches or one branch with three alternatives. They settled on `or` for the same reasons.

`or` also enables or-patterns inside lambda args (where `|` would be structurally impossible): `|Admin({ email, .. }) or Guest(email)| email` — the `or` is inside the `||` delimiters, so there's no confusion about what's a pattern boundary and what's an alternative.

The tradeoff: `|` is more visually sparse and scans better at line starts in multiline patterns. But Tempo already uses `then` instead of `->` and `and` for guards — it's a keyword-centric design where `or` fits naturally. In multiline or-patterns, `:` at line start always signals a new arm, so indented `or` continuations are unambiguous:

```ruby
if shape
    : VeryLongPattern(x, y, z)
      or AnotherLongPattern(a, b, c) then result
    : Other then other_result
```

> Why keyword-centric syntax instead of minimal punctuation?

A design with fewer syntactic primitives (reusing `|` and `{}` for everything) seems like it should be easier to learn — fewer symbols to memorize. But in practice, visual variety is what makes code scannable. When everything looks the same, you can't tell what you're looking at without reading carefully. Roc's community found this firsthand: `|pattern| { expr }` made match arms, lambdas, and blocks visually indistinguishable at a glance.

Keywords like `:`, `then`, `and`, `or` act as visual anchors — each one means something specific and is easy to spot. This matters more in real codebases than in minimal examples. The tradeoff is more characters per line, but the payoff is that structure is visible without syntax highlighting.

> Why does `and` bind tighter than `or` in arms?

To match boolean expression precedence. In expressions, `a or b and c` is `a or (b and c)`. If arms had `or` binding tighter (consuming patterns first, then `and` starting the guard), `: Foo(x) or Bar(x) and x > 10` would parse as `(Foo(x) or Bar(x)) and (x > 10)` — the opposite of what `and`/`or` precedence means everywhere else. Making `and` bind tighter keeps precedence consistent: the guard attaches to its nearest pattern. The tradeoff: boolean `or` inside guards requires parens (`and (x > 0 or x < -10)`), but this is rare and explicit.

> Why `and` chains instead of nesting?

Successive destructuring uses `and` to chain pattern tests left-to-right. This replaces what other languages need nested `match`/`case` for. Each arm is self-contained — no indentation sensitivity needed. Arms with shared prefixes may appear to repeat work, but because all functions are pure, the compiler deduplicates shared subexpressions (Maranget-style decision tree compilation).

## Nesting

Nesting `if` inside an arm result creates a dangling-else style ambiguity — `:` and `else` could belong to the inner or outer `if`. The rule: **`:` and `else` greedily bind to the nearest `if`**. Parens override when needed.

```ruby
# `: Baz` binds to inner `if y` (greedy)
if x
    : Foo(y) then if y
        : Bar(z) then use(z)
        : Baz then fallback()

# Parens close the inner `if`
if x
    : Foo(y) then (if y
        : Bar(z) then use(z)
        : Qux then other())
    : Baz then fallback()

# Flat `and` chains avoid the ambiguity entirely
if x
    : Foo(y) and y is Bar(z) then use(z)
    : Foo(y) and y is Qux then other()
    : Baz then fallback()
```

In practice, `and` chains flatten most nesting so the ambiguity rarely arises. A formatter makes the grouping visible by indenting arms under their `if`.

## Exhaustiveness

Multi-arm matching (`:`) always requires exhaustiveness — cover all cases or add `else`. This applies even when arms use `return`:

```ruby
# Error — non-exhaustive, what about Err?
if x
    : Ok(val) return val

# Ok — all cases covered
if x
    : Ok(val) return val
    : Err(e) then handle(e)
```

The standalone `if expr return expr` form is different — it's a guard clause, not multi-arm dispatch. Guard clauses fall through by design:

```ruby
# Ok — guard clause, falls through to code below
if x is Ok(val) return val
```

This distinction means `if x is Ok(val) return val` and `if x : Ok(val) return val` are NOT the same thing. The `is` form is a guard clause (falls through). The `:` form is a one-arm multi-arm match (requires exhaustiveness). There's no redundancy — each form has a distinct purpose.

## Footguns

**Dangling-else with nested `if`** — `:` and `else` greedily bind to the nearest `if`. Fix: parens or `and` chains. A formatter makes this visible.
