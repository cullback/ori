# Comments

`#` is the only comment syntax. No block comments. Position determines whether a comment is a doc comment or a regular comment.

```ruby
# Doc comment — directly above a binding.
# Supports markdown.
parse : Str -> Result(I32, [ParseErr(Str)])
parse = |s| ...

x = foo()  # regular comment — end of line
# regular comment — inside a function body
y = bar()
```

## Doc comments

A `#` comment directly above a `name :` or `name =` line is a doc comment. It attaches to the next binding and is included in generated documentation. Markdown is supported — headers, code blocks, links, inline code.

```ruby
# Parses a string into an integer.
#
# Returns `Err(ParseErr)` if the string contains non-digit characters.
#
# ```
# parse("42")   # Ok(42)
# parse("nope") # Err(ParseErr("nope"))
# ```
parse : Str -> Result(I32, [ParseErr(Str)])
parse = |s| ...
```

### Placement

A binding is the type annotation + definition pair (or whichever is present). The doc comment goes above the first line:

```ruby
# Both annotation and definition — doc goes above annotation.
parse : Str -> Result(I32, [ParseErr(Str)])
parse = |s| ...

# Definition only — doc goes above definition.
double = |x| x * 2

# Derivation only — doc goes above signature.
equals : _
```

The annotation and definition are one unit. A comment between them is an error:

```ruby
# This is the doc comment.
parse : Str -> Result(I32, [ParseErr(Str)])
# ERROR — nothing goes between annotation and definition.
parse = |s| ...
```

### Doc tests

Code blocks in doc comments are verified by the compiler. `ori test` runs them alongside `expect` tests:

```ruby
# Clamps a value to the given range.
#
# ```
# clamp(5, 1, 10)   # 5
# clamp(-3, 0, 100)  # 0
# clamp(999, 0, 100) # 100
# ```
clamp : I32, I32, I32 -> I32
clamp = |val, lo, hi|
    if val < lo then lo
    else if val > hi then hi
    else val
```

Doc tests are an especially good fit for Ori. The conventional wisdom (from Rust, Python, Elixir) is that doc tests work best for pure functions with simple inputs — stateful code requires too much setup scaffolding. Since Ori is pure by default, doc tests cover a much larger percentage of the codebase than in other languages.

## Regular comments

Any `#` that is not directly above a binding is a regular comment. Stripped from compiled output, not included in generated docs.

```ruby
process = |items| (
    # Filter out negatives first
    filtered = items.keep_if(|x| x > 0)
    filtered.map(|x| x * 2)  # double each remaining item
)
```

## Design rationale

> Why not separate syntax for doc comments (`##`, `///`)?

A comment above a function is a docstring — there's no practical reason to write a non-doc comment in that position. TODOs and hacks should live inside the function body or in a ticket, not above the declaration. One syntax means no decision fatigue about "should this be `#` or `##`?" Position-based semantics keep the grammar simple and the rule memorable.

> Why no block comments (`/* */`, `{- -}`)?

Block comments introduce a design trap around nesting. C-style `/* */` can't comment out code containing other block comments (the first `*/` closes everything). Nested block comments (Haskell's `{- -}`, Rust's `/* */`) fix this but break when strings contain comment-like sequences — Haskell's `"{-}"` inside a block comment causes premature termination because the lexer doesn't fully parse strings within comments. Every block comment design either fails to nest or fails at string edge cases.

Line-only comments also reduce lexer state. The lexer already tracks one bit of multi-line state for `"""` strings, but adding block comments would introduce a second independent multi-line state that interacts badly with the first (block comments containing string delimiters, strings containing comment delimiters). Keeping comments line-scoped means only strings require cross-line tracking.

Modern editors toggle `#` prefixes on selected blocks trivially, removing the convenience argument. Zig, Ada, Python, and Erlang all lack block comments and manage fine.

> Why `#` instead of `//`?

`#` is consistent with the Ruby-influenced surface syntax and doesn't conflict with any operator. `//` would collide with potential future use (integer division, path separators in imports) and reads as "empty regex" in some contexts.
