# Parser combinators

Parser combinators are a key test of the language's ergonomics. A functional language where parsers feel awkward has a problem. This note documents how Ori's features interact with parser combinator design, what works well, and where the friction lives.

## Record builders as parse specifications

Record builder syntax turns parser composition into a declaration of the output shape. The `sequence` combinator has the `map2` signature, so passing it a record literal desugars to nested sequential parsing in field order:

```ruby
# Parse "2x3x4" into { l: U64, w: U64, h: U64 }
box = Parser.sequence({
    l: natural.and_drop_right(symbol('x')),
    w: natural.and_drop_right(symbol('x')),
    h: natural,
})
```

The record literal simultaneously declares the field names, the parsers for each field, and the output type. No separate type definition, no positional field-matching bugs (Haskell's `<$>`/`<*>` problem), no builder pattern. Delimiters are consumed inline via `and_drop_right` / `and_drop_left` — the record fields map 1:1 to the output record fields.

This works because `sequence` threads input from one parser to the next — each field consumes bytes and passes the remainder. The desugaring produces nested `sequence` calls in source order, which matches parse order. See [record builders](record-builders.md#applicative-vs-sequential).

A complete example — Advent of Code 2015 Day 2, computing wrapping paper for a list of boxes:

```ruby
box = Parser.sequence({
    l: natural.and_drop_right(symbol('x')),
    w: natural.and_drop_right(symbol('x')),
    h: natural,
})

boxes = box.separated_by(symbol('\n'))

paper = |{ l, w, h }| (
    sides = [l * w, w * h, h * l]
    smallest = sides.walk(sides.first().unwrap(), |a, b| a.min(b))
    sides.walk(0, |sum, s| sum + 2 * s) + smallest
)

total = boxes.run(input)
    .map(|bs| bs.walk(0, |sum, b| sum + paper(b)))
```

The parser reads like the format: "natural, then `x`, then natural, then `x`, then natural." The record destructuring in `paper` gives named access to the parsed dimensions. No regex, no `split("x")` with index access, no separate struct definition.

## Dot dispatch as pipeline

Combinators chain through dot dispatch, reading left-to-right as a pipeline:

```ruby
digit
    .one_or_more()
    .map(|digits| digits.walk(0, |acc, d| acc * 10 + (d - '0').to_u64()))
```

Compare Haskell, where the same composition reads inside-out:

```haskell
fmap (\ds -> foldl' (\acc d -> acc * 10 + digitToInt d) 0 ds) (some digit)
```

Ori's method syntax gives parser combinators the same readability that Rust's `nom` achieves with method chaining, without macros.

## Recursive grammars

Non-recursive parsers compose freely — `and_then`, `or_else`, `map`, `zero_or_more` are all plain function composition. Recursive grammars (expressions, nested JSON, S-expressions) hit a wall: pure Ori has no self-referential bindings and no general recursion.

### The fixpoint combinator

`fixpoint` iterates a parser transformer to a bounded depth:

```ruby
fixpoint : I32, (Parser(a) -> Parser(a)) -> Parser(a)
fixpoint = |depth, f|
    List.range(0, depth)
        .walk(Parser.fail("recursion depth exceeded"), |acc, _| f(acc))
```

Usage for arithmetic expressions:

```ruby
expr = Parser.fixpoint(256, |recurse|
    term.and_drop_right(symbol('+'))
        .and_then(recurse)
        .map(|(x, y)| x + y)
        .or_else(term))
```

`fixpoint(256, f)` builds `f(f(f(...f(fail)...)))` — 256 layers of the parser transformer applied to a base-case failure parser. The result handles up to 256 levels of nesting.

### Allocation cost

`fixpoint` eagerly allocates the full closure chain at construction time. `fixpoint(256, f)` creates 256 closures before any input arrives. Each closure captures the previous parser (a function pointer plus environment). This happens once per parser construction, not once per parse — build the parser once, reuse it across inputs, and the construction cost amortizes to nothing.

In a lazy language (Haskell), the recursive knot ties through a thunk — zero up-front cost, allocations only as deep as the actual input nests. Ori's strict evaluation requires paying up front for the bounded depth.

The compiler could in principle inline the closure chain and collapse it, since `f` is pure and known at compile time. Whether this happens in practice depends on the inliner's budget and the complexity of `f`.

### Table-driven alternative

A table-driven parser (LR/LL) avoids `fixpoint` entirely. The "recursion" lives in an explicit stack, and the driver is a linear fold over the token stream:

```ruby
parse = |tokens, table|
    tokens.walk_until(initial_stack, |stack, token|
        if table.action(stack.top(), token)
            : Shift(state) then Continue(stack.push(state))
            : Reduce(rule) then Continue(apply_reduction(stack, rule))
            : Accept then Break(stack)
            : Error then Break(stack))
```

No closures, no bounded depth, no `fixpoint`. The tradeoff: the grammar becomes implicit in the table rather than readable in the code, and you need a parser generator to produce the table.

### What fold can and can't parse

`fold` performs structural recursion over existing data. Parsing *constructs* structure from flat input — the recursion depends on what byte comes next, not on the shape of an inductive type.

Fold can drive a state machine over a token stream (fold the list, accumulate state), which covers regular grammars. Context-free grammars need a stack, which means either `fixpoint` (combinator style) or an explicit stack in a `walk` (table-driven style). Fold alone cannot express recursive descent.

## Comparison with Rust's nom

Ori's combinator library covers the same surface as `nom`: sequential composition, alternatives, repetition, mapping. The API reads similarly thanks to dot dispatch. Two differences matter for performance:

**Closures vs. zero-cost abstractions.** `nom` compiles parser combinators to tight loops through monomorphization and inlining. Ori's monomorphizer and lambda set resolution should achieve similar results for non-recursive parsers — each combinator specializes to its concrete closure type, and the defunctionalizer replaces indirect calls with direct dispatch.

**Recursive parsers.** `nom` uses Rust's native recursion. Ori uses `fixpoint`, which pre-allocates a closure chain. For shallow nesting (JSON objects 10 levels deep), the overhead is negligible. For deep nesting (256+ levels of S-expressions), the up-front allocation cost becomes measurable relative to `nom`'s zero-cost stack recursion. The practical gap depends on whether the compiler collapses the closure chain.

## Open questions

**Can the compiler optimize `fixpoint`?** The closure chain is a known pattern — `f` applied N times to a base case. A compiler that recognizes this could replace it with a loop and a depth counter at runtime, eliminating the up-front allocation entirely. Whether this optimization is worth implementing depends on how much parser-heavy code exists in practice.

**Should `fixpoint` be a compiler intrinsic?** If the optimization above proves difficult as a general transformation, `fixpoint` could be a recognized builtin that the compiler lowers directly to a loop with a depth check. This trades generality for guaranteed performance.

**Is `fixpoint` the right abstraction?** `fixpoint` works but feels like a workaround for the lack of lazy evaluation or recursive bindings. Alternative designs worth exploring:
- A `lazy` combinator that defers parser construction (requires compiler support for thunks)
- A `grammar` block that ties recursive knots at the syntax level (new language feature)
- Accepting that table-driven parsing is the right approach for recursive grammars in a strict total language, and investing in parser generator tooling instead

## Design rationale

> Why does this matter for a language like Ori?

Parser combinators are a litmus test for functional language ergonomics. Haskell's `parsec`, OCaml's `angstrom`, Rust's `nom`, Scala's `fastparse` — every functional-leaning language develops a combinator library, and its quality shapes how programmers perceive the language. Ori's record builder syntax, dot dispatch, and opaque types combine to produce a combinator API that reads cleanly for non-recursive grammars. The recursive grammar story needs more work.

> Why not just use parser generators?

Parser generators (yacc, menhir, tree-sitter) are the right tool for large, stable grammars — programming languages, data formats with RFCs. Combinators are the right tool for small, evolving, or embedded grammars — config files, DSLs, protocol messages, one-off data extraction. A language that only supports generators pushes users toward heavyweight tooling for lightweight problems.

> Why document this as a language-level concern?

The friction with recursive parsers comes from the language's core design (total functions, strict evaluation, no self-referential bindings), not from a library limitation. Any solution — compiler optimization of `fixpoint`, a `lazy` primitive, a `grammar` block — requires language-level decisions. Keeping the analysis in `gold/` alongside the other design notes ensures the tradeoffs stay visible.
