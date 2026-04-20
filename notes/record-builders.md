# Record builders

Record builders convert a record of wrapped values into a wrapped record. When a function with the `map2` signature is called with a record literal instead of two arguments, the compiler nests the calls automatically.

```ruby
# Normal call — two parsers, one combining function
CliParser.sequence(parser_a, parser_b, |a, b| { a, b })

# Record builder — same function, record of parsers
CliParser.sequence({
    name: Opt.str({ long: "name" }),
    count: Opt.maybe_u64({ long: "count" }),
})
# : CliParser({ name: Str, count: U64 })
```

No special methods, no reserved names. Any function with the right shape works.

## The rule

> When a function with signature `F(a), F(b), (a, b -> c) -> F(c)` is called with a single record literal where every field has type `F(something)`, the compiler desugars to nested calls.

This is safe because Ori has no currying — calling a 3-argument function with 1 argument is always a type error. The record builder desugaring resolves what would otherwise fail. There is no ambiguity.

## Desugaring

The compiler nests calls in source order (first field outermost), building tuples at intermediate steps and constructing the record in the final combining function:

```ruby
# User writes:
CliParser.sequence({
    name: Opt.str({ long: "name" }),
    count: Opt.maybe_u64({ long: "count" }),
    verbose: Opt.flag({ long: "verbose" }),
})

# Compiler generates:
CliParser.sequence(
    Opt.str({ long: "name" }),
    CliParser.sequence(
        Opt.maybe_u64({ long: "count" }),
        Opt.flag({ long: "verbose" }),
        |count, verbose| (count, verbose),
    ),
    |name, (count, verbose)| { name, count, verbose },
)
```

The nested tuples are an implementation detail — the user never sees them. The result type is `CliParser({ name: Str, count: U64, verbose: Bool })`.

## Use cases

The pattern appears anywhere you build a composite result from named parts. Each library defines its own function with the `map2` shape — the name reflects the library's semantics:

```ruby
# CLI argument parsing
config = CliParser.sequence({
    name: Opt.str({ long: "name" }),
    count: Opt.maybe_u64({ long: "count" }),
}).run(args)

# Custom JSON decoding
user = Json.all_fields({
    name: Json.field("name", Json.str),
    age: Json.field("age", Json.i32),
}).decode(bytes)

# Random generation
user = Gen.all({
    name: Gen.alpha(10),
    age: Gen.range(18, 99),
}).run(seed)

# Form validation (collects all errors, not just the first)
user = Validate.all({
    name: required(input.name),
    age: in_range(input.age, 0, 150),
}).check()

# Parallel HTTP requests
responses = Http.parallel({
    users: Http.get("/users"),
    posts: Http.get("/posts"),
}).run!()

# Parser combinators (sequential — field order is parse order)
point = Parser.sequence({
    x: natural.and_drop_right(symbol(',')),
    y: natural,
}).run(input)
```

## Multiple functions per type

Because the feature is triggered by the function signature, not a special method name, a single type can offer multiple strategies:

```ruby
# Sequential — parsers run left to right
CliParser.sequence({
    name: Opt.str({ long: "name" }),
    verbose: Opt.flag({ long: "verbose" }),
})

# First match — tries each parser, takes the first success
CliParser.first_of({
    by_name: Opt.str({ long: "name" }),
    by_id: Opt.u64({ long: "id" }),
})
```

Both functions have signature `CliParser(a), CliParser(b), (a, b -> c) -> CliParser(c)` but different implementations. The caller picks the strategy by calling the right function.

## The record literal is the specification

The record literal simultaneously declares what you want and types what you get:

```ruby
CliParser.sequence({ name: Opt.str(...), count: Opt.maybe_u64(...) })
# Input:  { name: CliParser(Str), count: CliParser(U64) }
# Output: CliParser({ name: Str, count: U64 })
```

No separate type definition. No runtime assembly. Missing a field is a compile-time type error. Adding a field to the record literal automatically extends the output type.

## Field order follows source order

Records are unordered — `{ x: I32, y: I32 }` and `{ y: I32, x: I32 }` are the same type, the compiler is free to reorder field evaluation in record literals, and memory layout is an optimization choice.

Record builder desugaring is a syntax transformation. The compiler reads the fields in the order they appear in the source and generates nested `map2` calls in that order. This means:

- Reordering fields in the record builder changes the generated call nesting
- Libraries that consume input sequentially (parser combinators, positional args) work correctly
- Libraries where order doesn't matter (JSON decoding, named CLI flags) are unaffected

This doesn't impose any ordering on record literals in general — it's purely how the desugaring reads the source.

### Applicative vs sequential

Some record builders are order-independent — each field sees the same input:

```ruby
# All fields search the same args list — order irrelevant
config = ArgParser.sequence({
    name: Opt.str("name"),
    verbose: Opt.flag("verbose"),
})

# All fields look up by key — order irrelevant
user = Json.decode({
    name: Json.field("name", Json.str),
    age: Json.field("age", Json.i32),
})
```

Others are sequential — each field consumes input, passing the remainder to the next:

```ruby
# Parses "123,456" left to right — order matters
point = Parser.sequence({
    x: natural.and_drop_right(symbol(',')),
    y: natural,
})

# Positional args — field position determines arg position
parser = ArgParser.sequence({
    command: Arg.str(),    # first positional
    file: Arg.str(),       # second positional
})
```

Both work with the same desugaring. The `map2` implementation decides whether to thread state (sequential) or share input (applicative). Source order makes both possible.

For composition that depends on a previous field's **value** (not just its position), use `?` chaining:

```ruby
# Monadic — body format depends on header
(header, input) = parse_header(input)?
(body, input) = parse_body(header.format, input)?
```

Record builders combine independent computations (applicative or sequential). `?` chaining threads values through dependent steps.

## Why not the builder pattern?

The traditional builder pattern accumulates fields incrementally through method chaining:

```ruby
# Builder — incremental construction
config = CliBuilder.new()
    .name(Opt.str({ long: "name" }))
    .count(Opt.maybe_u64({ long: "count" }))
    .build(args)
```

This has three problems in a statically typed pure functional language:

**Missing fields are detected late.** The builder accumulates state across calls. Checking whether all required fields were set is either done at runtime in `.build()` — returning `Result` or panicking — or tracked via typestate, which requires a combinatorial explosion of intermediate types to encode which fields have been set.

**The output type isn't inferred from what you wrote.** A builder can't derive `{ name: Str, count: U64 }` from the chain of `.name()`, `.count()` calls. Either you define the target type separately, or the builder is stringly-typed and loses type safety.

**Mutable state.** Each builder method mutates internal state, which conflicts with immutable values. You'd need to thread the builder through or use a mutable reference, neither of which fits a pure functional language.

With record builders, the record literal IS the specification. The compiler sees all fields at once, infers the output type, and checks completeness — all at compile time, with no separate builder type.

## Why not `?` with `Result`?

The try operator handles sequential, short-circuiting composition:

```ruby
config = {
    name: Opt.str({ long: "name" }).parse(args)?,
    count: Opt.maybe_u64({ long: "count" }).parse(args)?,
}
```

This works when the context is `Result` and short-circuiting on the first error is acceptable. Record builders handle cases where `?` doesn't apply:

- **Collecting all errors** — a form validator reports every invalid field, not just the first
- **Parallel execution** — the combined form knows all fields upfront, enabling batching
- **Inspectable descriptions** — a CLI parser generates `--help` from the combined description before executing
- **Non-Result contexts** — random generators, decoders, and parsers aren't `Result` types

If `?` covers the use case, use `?`. Record builders are for when the context isn't `Result` or when you need the whole description before executing.

## Why not Roc's `<-` syntax?

Roc uses `{ combiner_fn <- field: expr }` — the combiner function is named explicitly in a new syntactic form:

```roc
{ combine_matchers <-
    users: exact_segment("users"),
    user_id: u64_segment,
    tab: any_segment,
}
```

Ori's approach needs no new syntax. A record literal passed to a `map2`-shaped function triggers the desugaring. The function call IS the builder — you see the function name, you know the strategy.

Roc's `<-` allows any function to be the combiner, which Ori also achieves — but through overloaded calling convention (record literal vs normal args) rather than new syntax. The result is more compact and reuses existing language constructs.

## Why not Haskell's Applicative operators?

Haskell builds records using `<$>` and `<*>`:

```haskell
data Config = Config { name :: String, count :: Int, verbose :: Bool }

configParser :: Parser Config
configParser = Config
  <$> strOption (long "name")
  <*> option auto (long "count")
  <*> switch (long "verbose")
```

Three problems ([well described by Gabriella Gonzalez](https://haskellforall.com/2024/05/prefer-do-notation-over-applicative)):

**Silent order bugs.** Fields are positional — swapping `name` and `count` in the parser silently reads values into the wrong fields. Ori's named fields make this impossible.

**Separate type definition.** The `Config` type and the parser must be kept in sync manually. Ori infers the output type from the record literal.

**Cryptic errors.** Adding a field to `Config` produces a currying type error, not "missing field." Ori reports the missing field directly.

Haskell's workaround is `ApplicativeDo` — a GHC extension that analyzes `do` blocks to detect independent computations and desugar to Applicative. Ori's record builder desugaring achieves the same thing more simply: the compiler sees all fields at once in the record literal and nests the `map2` calls mechanically. No extension, no operators, no dependency analysis.

## Error messages

When the function doesn't have the right signature:

```
-- NOT A RECORD BUILDER --

This function is called with a record literal, but its signature
doesn't match the record builder pattern:

  5 |     MyModule.process({ name: foo(...), age: bar(...) })

`process` has signature:

    process : MyType(a), Str -> MyType(a)

Record builders require:

    F(a), F(b), (a, b -> c) -> F(c)
```

When fields have different wrapper types:

```
-- MIXED TYPES IN RECORD BUILDER --

The fields in this record have different wrapper types:

  5 |     CliParser.sequence({ name: Opt.str(...), count: Gen.range(...) })

  `name` has type CliParser(Str)
  `count` has type Gen(U64)

All fields must have the same wrapper type for record builder
desugaring.
```
