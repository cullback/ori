# Constraints

## Where clauses

Constraints go on functions, not type declarations — a `Dict` can hold any key type; only `get`/`insert` need it to be hashable:

```ruby
deduplicate : List(a) -> List(a)
    where [a.Hash]

equals : List(elem), List(elem) -> Bool
    where [elem.equals : elem, elem -> Bool]
```

Named (`a.Hash`) and anonymous (`elem.equals : ...`) constraints mix freely in the same `where` clause.

> Why declarative, not computational?

Languages with type-level computation (Rust's associated types, Haskell's type families) create a parallel programming language at the type level. Keeping constraints declarative means the type level stays small — there's no second language to learn.

## Named constraints

Named bundles that expand inline — not a separate language feature:

```ruby
a.Eq      : [a.equals : a, a -> Bool]
a.Hash    : [a.Eq, a.hash : a -> U64]
a.Compare : [a.Eq, a.compare : a, a -> Order]

a.Encode(fmt) : [a.to_encoder : a -> Encoder(fmt)]
a.Decode(fmt) : [a.decoder : Decoder(a, fmt)]
```

Constraints compose — `Hash` includes `Eq` and adds `hash`. Extra type variables go in parens: `where [a.Encode(Json)]`.

A type satisfies a constraint if it has the required functions — structural, not nominal. No `impl` blocks, no orphan rules, no coherence checking. If the methods exist, the type qualifies.

> Why structural instead of nominal?

Nominal conformance (Rust traits, Haskell typeclasses) requires `impl` declarations and coherence rules — type-level pattern matching duplicated across two languages. Structural conformance eliminates this layer entirely. Go's interfaces validate this approach. The tradeoff: you can't have two implementations of the same constraint for one type, which is rarely needed and usually a design smell.

This also eliminates the ecosystem lock-in that Rust's coherence and orphan rules create. In Rust, if a foundational crate (like `serde`) defines a trait, and a better alternative appears, every downstream crate needs updating — and the orphan rules prevent third parties from bridging the gap (`impl ForeignTrait for ForeignType` is illegal). The first mover wins by language fiat. In Ori, there are no `impl` blocks to fight over — a type satisfies a constraint by having the right functions, regardless of where the constraint was defined. No orphan rules means no artificial gatekeeping.

The one-implementation-per-type model also prevents the HashMap problem: in Rust, without coherence, different crates could provide conflicting `Hash` implementations for the same type, producing nonsensical results when collections are passed between them. In Ori, `hash` is defined once in the type's module — there's no mechanism for conflicting implementations to exist.

Similarly, Rust's associated types create soundness risks without coherence — conflicting associated type impls can enable transmutation in safe code. Ori avoids this entirely by keeping named constraints as structural bundles that expand inline, with no type-level computation to exploit.

### Numeric constraints

```ruby
a.Num : [
    a.add : a, a -> a,
    a.sub : a, a -> a,
    a.mul : a, a -> a,
    a.neg : a -> a,
    a.Eq, a.Compare,
]

a.Int  : [a.Num, a.div : a, a -> a, a.mod : a, a -> a]
a.Frac : [a.Num, a.div : a, a -> a]
a.Bits : [a.bit_and : a, a -> a, a.bit_or : a, a -> a, a.bit_xor : a, a -> a]
```

Number literals are polymorphic — `42` has type `a where [a.Num]`, resolved by context. Defaults: integers → I32, decimals → F64. See [let-generalization](let-generalization.md) for which bindings are generalized and which infer a single concrete type.

## Design rationale

> Why constraints on functions, not type declarations?

A `Dict(key, val)` can store any key type — it's just a data structure. Only specific *operations* need the key to be hashable. If constraints lived on the type, every function touching a `Dict` would silently carry those constraints, even ones like `len` that don't need them. Worse, you'd have to understand a type's definition to know whether a type variable is constrained — constraints would be invisible at the use site.

The rule: all constraints on type variables are visible in the function's own type signature. You should never need to chase a type definition to discover a hidden constraint.

```ruby
# Dict doesn't constrain key — it's just a container
Dict(key, val) := ...

# Only the functions that need it say so
insert : Dict(key, val), key, val -> Dict(key, val)
    where [key.Hash]

get : Dict(key, val), key -> Result(val, [KeyNotFound])
    where [key.Hash]

# len doesn't need hashable keys — no where clause
len : Dict(key, val) -> I32
```

> Why are anonymous constraints the primitive?

Named constraints like `a.Hash` are convenient, but they're sugar — they expand to `[a.Eq, a.hash : a -> U64]`. The anonymous form is what the compiler actually works with, and what the REPL must print for inferred types:

```ruby
>> |a, b| a.foo(b)
# REPL prints the inferred type:
a, b -> c where [a.foo : a, b -> c]
```

No named constraint is needed — the compiler infers exactly which functions the code uses and reports them. Named constraints are a convenience for humans writing annotations, not a requirement of the type system.

This means named and anonymous constraints mix freely in the same where clause:

```ruby
deduplicate : List(a) -> List(a)
    where [a.Hash, a.to_str : a -> Str]
```

> Why one type variable per constraint?

Named constraints have exactly one "dispatching" type variable — the type whose module provides the functions. The `a.Eq` syntax makes this structurally obvious: `a` is the variable, `Eq` is the constraint. You can't accidentally write a constraint that dispatches on two types.

This falls out of how constraints work: `a.Hash` means "the module for `a` has `equals` and `hash`." There's one module per type, so there's one variable per constraint. Extra type variables can appear inside the constraint's functions (like the `fmt` in `a.Encode(fmt)`), but those are parameters, not dispatching variables.

```ruby
a.Eq           # one variable — the type that must have equals
a.Encode(fmt)  # one dispatching variable (a), one parameter (fmt)
```

> Why not put constraints inline in type parameters?

An alternative design puts constraints directly in the type position: `List(Hashable(elem))` instead of `List(elem) ... where [elem.Hash]`. This was explored and rejected because:

- Constraints aren't types. `Hashable(elem)` looks like a type constructor (like `List(elem)`) but it's not — it doesn't change the type, it restricts it. The visual similarity is misleading.
- Repetition. Every occurrence of the variable needs the constraint: `List(Hashable(elem)), List(Hashable(elem)) -> List(Hashable(elem))`. With where clauses, you write it once.
- Composition is ugly. A hashable and equatable key becomes `Hashable(Equatable(key))` — nesting constraints suggests an ordering that doesn't exist.
- Ambiguity. Is `Hashable` a type or a constraint? You can't tell without checking its definition.

Where clauses keep constraints separate from the type structure, state each constraint once, and make the distinction between types and constraints visually clear.

> Why square brackets for where clauses?

The `where [...]` syntax solves a parsing problem: how does the compiler know where the where clause ends and the next statement begins? Without delimiters, a trailing comma or newline becomes ambiguous. Square brackets make the boundary explicit, support trailing commas naturally, and parallel the `[...]` syntax used for tag union declarations — both are lists of items.

```ruby
insert : Dict(key, val), key, val -> Dict(key, val)
    where [key.Eq, key.hash : key -> U64]

# Multi-line with trailing comma
insert : Dict(key, val), key, val -> Dict(key, val)
    where [
        key.Eq,
        key.hash : key -> U64,
    ]
```
