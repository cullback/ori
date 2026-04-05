# Fold

`fold` is the only recursion primitive. It performs structural recursion over inductive data types — processing values bottom-up, replacing each constructor with a computation. No general recursion, no fixpoints. All programs terminate by construction.

**Keywords:** `fold` (1 new keyword, added to the existing set).

## Syntax

```ruby
fold expr
    : Constructor(fields) then body
    : Constructor(fields) then body
    ...
```

Same arm syntax as `if` multi-arm matching (`: Pattern then body`). The semantic difference: **in fold arms, pattern variables for recursive fields bind to the fold result, not the original value.** Non-recursive fields bind to the original value as usual.

## Examples

### Nat to I64

```ruby
Nat : [Zero, Succ(Nat)]

to_i64 : Nat -> I64
to_i64 = |n| fold n
    : Zero then 0
    : Succ(prev) then prev + 1
```

`prev` is the fold result (an I64), not the predecessor Nat. Evaluation of `to_i64(Succ(Succ(Zero)))`:

- `Zero` → 0
- `Succ(0)` → 0 + 1 = 1
- `Succ(1)` → 1 + 1 = 2

### Tree sum

```ruby
Tree : [Leaf(I64), Branch(Tree, Tree)]

tree_sum : Tree -> I64
tree_sum = |t| fold t
    : Leaf(val) then val
    : Branch(left, right) then left + right
```

`left` and `right` are fold results (I64 sums of subtrees), not the original subtrees. `val` is the original I64 value (non-recursive field).

### List sum

```ruby
List : [Nil, Cons(I64, List)]

list_sum : List -> I64
list_sum = |xs| fold xs
    : Nil then 0
    : Cons(hd, rest) then hd + rest
```

`hd` is the original I64 head (non-recursive). `rest` is the fold result (sum of the tail), not the tail itself.

### List map (+1)

```ruby
List : [Nil, Cons(I64, List)]

map_inc : List -> List
map_inc = |xs| fold xs
    : Nil then Nil
    : Cons(hd, rest) then Cons(hd + 1, rest)
```

`rest` is the already-mapped tail. The fold rebuilds the list bottom-up with each head incremented.

### Factorial (with accumulator pair)

```ruby
Nat : [Zero, Succ(Nat)]
Pair : [MkPair(I64, I64)]

factorial : Nat -> I64
factorial = |n| (
    result = fold n
        : Zero then MkPair(0, 1)
        : Succ(rec) then
            if rec
                : MkPair(idx, f) then (
                    next = idx + 1
                    MkPair(next, next * f)
                )
    if result
        : MkPair(_, f) then f
)
```

The fold carries an `(index, factorial)` pair as its accumulator. Each `Succ` step increments the index and multiplies. This is the standard technique for computing with fold over Nat — threading state through a pair.

### Fibonacci

```ruby
Nat : [Zero, Succ(Nat)]
Pair : [MkPair(I64, I64)]

fibonacci : Nat -> I64
fibonacci = |n| (
    result = fold n
        : Zero then MkPair(0, 1)
        : Succ(rec) then
            if rec
                : MkPair(a, b) then MkPair(b, a + b)
    if result
        : MkPair(a, _) then a
)
```

## Semantics

Fold is a catamorphism. For an inductive type with constructors C1, C2, ..., `fold` replaces each constructor with a user-defined computation:

1. **Pattern match** the value's constructor tag
2. **Recursively fold** each recursive field (bottom-up)
3. **Bind** non-recursive fields to their original values and recursive fields to their fold results
4. **Evaluate** the arm body with these bindings

The original recursive subterms are not accessible to the arm body. This is what makes fold safe — you can only process things bottom-up, never inspect raw recursive structure.

### Recursive field detection

The compiler determines which fields are recursive by checking if a field's type name matches the type being defined:

```ruby
Nat : [Zero, Succ(Nat)]
#                  ^^^ recursive — same as the type being defined

List : [Nil, Cons(I64, List)]
#                 ^^^        non-recursive
#                      ^^^^  recursive

Tree : [Leaf(I64), Branch(Tree, Tree)]
#            ^^^           ^^^^  ^^^^
#        non-recursive   both recursive
```

Fields with the same type name as the enclosing type declaration are recursive. All others are non-recursive. This is a syntactic check on the type name — no type inference needed.

## Relationship to `if`

`fold` and `if` are parallel constructs with the same arm syntax:

|                | `if`                  | `fold`                                                    |
| -------------- | --------------------- | --------------------------------------------------------- |
| Purpose        | Pattern dispatch      | Structural recursion                                      |
| Arm syntax     | `: Pattern then body` | `: Pattern then body`                                     |
| Field bindings | Original values       | Non-recursive: original values. Recursive: fold results   |
| Exhaustiveness | Required (or `else`)  | Required (no `else`)                                      |
| Guards         | Supported (`and`)     | Not supported (fold always processes the whole structure) |

`if` asks "what shape is this value?" and dispatches. `fold` asks "what shape is this value?" and recursively processes it bottom-up.

## What fold compiles to

The recursion shape determines the execution strategy:

- **Fold on Nat** → counted for-loop
- **Fold on List** → while-loop
- **Fold on Tree** → parallel divide-and-conquer (independent branches are independent by construction)

This is possible because fold's structure is fully known at compile time — no dynamic dispatch, no unbounded stack growth.

## Design decisions

> Why a separate `fold` keyword instead of extending `if`?

`fold` has fundamentally different semantics from `if` — it implies bottom-up traversal and changes what pattern variables mean. Mixing fold into `if` would be confusing: the same pattern `Cons(hd, rest)` would mean different things depending on context. A separate keyword makes the semantics visible at the call site.

> Why no `else` on fold?

Fold must be exhaustive — every constructor of the type must have an arm. An `else` catch-all doesn't make sense because the algebra needs to handle each constructor's specific field structure. A wildcard can't bind the right number of fields.

> Why no access to original recursive field values?

In a catamorphism, the algebra receives non-recursive components as-is and recursive components replaced by their fold results. The original recursive subterms are not part of the interface. This is what makes fold structurally recursive — you can't "cheat" by inspecting the raw subtree. In practice, across all our Core IR test programs (factorial, fibonacci, list_sum, list_length, list_map, list_reverse, tree_sum, tree_depth, is_prime), the original recursive field value is never used.

If a future use case requires access to both the original value and the fold result, an `as` binding could be added: `: Cons(hd, rest as rest_result) then ...`. But this is speculative and not needed now.

> Why no guards in fold arms?

Guards (`and` conditions) don't make sense in fold because the fold always processes the entire structure. You can't conditionally skip a constructor — every value must be reduced. Conditional logic goes in the arm body using `if`.
