# Fold

`fold` is the only recursion primitive. It performs structural recursion over inductive data types — processing values bottom-up, replacing each constructor with a computation. No general recursion, no fixpoints. All pure functions terminate by construction.

**Keywords:** `fold` (1 new keyword, added to the existing set).

## Syntax

```ruby
fold expr
    : Constructor(fields) then body
    : Constructor(fields) then body
    ...
```

Same arm syntax as `if` multi-arm matching — guards (`and`), or-patterns (`or`), and early return (`return`) all work identically. The semantic difference: **in fold arms, pattern variables for recursive fields bind to the fold result, not the original value.** Non-recursive fields bind to the original value as usual.

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

### Tree depth

```ruby
Tree : [Leaf(I64), Branch(Tree, Tree)]

tree_depth : Tree -> I64
tree_depth = |t| fold t
    : Leaf(_) then 1
    : Branch(left, right) then 1 + max(left, right)
```

`left` and `right` are fold results (depths of subtrees). The fold computes the depth bottom-up — the compiler can evaluate branches in parallel since they're independent by construction.

### List reverse

```ruby
List : [Nil, Cons(I64, List)]

reverse : List -> List
reverse = |xs| fold xs
    : Nil then Nil
    : Cons(hd, rest) then append(rest, Cons(hd, Nil))
```

`rest` is the already-reversed tail. The fold rebuilds the list bottom-up, appending each head to the end of the reversed tail.

### Tree search (early return)

```ruby
Tree : [Leaf(I64), Branch(Tree, Tree)]

find : Tree, I64 -> Result(I64, [NotFound])
find = |t, target| fold t
    : Leaf(val) and val == target return Ok(val)
    : Leaf(_) then Err(NotFound)
    : Branch(left, _) and left is Ok(_) return left
    : Branch(_, right) then right
```

`return` exits the enclosing function. The compiler evaluates recursive fields on demand — `left` is checked before `right` is computed, so if the left subtree contains the target, the right subtree is never traversed. This gives DFS with genuine short-circuiting. See [demand-driven evaluation](#demand-driven-evaluation).

### Or-patterns and guards

```ruby
Expr : [Num(I64), Neg(Expr), Add(Expr, Expr), Mul(Expr, Expr)]

# Or-patterns — same handling for Add and Mul
count_ops : Expr -> I64
count_ops = |e| fold e
    : Num(_) then 0
    : Neg(inner) then inner
    : Add(l, r) or Mul(l, r) then 1 + l + r

# Guards — conditional logic on field values
eval : Expr -> I64
eval = |e| fold e
    : Num(n) then n
    : Neg(inner) then -inner
    : Add(l, r) then l + r
    : Mul(_, r) and r == 0 then 0
    : Mul(l, _) and l == 0 then 0
    : Mul(l, r) then l * r
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

`fold` is multi-arm `if` with two differences: recursive field rewriting and demand-driven evaluation. The arm grammar is identical — guards, or-patterns, and `return` all work the same way.

|                | `if`                        | `fold`                                                    |
| -------------- | --------------------------- | --------------------------------------------------------- |
| Arm syntax     | `: Pattern then body`       | `: Pattern then body` (identical)                         |
| Guards         | `and condition`             | `and condition` (identical)                               |
| Or-patterns    | `or Pattern`                | `or Pattern` (identical)                                  |
| Early return   | `return expr`               | `return expr` (identical — exits enclosing function)      |
| Field bindings | Original values             | Non-recursive: original. Recursive: fold results          |
| Exhaustiveness | Required (or `else`)        | Required (no `else`)                                      |
| Evaluation     | Strict                      | Demand-driven (recursive fields evaluated when referenced)|
| Extra forms    | Boolean, guard clause, `is` | — (always multi-arm)                                      |

`if` asks "what shape is this value?" and dispatches. `fold` asks "what shape is this value?" and recursively processes it bottom-up. The extra `if` forms (boolean conditional, guard clause, inline `is`) don't apply to fold — fold is always multi-arm pattern dispatch over constructors.

## Demand-driven evaluation

Fold evaluates recursive fields when first referenced in the arm body. If an arm returns without referencing a recursive field's fold result, that subtree is not traversed.

This is semantically equivalent to eager bottom-up evaluation — since fold bodies are pure, skipping an unused computation produces the same result. But the performance difference matters: tree search becomes O(k) (nodes visited before finding the target) instead of O(n) (every node).

```ruby
find = |t, target| fold t
    : Leaf(val) and val == target return Ok(val)
    : Leaf(_) then Err(NotFound)
    : Branch(left, _) and left is Ok(_) return left
    : Branch(_, right) then right
```

The compiler generates:

1. Fold left subtree
2. Check if `left` is `Ok` — if so, return immediately (right subtree never touched)
3. Only if needed: fold right subtree
4. Return `right`

This is DFS with short-circuiting. The demand-driven rule means `return` in fold does what it looks like — it genuinely skips work, not just the final combination step.

## What fold compiles to

The recursion shape determines the execution strategy:

- **Fold on Nat** → counted for-loop
- **Fold on List** → while-loop
- **Fold on Tree** → parallel divide-and-conquer (independent branches are independent by construction)

This is possible because fold's structure is fully known at compile time — no dynamic dispatch, no unbounded stack growth.

## Bounded iteration

Some algorithms need iteration with data-dependent termination — binary search, Newton's method, convergence loops. These don't map to fold over a recursive type (the iteration count depends on runtime values, not structure). The idiomatic pattern is `List.range` + `List.walk_until`:

```ruby
binary_search : List(I64), I64 -> Result(U64, [NotFound])
binary_search = |list, target| (
    List.range(0, 64)
        |> List.walk_until(Err(NotFound), (0, List.len(list)), |state, _|
            (low, high) = state
            if low >= high then Break(state)
            else (
                mid = (low + high) / 2
                val = List.get(list, mid)
                if val == target then Break((mid, mid, Ok(mid)))
                else if val < target then Continue((mid + 1, high))
                else Continue((low, mid))
            )
        )
)
```

`List.range(0, 64)` provides the fuel — at most 64 iterations, enough for any list that fits in memory. `walk_until` exits early via `Break` when the answer is found or the range is exhausted. Termination is guaranteed because you can't walk more elements than the range has.

The pattern generalizes: any bounded loop is `List.range(0, bound) |> List.walk_until(initial_state, step_fn)`.

## Effectful recursion

`fold` guarantees termination for pure functions. Effectful functions (`=>`) may still need unbounded iteration — reading from a socket, polling a queue, running an event loop. These are not subject to the termination guarantee (they interact with the external world where "done" is decided by I/O, not by structure).

The exact mechanism for effectful iteration (platform-provided loop primitives, effect handlers, or unrestricted recursion in `=>` functions) is an open design question.

## Why Gödel System T

Restricting pure code to structural recursion is a choice about the whole compiler, not just the source language. A total language where every pure function provably terminates makes a cascade of compiler passes simpler, faster, or eliminable. The call graph of pure code is a DAG, and every downstream pass gets to assume termination and acyclicity.

### Monomorphization in one topological pass

General recursion forces monomorphization to run as a worklist. Process each call site, discover new specializations of polymorphic functions, process those, iterate until no new instantiations appear. Polymorphic recursion can diverge, so the worklist needs a termination argument and guards against infinite specialization.

In System T, monomorphization is a single topological walk:

1. Topo-sort declarations once — callees before callers.
2. Walk in order. When a call `foo(T)` with concrete `T` is encountered, specialize `foo` on demand. The specialized body only calls things already processed, so it cannot create new instantiations upstream.
3. Done in one pass.

No worklist, no fixpoint, no divergence argument. Polymorphic-recursion blowup is impossible by construction, not merely unlikely.

### Sequential type inference

Hindley-Milner implementations typically compute strongly connected components of the call graph so that mutually recursive functions generalize together. You cannot generalize one without knowing the other's type. In System T every SCC has size one, so each function generalizes immediately after its body is checked. One less pass, one less data structure.

The two-phase forward-declaration walk that many compilers run also disappears. That phase exists so body N can call body M defined later in a cycle. Topological order guarantees every callee is fully checked before its caller is visited.

### Reachability and incremental recompilation

Reachability from `main` is DFS without cycle-breaking logic. A visited set is still useful for deduplication, but there are no indirect cycles where "this function calls itself through a chain" could go wrong.

Dependency analysis for incremental recompilation follows the same shape. Each function depends on a closed prefix of earlier functions. Changing `foo` invalidates exactly the functions that reach `foo` transitively, computed in one pass with no cycle analysis.

### Optimization without termination carveouts

Standard optimizations apply without an "unless it loops" guard. Parallel evaluation of independent fold branches is safe because neither branch can run forever while the other returns early. Speculative evaluation, aggressive inlining, and common subexpression elimination all work unconditionally. In a Turing-complete pure language each of these requires a termination proof or a conservative fallback.

The recursion shape itself is visible to the compiler: fold on `Nat` compiles to a counted loop, fold on `List` to a while loop, fold on `Tree` to divide-and-conquer. See [what fold compiles to](#what-fold-compiles-to).

### The tradeoff

The lost expressiveness is narrower than it looks. The fold-rebuild pattern covers most list and tree transformations. `List.range` + `List.walk_until` covers bounded iteration with data-dependent termination — binary search, Newton's method, convergence loops. Effectful code (`=>`) is unrestricted, so event loops, pollers, and servers run as long as they need to. The only thing ruled out is unbounded recursion in pure code, and in exchange every compiler pass downstream of the call graph gets to assume termination and acyclicity.

## Design rationale

> Why a separate `fold` keyword instead of extending `if`?

`fold` has fundamentally different semantics from `if` — it implies bottom-up traversal and changes what pattern variables mean. Mixing fold into `if` would be confusing: the same pattern `Cons(hd, rest)` would mean different things depending on context. A separate keyword makes the semantics visible at the call site.

> Why no `else` on fold?

Fold must be exhaustive — every constructor of the type must have an arm. An `else` catch-all would silently skip structural recursion for any constructor you forgot to handle. With demand-driven evaluation, an `else` body that doesn't reference recursive fields would skip those subtrees entirely — a dangerous default. Listing every constructor forces you to think about what each case should produce.

> Why no access to original recursive field values?

In a catamorphism, the algebra receives non-recursive components as-is and recursive components replaced by their fold results. The original recursive subterms are not part of the interface. This is what makes fold structurally recursive — you can't "cheat" by inspecting the raw subtree.

If a future use case requires access to both the original value and the fold result, an `as` binding could be added: `: Cons(hd, rest as rest_result) then ...`. But this is speculative and not needed now.

> Why allow `return` in fold?

Without `return`, fold always processes every node. This makes a large class of common operations on recursive data structures unnecessarily O(n):

```ruby
# Find a value in a tree — stop at first match
find = |t, target| fold t
    : Leaf(val) and val == target return Ok(val)
    : Leaf(_) then Err(NotFound)
    : Branch(left, _) and left is Ok(_) return left
    : Branch(_, right) then right

# Check if any node satisfies a predicate — stop at first True
any = |t, pred| fold t
    : Leaf(val) and pred(val) return True
    : Leaf(_) then False
    : Branch(True, _) return True
    : Branch(_, right) then right

# Validate an AST — stop at first error
validate = |expr| fold expr
    : Div(_, right) and right == 0 return Err(DivByZero)
    : Num(_) then Ok({})
    : Add(left, _) and left is Err(_) return left
    : Add(_, right) then right
    : Div(left, _) and left is Err(_) return left
    : Div(_, right) then right
```

Without `return`, every one of these traverses the entire structure even when the answer is known after visiting a single node. With `return` and demand-driven evaluation, they short-circuit — `find` stops at the first match, `any` stops at the first `True`, `validate` stops at the first error.

For lists, `walk_until` already provides early termination. `return` in fold extends this capability to all recursive data types — trees, expressions, any user-defined inductive type. Without it, the only way to express these algorithms in pure code would be to flatten the structure into a list (losing the tree shape) or use effectful code for no reason other than a missing control flow primitive.

`return` in fold exits the enclosing function, identical to `return` in `if`. Termination is still guaranteed — the structure is finite and recursion is structural, so early exit only makes it terminate sooner.

> Why demand-driven evaluation instead of strict bottom-up?

In strict bottom-up evaluation, fold computes all recursive fields before running the arm body. This means `return` in a Branch arm would skip ancestor combinations but still traverse every subtree — defeating the purpose of early return.

Since fold bodies are pure, evaluating or skipping an unused computation produces the same result. Demand-driven evaluation exploits this: recursive fields are evaluated when first referenced, and unreferenced fields are skipped. This is observationally equivalent to strict evaluation (no side effects to observe) but changes O(n) tree search into O(k) where k is nodes visited before the target.

The compiler implements this by analyzing which recursive fields each code path references and deferring evaluation of fields that aren't needed in early-return paths.
