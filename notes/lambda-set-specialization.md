# Closures and lambda sets

Ori compiles closures as **tagged unions over a finite, statically-known set of lifted functions**. There is no opaque function pointer, no vtable, and no heap allocation in the common case. This note is a tutorial and specification for how that works — the language-level concept, the semantics, and the runtime representation. For the implementation, see `src/passes/lambda/`.

The companion note `notes/functions.md` covers function syntax. This note is about what happens *behind* a closure value.

## Lambda, closure, lambda set

Three words that get confused easily:

- A **lambda** is the source-level expression `|args| body`. It's syntax. After lifting, no lambdas survive.
- A **closure** is the runtime value that a lambda produces: a function paired with its captured environment. Two lambdas with the same body but different captures are two different closures.
- A **lambda set** is the static enumeration of all closure values that can flow through a given function-typed position in the program. It's a property of *positions* (a parameter, a return, a let-bound variable), not values.

A function-typed parameter `f : a -> b` has, at every call site in the program, a lambda set that lists every closure value that can show up there. The compiler computes this set ahead of time. There is no runtime "function pointer that could be anything" — every possible target is named.

## The setup: how a lambda becomes a value

Start with a lambda:

```ruby
make_adder = |n| (|x| x + n)
```

The inner lambda `|x| x + n` captures `n` from the enclosing scope. The compiler **lifts** every lambda to a top-level function, threading captures in as leading parameters:

```ruby
# After lifting (conceptually):
__lifted_inner = |n_cap, x| x + n_cap

make_adder = |n| Closure { func: __lifted_inner, captures: (n,) }
```

The result of evaluating the inner lambda is no longer an opaque function value — it's a *constructor call* producing a closure value. The function part (`func`) is a compile-time-known top-level function symbol. The captures are the run-of-the-mill values from the enclosing scope.

This is the only thing a closure *is*: a function name paired with a tuple of captured values.

## Lambda sets

Consider:

```ruby
add_x : I64 -> I64
greet : I64 -> I64
add_x = |y| y + x_global
greet = |y| y + s_global.len()

apply : (I64 -> I64), I64 -> I64
apply = |f, n| f(n)
```

`apply`'s first parameter `f` has type `I64 -> I64`. From the type alone, `f` could be any function with that signature. But Ori is closed-world: every closure that can ever flow into `f` is constructed somewhere in the program, and the compiler enumerates them. That enumeration is the **lambda set** of `f`'s position.

If the program calls `apply(add_x, 5)` once and never passes `greet` to apply, the lambda set of `apply`'s `f` is `{add_x}` — a singleton. If both calls exist, the set is `{add_x, greet}`.

The lambda set is essentially a tag union type, automatically inferred:

```
f : I64 -[add_x | greet]-> I64
```

(Ori doesn't write the lambda set in source syntax — the inference is implicit. The notation here is just to make the underlying structure visible.)

This is closely related to row-polymorphic tag unions for ordinary data: `[Ok(a), Err(e)]` is a tag union over two variants; the lambda set is a tag union whose variants are closures. The machinery is shared.

## Runtime representation

A closure value at runtime is exactly its tag-union shape:

- **Multi-variant lambda set**: `(tag, captures...)`. The tag identifies which closure the value is, the captures follow. Lowered as `(tag: U64, payload_ptr: RcPtr)` to a heap object containing the captures — the standard D2 shape for non-fieldless tag unions.
- **Single-variant lambda set**: `(captures...)`. The tag is implicit (there's only one option), captures live in registers as parallel SSA values. No heap object. This is Phase E single-variant decomposition.

The single-variant case is the common case in practice. Most call sites pass one specific closure to one specific HOF — the lambda set is naturally singleton. The compiler exploits this aggressively.

When the lambda set is genuinely multi-variant (two or more closures flowing through the same position by run-time control flow), the tag exists and the dispatch is a tag compare. The dispatcher knows every possible target by name and emits a direct call per arm — no vtable, no indirect call.

## Dispatch

Inside the HOF body, a call to the function-typed parameter is **tag dispatch over the lambda set**:

```ruby
# Source:
apply = |f, n| f(n)

# Conceptual lowering (multi-variant case):
apply = |f, n|
    if f
        : AddX(x) then __lifted_add_x(x, n)
        : Greet(s) then __lifted_greet(s, n)
```

For a singleton lambda set, the dispatch is a one-arm match that the lowering collapses to a direct call:

```ruby
# Singleton case:
apply = |f, n|
    if f : AddX(x) then __lifted_add_x(x, n)

# Phase E lowers this to: __lifted_add_x(captures_from_f..., n)
# — no tag check, no payload load, captures are already in registers.
```

The "tag dispatch" model means dispatch is **always discrimination over a known finite set**, never invocation through an unknown pointer. The runtime cost is at most one tag compare + a direct jump.

## Per-call-site specialization

Two call sites of the same HOF can pass two different closures:

```ruby
main = |arg|
    a = arg + 10
    b = arg + 20
    x1 = apply(|y| y + a, 1)   # site 1: passes closure_a
    x2 = apply(|y| y + b, 2)   # site 2: passes closure_b
    x1 + x2
```

A naive analysis would say `apply`'s `f` parameter has lambda set `{closure_a, closure_b}` — multi-variant. Each closure value at construction would then need the `(tag, payload)` shape, even though at each individual call site only one closure ever flows in.

Ori specializes more aggressively: it generates a **separate clone of `apply`** for each call site. The clone's `f` parameter has a singleton lambda set (just the one closure that flows in at that site). At each call site, the closure value is single-variant, Phase E fires, captures live in registers, and the dispatch inside the clone collapses to a direct call.

This is the *function-set analog* of monomorphization. Just as Ori specializes generic functions per type — `apply : (a -> b), a -> b` is cloned per concrete `a, b` — it also specializes them per lambda set. Function specialization and type specialization are orthogonal axes of the same idea: replace polymorphism with cloning, get direct calls and tight layouts as the natural result.

The genuinely multi-variant case — when *one* call site can produce *multiple* closures by runtime control flow — keeps the tag:

```ruby
apply(if cond then closure_a else closure_b, 5)
```

Here a single call site's closure value can be either closure depending on `cond`. The lambda set at this position is `{closure_a, closure_b}`; the value must carry the tag; the dispatcher must compare it. There's no narrowing to apply, and no way around the tag — but the dispatch is still a switch over two known arms with direct calls, not an indirect call.

## Compile-time collapse

The runtime representation is a worst-case description. In practice further compiler passes collapse it further when the surrounding code permits:

- **Static promotion**: if a closure's captures are all compile-time constants, the entire closure value is baked into static memory. The dispatcher's tag load returns a static constant, branch folding prunes the unreachable arms, dead-code elimination removes the construction. The closure is gone before the program runs.
- **Inlining + constant propagation**: if the HOF is small enough to inline, the closure construction and the dispatch end up in the same block. The tag store flows directly into the tag load; branch folding fires; the dispatch collapses to its one live arm.
- **Phase E**: single-variant closures lower to register captures (no tag, no payload). This is automatic for every singleton lambda set, whether the singleton came from natural call-site usage or from per-call-site specialization.

The layered story: **specialization** reduces the worst case at compile time (more sets become singleton); **lowering** turns singleton sets into register-only values; the **opt pipeline** does further constant-time collapse where the SSA permits.

## What you pay, when

| Closure construction | Cost |
|---|---|
| Singleton set + non-constant captures | Captures live in registers. No allocation. Dispatch is a direct call. |
| Singleton set + constant captures | Closure folded into a static. Zero runtime work. |
| Multi-variant set, statically determinable | Folded into the matching variant at compile time. Zero runtime work. |
| Multi-variant set, runtime-conditional | Tag is stored at construction. Dispatch is one tag-compare + direct jump. Captures heap-allocated for variants that have them. |

The only irreducible cost is the genuinely heterogeneous, genuinely runtime-conditional case. And even there, the cost is one tag compare — the same cost as pattern-matching on `Ok(_) | Err(_)`. There is no vtable indirection in any case.

## Why this design

Ori's central claim is that **memory is managed statically** — Perceus refcounting and FBIP in-place mutation aren't optimizations, they're the runtime model. For that claim to hold under higher-order functions, closures cannot be opaque. A closure that the compiler can't see through is a closure whose captures the RC pass can't track, whose lifetime FBIP can't reason about, and whose dispatch costs an indirect call.

Lambda set inference is the mechanism that keeps closures transparent. Every closure is a constructor call producing a tagged union value, just like `Ok(x)` is a constructor call producing a `Result`. The same machinery — RC traffic on the payload, FBIP on update, single-variant decomposition for layout — handles closures uniformly. Higher-order code pays nothing extra at the language level.

The model is borrowed from Roc, where the analogous machinery has shipped in production for years. The key insight (in both languages) is that closures are sum types: at any point in the program, a function-typed value is exactly one of a known finite set of options, and the compiler can specialize per option whenever it pays off.

## Comparison

| | Direct calls | Heterogeneous closures | Heap for closures | Indirect calls |
|---|---|---|---|---|
| Rust monomorphization | Yes, when types unify | No — needs `Box<dyn Fn>` | `dyn Fn` → heap | `dyn Fn` → vtable |
| Type-erased function pointers (`fn(*captures)`) | Always | Yes | Yes (the captures) | Yes (the pointer) |
| Ori lambda sets | Singleton sets | Yes, via tag union | Only when variant payload is nonempty | Never |

Lambda set compilation strictly dominates monomorphization-with-dyn for heterogeneous closures — same direct-call quality, no heap, no vtable. The tag is the only added concept, and it's only paid when genuinely needed.

## What is out of scope

- **General recursion through closures.** Ori is total — structural recursion only via `fold` over inductive types. A closure can't refer to itself by name from inside its own body, so the lambda-lift step is straightforward and the lambda set is always finite.
- **Closures crossing FFI.** All closure values are constructed inside the Ori program. Nothing flows back from a host that the compiler hasn't enumerated.
- **Function pointers as first-class values across modules without a known set.** Lambda set inference is whole-program. Per-module incremental compilation, if added later, requires a story for cross-module function-set propagation (Roc has one; Ori currently does not need it).
- **`dyn`-style erasure as an opt-in escape valve.** If code size from per-call-site cloning ever becomes a real problem, Ori could add an opt-in erasure mode for specific positions (typed function pointer + opaque captures pointer). Not currently planned — every benchmark so far fits inside the lambda-set model.

## A worked example

```ruby
double = |x| x * 2

apply : (I64 -> I64), I64 -> I64
apply = |f, n| f(n)

main : I64 -> I64
main = |arg| (
    x = arg + 1
    apply(|y| y + x, 5) + apply(double, 7)
)
```

What the compiler sees, after lambda lifting:

- `double` is a named top-level function.
- The inline `|y| y + x` becomes a lifted function `__lifted_0 = |x_cap, y| y + x_cap`, plus a closure value `Closure { func: __lifted_0, captures: (x,) }` at the call site.
- Two call sites of `apply`: one passes the inline closure, one passes `double` directly (which the compiler treats as an empty-capture closure: `Closure { func: double, captures: () }`).

Lambda sets at `apply`'s `f` parameter:
- At site 1: `{__lifted_0(I64)}` — singleton, captures one I64.
- At site 2: `{double()}` — singleton, no captures.

Specialization clones `apply` per call site (their lambda sets differ). Each clone has a singleton `f`. Phase E lowers both closures to register-only values: site 1's is just the captured `x`, site 2's is empty. Each clone's body inlines to a direct call: `__lifted_0(x, 5)` and `double(7)` respectively.

What actually runs:

```ruby
main = |arg|
    x = arg + 1
    (5 + x) + (7 * 2)    # closures fully eliminated
```

No tag was stored. No heap object was allocated for any closure. Two direct calls — one to `__lifted_0`, one to `double` — both of which the inliner is free to inline further. The end result is plain arithmetic.

That collapse is what the lambda set machinery exists to deliver. Every higher-order Ori program is compiled toward this shape; the only deviations are the truly heterogeneous cases, where the cost is one tag compare.
