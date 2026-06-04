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

## Migration: reorder lift before infer (DONE, with a pivot)

**Implemented in commits on `lambda-rewrite` branch (June 2026).** What
actually shipped differs from the original plan in one load-bearing
way: closures are kept **Arrow-typed through inference** (via the
existing `ExprKind::Closure` node) rather than emitted as
`Call(__ClosureTag_N, captures)` and natively typed as tag unions.

### Why the pivot

The original plan assumed inference could unify a synthesized
closure-union type (`__ClosureType_N`) with any `Type::Arrow` flowing
into a higher-order parameter — the way Roc unifies via lambda-set
rows. Ori's HM unifier doesn't have lambda-set rows: `Type::Arrow`
has no row variable for the set of closures it admits. So
`cannot unify (state, U64) -> Step(state) with __ClosureType_0`
falls out the first time a stdlib HOF (e.g. `walk_until`) sees a
synthesized closure-tag constructor call.

Adding lambda sets to `Type::Arrow` (and to unification + mono) is a
multi-week type-system project. Far smaller: pivot `lift_pre_infer`
to emit `ExprKind::Closure { func, captures }` and teach infer to
type that node as the lifted function's Arrow (minus the leading
capture params). Closures stay Arrow-typed; the downstream
post-mono pipeline (solve / specialize / narrow) keeps doing its
job.

### What the pivot ships

1. **`lambda::lift_pre_infer`** — new pass, runs after `flatten_patterns`,
   before `topo` and `infer`. Walks every body, lifts each `Lambda`
   to a top-level `FuncDef __lifted_N(captures..., params...)` whose
   body has captures substituted to fresh capture-param symbols.
   Emits `ExprKind::Closure { func: __lifted_N, captures: [Name(c0)..] }`
   at the lambda site. No TagDecl synthesis; no `func_schemes`
   touching.

2. **`types::infer`** — `ExprKind::Closure` arm looks up the lifted
   func's scheme (already inferred earlier in topo order),
   instantiates, unifies each `cap_expr` with the corresponding
   capture param type, and returns `Type::Arrow(remaining_params, ret)`
   — the closure's *callable* view. No Arrow-vs-TagUnion mismatch
   because closures stay Arrow-typed.

3. **`types::post_infer`** eta-expansion — now emits
   `ExprKind::Closure { func: __lifted_eta_K, captures: [] }`
   instead of `ExprKind::Lambda`. The synthesized
   `__lifted_eta_K(params) = body` FuncDefs and their monomorphic
   schemes are spliced into the module + `func_schemes` after the
   rewrite walk.

4. **`mono`** — `ExprKind::Closure` handler builds the *full* concrete
   arrow for the lifted func (capture types prepended to the
   closure's callable params), unwrapping transparent-newtype
   applications via `resolve_transparent` before calling
   `specialize_target`. `extract_substitution_with` itself takes
   the transparent table and unwraps on shape mismatch — so
   `App("Set", [V])` vs the underlying record now binds V.
   `SpecRequest` carries an `extra_mapping` for vars that appear
   in `scheme.ty` but not `scheme.vars` (foreign vars from the
   enclosing scope leaking into a lifted scheme.ty) — process_request
   layers it into the body's substitution mapping.

5. **`Scheme`** — gains `var_concretes: HashMap<TypeVar, Type>`
   carrying post-infer resolutions for vars that were generalized
   polymorphic but later bound to a *fully concrete* type at a call
   site (e.g. a method-constraint ret var resolving at a closure use
   site). The "fully concrete" filter is critical: a var resolving
   to a type containing another scheme's vars would carry foreign
   vars through mono.

6. **`engine.instantiate`** — preserves `expr_id` and `span` when
   re-pushing constraints. Polymorphic schemes with a method-on-tvar
   body otherwise never record `MethodCall.resolved` — the
   body-inference constraint's tvar never binds (each call site
   instantiates to a fresh tvar), so the fresh constraint's
   `expr_id` is the only one verify_constraints can write back.

7. **`register_methods`** — pre-mono method schemes are
   **polymorphic** over the fresh placeholder vars (not `Scheme::mono`).
   Otherwise those vars stay free in env, every Pass-2b caller
   unifies with the same env-resident vars, leaving cross-scheme
   aliases that break generalization.

8. **`solve` / `specialize` / `narrow`** — unchanged in structure.
   They still operate on `ExprKind::Closure` nodes the way they did
   when lift ran post-mono. specialize still does the `Closure → Call`
   rewrite + TagDecl synthesis. narrow still does scheme rewriting +
   per-call-site cloning. existing-lower still does shell-wrap
   materialization for HO call boundaries. The "drop scheme
   rewriting" / "remove shell-wrap" / "remove ho_param_closures"
   ideas from the original plan presupposed TagUnion-typed closures
   from infer — they don't apply to the pivot. (`ho_param_closures`
   itself was dead plumbing and is now removed; the others stay.)

9. **Dead Lambda walks** — every pass that runs *after* `lift_pre_infer`
   (infer, post_infer, mono, solve, specialize, narrow, reachable,
   core/pipeline, lower) has its `ExprKind::Lambda` match arm
   replaced with `unreachable!()`. `is_syntactic_value`,
   `infer_lambda`, and `check_lambda` in `types/infer.rs` are
   deleted.

### What's left for a future "real" cleanup

The shell-wrap path in `lower::to_slots` (Multi→Single materialization)
and `narrow::retype_scheme_params` exist because HO param positions
in `func_schemes` still carry `Type::Arrow` rather than the concrete
closure-union shape. Re-flowing the body's arg/return types through
every consumer that reads schemes would let both go away — but that's
the same multi-week scope as adding lambda sets to `Type::Arrow`
directly. Worth doing iff the runtime cost or maintenance cost of
the workarounds becomes load-bearing.

## Migration: reorder lift before infer (original plan, superseded)

The current pipeline runs lift AFTER mono+infer. That ordering forces lift to materialize types it doesn't strictly need (`func_schemes` for `__lifted_N`, `.ty` on Closure captures) and creates a two-source-of-truth problem downstream: schemes say one shape (Arrow for HO params), bodies expect another (closure-union for `__apply_K`). The mismatch surfaces in lowering as arity errors, type warnings, and the need for shell-wrap workarounds.

The clean ordering is **lift before infer**, with the `ExprKind::Closure` node retired entirely:

```
parse → resolve → fold_lift → flatten_patterns → lift → topo → infer → mono → solve → specialize → narrow → ...
```

### What changes per pass

1. **`lambda::lift`** (renamed `lift_pre_infer` or kept under same name):
   - Takes `&mut Resolved`, not `&mut Monomorphized`. Does not touch `func_schemes`.
   - For each `Lambda`: free-var analysis (lexical, no types needed) gives the captures. Mints a fresh `__lifted_N` `SymbolId` and a fresh `__Closure_N` tag-union name.
   - Emits THREE Decls:
     - `TypeAnno __Closure_N := [Tag_N(Var(c0), Var(c1), ...)]` — one type-var per capture.
     - `FuncDef __lifted_N(c0_param, c1_param, ..., param0, param1, ...) -> body` — captures as leading params, body has captures substituted to the new params.
     - (the original FuncDef the lambda was inside, with the Lambda replaced)
   - Replaces the Lambda site with `Call(Tag_N_sym, [cap_exprs])` — a regular tag-constructor call. No `ExprKind::Closure` produced.

2. **`types::infer`**:
   - Delete the `ExprKind::Closure => panic!` arm. Closure nodes no longer exist.
   - The new `TypeAnno __Closure_N` and `FuncDef __lifted_N` flow through inference as regular declarations. No special-casing.
   - Constructor calls `Tag_N(captures)` type as the declared TagUnion; capture type-vars unify with each `cap_expr`'s inferred type. Standard HM.
   - HO param positions (`apply`'s `f`) get unified with whatever closure-union flows in; result: `f` has type `__Closure_N` (or a tag-union of multiple `__Closure_*` types if multiple flow into one position — same lambda-set principle as today).

3. **`mono`**:
   - Specializes both user code and synthesized `__lifted_N` / `__Closure_N` declarations per the post-infer typing. Each `__Closure_N` gets monomorphized if its captures are polymorphic. No special handling needed — they're regular declarations.

4. **`lambda::solve`**:
   - Operates on typed AST as today, but instead of looking for `ExprKind::Closure`, looks for `Call(closure_tag_sym, captures)` where `closure_tag_sym` is a known closure-tag (i.e. its containing TypeAnno's name starts with `__Closure_`). Same 0-CFA flow analysis; smaller code because closure values are uniformly tag-constructor calls.

5. **`lambda::specialize`**:
   - No more `register_apply_scheme` post-hoc — `__apply_K`'s body is generated and inference (or a focused re-infer over just the synth helpers) types it naturally. Or: emit `__apply_K` as a regular FuncDef before mono, let mono pick it up. Either way: no scheme-rewriting machinery.
   - HO call rewrites (`f(n)` → `__apply_K(f, n)`) remain as today, but the AST-mutation is the only work — no separate scheme update needed because types are already correct.

6. **`lambda::narrow`**:
   - Per-call-site cloning. The `retype_scheme_params` function disappears: clones get their schemes re-derived (or just structurally rewritten without type changes — the singleton-narrow case substitutes one closure-union for another, both already concrete). Shrinks from ~1300 lines to probably ~600.

7. **`existing-lower`**:
   - `to_slots`' Multi→Single materialization path stays for *non-closure* multi-slot args (records-as-args, etc.) but the HO-call branch goes away — closures are uniformly multi-slot, just like records.
   - `lower_closure_step` simplifies — it's the closure-value lowering, and the value is already a Call to a constructor with the right shape.
   - `walk.rs` emission: step_params come from the apply target's scheme directly; no special closure-shape derivation.
   - The `mono.ho_param_closures` map (added during the failed incremental attempt) becomes unnecessary and can be removed.

### Migration approach

The cascade across passes is real — the user-facing test suite will break in batches during the migration. The honest path:

1. Build the new `lift_pre_infer` in parallel with the old `lift`; pipeline initially uses the old one.
2. Add a `ORI_LAMBDA_V2=1` flag that switches pipelines.
3. Get the v2 pipeline passing tests by working through cascades pass-by-pass (infer → mono → solve → specialize → narrow → lower).
4. Once v2 is at parity, delete v1 + the flag.

Estimated effort: 2-3 focused days. Touches ~3-4k lines across `passes/lambda/*`, `types/infer.rs`, `lower/*.rs`. Net delta: probably -500 to -1500 lines once shell-wrap workarounds are removed.

### Concrete audit: `ExprKind::Closure` references

Run this audit before starting — it converts "vague refactor" into "fix exactly these sites":

**Producers** (will be deleted):
- `src/passes/lambda/lift.rs:205` and `:327` — the two places lift currently emits `Closure { func, captures }`. New `lift_pre_infer` emits `Call(closure_tag, captures)` + `TypeAnno __Closure_N := [...]` + `FuncDef __lifted_N` instead.

**Structural consumers** (need rewrites to handle the new `Call`-shape):
- `src/passes/lambda/solve.rs:371, 438, 501, 575` — 0-CFA flow analysis that matches `Closure { func, captures }` to extract func/capture names. Update to match `Call(closure_tag_sym, captures)` where `closure_tag_sym` is recognizable as a closure tag (registry from lift, or name-prefix check on `__Closure_*_tag`).
- `src/passes/lambda/specialize.rs:684, 736` — does the `Closure → Call(tag, captures)` rewrite today. After lift produces this directly, **these blocks delete entirely** (~30 lines net deletion).

**Traversal walkers** (just delete the `Closure` arm — variant no longer exists):
- `src/passes/reachable.rs:318`
- `src/ast_display.rs:304`
- `src/passes/mono.rs:537, 1023`
- `src/passes/validate_ast_types.rs:190`
- `src/passes/core/pipeline.rs:590`
- `src/passes/topo.rs:212`
- `src/lower/mod.rs:166, 1109`
- `src/types/post_infer.rs:161`
- `src/passes/lambda/narrow.rs:324, 818, 962, 1107` — narrow walks Closure structurally for cloning; also needs Call-shape update (~50 lines)
- `src/passes/flatten_patterns.rs:234`
- `src/test_frontend.rs:3686`

**Panic/error guards** (update or delete):
- `src/passes/fold_lift.rs:202` and `:592` — "Closure should not exist before lambda_lift" — still valid after reorder if Closure variant is retained. If variant is deleted entirely, remove these guards.
- `src/passes/lambda/solve.rs:544` — `"expected Name in Closure captures"` — invariant still holds for Call(closure_tag, [Name, Name, ...]) shape; reword.
- `src/passes/lambda/specialize.rs:746` — `"Closure func must be in lambda set"` — delete entirely (specialize no longer touches Closure).
- `src/types/infer.rs:745` — `"Closure should not exist during type inference"` — **delete this arm** (Closure never exists in infer's input under the new ordering, OR variant is retained but unreachable).

### Where the new closure-tag declarations live

Currently `specialize::build_closure_type` synthesizes the `TagDecl __Closure_N := [Tag_N(field_tys...)]` after solve has merged lambdas into lambda sets. In the new ordering, **lift creates one TagDecl per lambda** (single-variant): `__Closure_lambda_N := [Tag_lambda_N(Var(c0), Var(c1), ...)]`. Capture types are type-variables.

Inference's row-polymorphism then handles the union case automatically: when two distinct lambdas flow into the same HO parameter, unification of their single-variant types yields a multi-variant tag union via existing row machinery. **`lambda_solve` no longer needs to compute set membership** — it just reads the post-infer types and enumerates the union's tags. Solve becomes a much smaller pass (~200 lines instead of 672).

### What changes for `__apply_K`

`specialize::build_apply_function` currently runs after the body rewriter. In the new world, it can run as part of specialize too (the body-rewriting half of specialize stays — it's where `f(n)` becomes `__apply_K(f, n)`). What changes: the closure-union types `__apply_K` consumes are now natively typed by inference, so `register_apply_scheme` simplifies — no need to derive the scheme from lifted-function param types after the fact; it falls out of normal inference if `__apply_K`'s body is emitted before the second inference pass.

Actually simpler: `__apply_K` is just a regular function. Lift could emit it. Or specialize could emit it. Either way, normal inference covers it.

### Why this is worth doing

The current architecture leaks a "fix up types after the fact" pattern across multiple consumers (Core's `param_slot_types`, existing-lower's `to_slots`, `decl_info`'s helper maps, the abandoned `mono.ho_param_closures`). Every consumer that touches HO function signatures has to special-case Arrow-vs-closure-union. The lift-pre-infer reorder collapses all of that into "the type system says what the type is; consumers read it." One source of truth.

The blocker today is just that the original lift-after-infer ordering was load-bearing for several passes' implementations; unwinding it touches enough surface that it's a focused-session task, not a quick patch.

### Why this is worth doing

The current architecture leaks a "fix up types after the fact" pattern across multiple consumers (Core's `param_slot_types`, existing-lower's `to_slots`, `decl_info`'s helper maps, the abandoned `mono.ho_param_closures`). Every consumer that touches HO function signatures has to special-case Arrow-vs-closure-union. The lift-pre-infer reorder collapses all of that into "the type system says what the type is; consumers read it." One source of truth.

The blocker today is just that the original lift-after-infer ordering was load-bearing for several passes' implementations; unwinding it touches enough surface that it's a focused-session task, not a quick patch.
