# lambda/

**Defunctionalization.** Four sub-passes that together strip every
`Lambda` and `Closure` AST node out of the program, leaving every
call with a known first-order target.

```
input AST (with Lambda / Closure nodes)
   │
   ▼
lift::lift               (lambdas → top-level FuncDefs + Closure values)
   │
   ▼
solve::solve             (0-CFA: which closures can flow where)
   │
   ▼
specialize::specialize   (Closure values → tag constructor calls,
                          merged-set `__apply_K` dispatchers)
   │
   ▼
narrow::narrow           (per-call-site clones of user HOFs —
                          singleton sets → Phase E)
   │
   ▼
output AST (no Lambda, no Closure, every call first-order,
            closure values decompose into register captures)
```

## Why defunctionalization at all

Ori's thesis is **static memory management** — Perceus refcounting +
FBIP at the language level, not as an optimization. For that thesis to
mean anything, closures can't be black boxes. A closure that gets
heap-allocated and dispatched through a vtable is a closure that the
RC/FBIP machinery can't see through, so the language's claim about
memory behavior breaks down for any program that uses higher-order
functions.

Defunctionalization converts every closure into something the rest of
the compiler can reason about:

- **Closures become tag union values.** A closure with captures
  becomes a tag-constructor call carrying the captures as fields. The
  same machinery that handles `[Ok(x), Err(e)]` handles
  `[ClosureA(cap1, cap2), ClosureB(cap1)]` — RC, FBIP, pattern
  matching, layout, all unchanged.
- **Higher-order calls become first-order dispatches.** `f(x)` where
  `f` is a closure becomes either a direct call (singleton lambda set)
  or a tag-discriminated dispatch (multi-variant set). No vtable, no
  indirect call through a function pointer column.
- **Phase E fires on closures.** When the lambda set is single-variant
  (the common case after `narrow`), the closure value lowers to
  `Multi(captures…)` — captures live in registers, no heap object for
  the closure itself.

The trade-off versus Rust's "closures are anonymous types" model:
- Rust's mono handles homogeneous closures with direct calls (good)
  but needs `Box<dyn Fn>` for heterogeneous flow (heap + vtable).
- Defunctionalization handles **both** cases without heap or vtable.
  Singleton sets → direct calls; multi-variant sets → tag dispatch.

The trade-off versus type-erased function pointers:
- A function pointer + opaque captures pointer is simple but requires
  RC bookkeeping the runtime can't statically know about, and breaks
  FBIP entirely.
- Defunctionalization keeps everything visible.

This is the same approach Roc takes (RFC 0102, "Compiling lambda
sets"); the names "lambda set" and "function specialization" come from
there. See `notes/lambda-set-specialization.md` for the design history
and how the four-pass split mirrors Roc's solve/specialize split.

## The four sub-passes

### lift — `lift.rs`

Converts every `ExprKind::Lambda` into a top-level `Decl::FuncDef`
with captures threaded in as leading parameters, and replaces the
`Lambda` node with an `ExprKind::Closure { func, captures }` value.

Input invariant: lambdas may be nested. Output invariant: no
`Lambda` nodes survive. Each closure-shaped value is now a tuple
`(lifted_func_sym, captures)` carried as a `Closure` AST node.

Why this is a separate pass: the rest of the lambda pipeline analyzes
**flow** between top-level functions. Lifting first gives every
former lambda a stable identity (its `SymbolId`) that solve can
reason about.

### solve — `solve.rs`

0-CFA flow analysis. For each higher-order parameter position in the
program, computes a **lambda set**: the list of lifted functions that
can flow into that position.

Iterates to fixpoint. The main signals it tracks:

1. **Direct flow.** `apply(closure_value, x)` adds `closure_value`'s
   lifted func to `apply`'s f-param lambda set.
2. **Variable flow.** Closures stored in `let` bindings or function
   return values get propagated.
3. **Capture chains.** If a lifted function's capture is itself
   called, the enclosing function's parameter at the corresponding
   position is also higher-order.
4. **Per-call-site keying for intrinsics.** `List.walk` has no AST
   body — `solve` keys its lambda sets per call-site span so each
   walk call site lands in its own (typically singleton) set. The
   downstream `lower::walk` pipeline reads this back via the
   `singletons` map and emits a direct call inside the walk loop.

Output: a `LambdaSolution` mapping each
`(callee_name, parameter_index)` to a lambda set.

### specialize — `specialize.rs`

Consumes the `LambdaSolution`. For each lambda set, synthesizes:

- A `TagDecl` closure type, one variant per closure in the set.
- An `__apply_K` `FuncDef` that pattern-matches on the closure tag
  and dispatches to the matched closure's lifted function.

Then rewrites the AST:

- `Closure { func, captures }` → `Call(tag_sym, captures)` — a tag
  constructor call producing a closure value.
- `f(x)` where `f` is a higher-order variable → `__apply_K(f, x)` —
  the dispatcher call. For singleton lambda sets, this is short-
  circuited to an inline `if f : tag(captures) then lifted(captures, x)`
  pattern match, which lowers to a direct call.

After this pass there are no `Lambda` or `Closure` nodes anywhere.
Every call has a first-order target.

The piece this pass deliberately doesn't do: per-call-site narrowing
of user HOFs. When two call sites of `apply` pass two different
closures, they share `apply`'s f-param lambda set, which becomes
multi-variant, and the closure values end up in the D2
`(tag, payload_ptr)` heap shape. That's the job of `narrow`.

### narrow — `narrow.rs`

Per-call-site cloning of user-defined HOFs. The reason this is a
separate pass instead of part of `specialize`: it requires the AST
already be in post-specialize shape (closures are tag constructor
calls, dispatches go through `__apply_K`), and it touches a fairly
self-contained set of patterns.

For each post-specialize `Call(user_hof, [Call(tag_sym, captures), ...])`
where the closure tag's enclosing `TagDecl` is multi-variant:

1. Synthesize a singleton `TagDecl` for the narrowed HO position,
   with a fresh tag constructor.
2. Clone the callee's `FuncDef` body, allocating fresh `SymbolId`s
   for params and locals via an AST-substitution visitor.
3. Rewrite the clone's body so `__apply_K(f, args)` (where `f` is the
   narrowed param) becomes
   `if f : new_tag(captures) then target_func(captures, args)` —
   a single-arm match that lower's `is_single_variant_tag_union`
   collapses to register access.
4. Update `func_schemes` so the clone's HO param has the singleton
   `Type::TagUnion` type.
5. Retarget the call site: `target` → clone, closure-constructor's
   target → new tag, closure-arg's `expr.ty` → singleton `Type::TagUnion`.

Sites whose closure tag is already in a single-variant `TagDecl` are
skipped — narrowing them is semantically a no-op and interacts badly
with `const_eval`'s static-promotion path for compile-time-constant
captures.

Result: the multi-callsite user HOF case (`apply` called with two
different closures) goes from 4 heap allocs to 0, matching the walk
case shipped earlier.

## Shared types

`mod.rs` re-exports `SingletonTarget` (defined in `specialize.rs`) so
downstream callers in `lower/` and `mono` import it as
`crate::passes::lambda::SingletonTarget` without depending on which
sub-pass produces it. The other shared types — `LambdaSolution`,
`LambdaSet`, `LambdaEntry` — only cross the solve/specialize boundary
and are imported with their full path; they're not part of the
lambda module's public surface.

## Validation

Three pinned tests in `test_frontend.rs` together exercise the
pipeline:

- `e_captured_closure_in_walk` — walks (intrinsic HO position).
  Singleton via `solve`'s per-call-site keying. Closure decomposes
  into register captures, no heap.
- `e_user_hof_two_callsites_same_type` — user HOF called from two
  call sites with different closures. Narrowing fires; each clone has
  a singleton set. Asserts 0 allocs.
- `e_user_hof_heterogeneous_callsite` — single call site with
  `if cond then closure_a else closure_b`. Narrowing doesn't apply
  (the merged tag union really is needed). Asserts correctness only.

## Order constraints

`lift` must precede `solve` (solve needs lifted top-level functions).
`solve` must precede `specialize` (specialize consumes `LambdaSolution`).
`specialize` must precede `narrow` (narrow walks post-specialize
shapes — tag constructor calls and `__apply_K` references).

All four must precede `decl_info::build` and `reachable::prune`, which
need to see the final set of decls (including synthesized `TagDecl`s,
`__apply_K` functions, and `narrow`-generated clones).
