# Plan: per-call-site lambda set specialization

Status: **Stage A shipped (walks).** Each `List.walk` / `List.walk_until` call site now has its own lambda set, keyed by the closure-arg's source span in addition to the step type. Phase E lowering's single-variant collapse fires for walk closures: the closure value decomposes into register captures, no tag/payload heap allocation, no `__apply_K` dispatcher. Verified by `e_captured_closure_in_walk` (2 allocs) and `e_two_walks_same_signature_singleton_each` (4 allocs across two walks).

Stage A landed as ~100 lines across `src/lower/walk.rs` (`walk_apply_name` takes a `Span`), `src/lower/call.rs` (callers pass the closure-arg span), `src/passes/lambda_solve.rs` (`walk_call_key` mangles the span), and `src/passes/reachable.rs` (mirrors the same name construction). The merge step in `lambda_solve` stayed — it still applies to non-walk HO positions.

**Remaining: Stages 1-6 below** — per-call-site specialization for *user-defined* HOFs, i.e. real callee cloning. Stage A only covers intrinsics (walk has no AST body, so per-call-site keying suffices; the existing lower-time `singletons` map handles direct dispatch). User HOFs like `apply : (a -> b), a -> b` need their bodies cloned per call site so the inner HO call dispatches against a known (likely singleton) set.

## Empirical findings

Two pinned tests in `src/test_frontend.rs` exercise user HOFs and reveal the precise gap:

- `e_user_hof_singleton_callsite` — user HOF `apply = |f, n| f(n)` called from one call site with a captured closure. **0 heap allocs today.** Note: this is *not* because Phase E fires — the closure value still uses the D2 shape — but because the closure's captures are constant-foldable (`x = 10`), so `const_eval` + `static_promote` bake the closure as a static and `rc_elide_static` removes the rc traffic. With runtime-dependent captures the count would be > 0.
- `e_user_hof_two_callsites_same_type` — same user HOF called from two call sites with two different captured closures of runtime-dependent values. **4 heap allocs today** (2 per closure: one for the captures payload + one for the `(tag, payload_ptr)` D2 shell). The merge step in `lambda_solve` unifies the two closures into one multi-variant tag union; the D2 shape is then required for both call sites because Phase E (single-variant decomposition) doesn't fire.

So Stage 2's actual goal: 4 allocs → 0 for this case, by making each call site's closure type single-variant so Phase E lowering's `is_single_variant_tag_union` collapse fires.

## What partial implementations do NOT work

Verified during the Stage 2 design pass:

- **Per-call-site keying in `lambda_solve` without cloning** breaks 16 tests. The body of `apply` runs `enter_scope("apply", params)` which looks up `param_to_set[("apply", 0)]`; if external call sites populate per-call-site keys like `("apply__cs<span>", 0)` instead, the body-side lookup finds nothing and `f` isn't marked HO. Inside the body, `f(n)` then dispatches as a regular call to a closure value → runtime crash.
- **Adding per-call-site sets *alongside* the merged set** (so the body still finds its set) doesn't help. The closure value at the call site would carry the singleton tag union type (for Phase E), but the callee's `f` param still expects the merged tag union type → type mismatch at the SSA level (Phase E shape `Multi(captures)` is multi-slot, merged shape `Multi(tag, payload_ptr)` is two-slot, but with different scalar types — they're not interchangeable).
- **SSA-level inline + branch-fold + DCE** doesn't currently eliminate the closure heap. The `--dump-ssa` output for the 2-callsite case shows all 4 `alloc` instructions surviving optimization; branch-fold doesn't see through the store→switch→load chain.

The cloning approach is the only one that gives each call site's `f` its own narrower type, which is what unblocks Phase E.

## Required machinery for Stage 2

To make `apply.cs1` and `apply.cs2` each fire Phase E:

1. **AST clone with substitution.** Deep-clone the callee's `Decl::FuncDef` body. Allocate fresh `SymbolId`s for params and any local lets/destructures/pattern bindings; build a substitution map; walk every `ExprKind::Name`, `Pattern::Binding`, `Stmt::Let { name }`, etc. and remap. ~150 lines.
2. **New singleton TagDecls per call site.** Each clone's HO param type is a new transparent newtype around a single-variant tag union. The variant carries the captures. ~50 lines.
3. **New tag constructor symbols.** Each new TagDecl needs its own constructor `SymbolId` (Ori constructors are scoped by name, and `decl_info::build` reads each TagDecl's variants into the constructors map). Updating `tag_targets` so `lower::resolve_closure_target` finds the direct call target. ~50 lines.
4. **Inline singleton dispatch in clone bodies.** Replace `__apply_K(f, args)` in the cloned body with the singleton's inline match: `if f : tag(captures) then lifted_func(captures, args)`. ~80 lines.
5. **Scheme updates for clones.** `mono.infer.func_schemes` needs entries for each clone with the HO param's narrowed type. Without this, `lower::scalar_type` won't resolve the param to the singleton TagDecl. ~30 lines.
6. **Call-site rewriting.** Walk all `Call(callee, args)` sites; for matching patterns, change `target` to the clone's symbol and update the closure-constructor args to use the new singleton tag. ~80 lines.
7. **Reachable + decl_info.** Both passes already iterate over all decls and pick up new clones automatically (decl_info builds from the module; reachable does a DFS from `__main`), so no changes needed *for the clones themselves* — but the original (now-unreached) `apply` body and the wide `__apply_K` will be pruned by reachable. Verify with `audit_ssa_cleanliness*`.

Total: ~440 lines for the pass + tests + integration. Genuinely a focused multi-day session, not "let me hack at it for a few more turns."

## Why this session stops here

Stage A landed cleanly (~100 lines, surgical). Stage 2 is structurally an order of magnitude larger. Attempting it mid-session — after F1-F4 + G1 + F2-full already shipped — risks the half-baked outcome the user explicitly rejected. The architecture is now documented in detail; the empirical numbers are pinned in tests; the next session can open `lambda_narrow.rs`, write the AST substitution helper first, and proceed from a clean slate.

## Why per-call-site keying alone (without cloning) doesn't help user HOFs

Tempting shortcut: just key lambda sets by `(callee_name, call_site_span, arg_idx)`. Each call site gets its own set; sets are singleton; Phase E should fire.

It doesn't work because the callee's HO param has *one* type — the union of all closures that can flow in. The closure value passed at each call site must conform to that union type. A Phase E single-variant value (the `Multi(captures)` shape, no tag) can't be passed to a position expecting a multi-variant tag union value (`Multi(tag, payload_ptr)`, D2 shape) — the shapes are incompatible.

The escape is to make the callee's HO param have the narrower per-call-site type, which means *cloning the callee per call site*. The clone's HO param type is the singleton set; values at this clone's call site are Phase E shape; Phase E fires uniformly.

Walks bypass this constraint because they have no callee body — there is no HO-param-typed variable to type-check. The lower stage emits the dispatch directly from the closure value at the call site.

## Context for a fresh session

Ori currently compiles closures via three passes (`notes/compiler-passes.md`):

- `lambda_lift` — every `Lambda` becomes a top-level `__lifted_N(captures..., params...)`; the Lambda node is replaced with `Closure { func, captures }`.
- `lambda_solve` — 0-CFA flow analysis. Tracks which lifted functions can flow into each HO parameter position. **Merges sets bidirectionally** when the same closure flows through multiple paths. Outputs `(func_name, param_index) → lambda_set_idx`.
- `lambda_specialize` — for each merged set, synthesizes a `TagDecl` closure type and an `__apply_K` dispatcher. Rewrites every `Closure` to a tag constructor and every HO call to `__apply_K(f, args...)`.

The merge step in `lambda_solve` is the problem. When polymorphic stdlib HOFs (`List.walk`, `List.map`, ...) accept closures from many call sites, all those closure sets unify into one. The resulting set is multi-variant, so `lambda_specialize` synthesizes a dispatcher and Phase E's single-variant collapse can't fire. The lowering correctly handles singletons; the upstream pass never produces any.

## The decomposition principle

**Specialize HOFs per call site, not per parameter position.** Each call site of a HOF gets its own clone of the callee, with the lambda set at *that call site* substituted into the callee's signature. After specialization the program is strictly first-order — there are no HOFs, and every closure value has a known, narrow set of possible targets.

This mirrors the type-specialization (mono) pass: just as a polymorphic type variable gets resolved per call site by cloning the callee, a polymorphic *function set* variable gets resolved per call site by cloning the callee. Roc calls these orthogonal axes "type specialization" and "function specialization." Ori already has the first; this plan adds the second.

## Why this is the right design

Compared to today's merging + dispatcher:

- **Smaller runtime representation.** A call site whose lambda set is singleton compiles to a direct call. No tag, no dispatcher, no payload heap object. Phase E lowering fires uniformly.
- **Multi-element sets keep working.** A heterogeneous call site (e.g. `if cond then fn1 else fn2`) gets a real lambda set tag union. Dispatch is a tag compare + jump — no vtable, no heap. Same shape Roc compiles to.
- **No new IR.** The same `TagDecl`/`Match` machinery used for ordinary tag unions handles dispatch. `lambda_specialize` becomes simpler: clone + substitute, no per-set dispatcher synthesis.

Compared to Rust's approach (closures as anonymous types, generic HOFs, `dyn` for heterogeneity):

- Rust handles homogeneous closures via mono — direct calls, no heap.
- Heterogeneous closures cost a `Box<dyn Fn>`: heap allocation + vtable dispatch.
- The Roc approach we're adopting handles both cases without heap or vtable. Strictly more powerful than Rust mono for our language.

Reference: Roc RFC 0102 *Compiling lambda sets* (the RFC explicitly calls this orthogonality and pipeline-cleanliness the design's main argument).

## Pipeline shape

```
parse → resolve → fold_lift → flatten_patterns → topo → infer
     → mono → lambda_lift → lambda_solve → lambda_specialize
     → reachable prune → lower (SSA) → opt → eval
```

The pass *names* stay; their *semantics* change.

### lambda_solve (new behavior)

Drop the merge step. Track per-call-site sets instead of per-position sets.

Output today:
```
(func_name, param_index) → lambda_set_idx
```

Output after this change:
```
call_site_id → lambda_set
```

Where `call_site_id` is a stable id for each HO call expression in the module. The `lambda_set` itself is a list of `(lifted_func, capture_types)` pairs — the same shape we have today, just not merged.

The 0-CFA propagation is otherwise unchanged: trace `Closure` values through bindings, captures, returns, and into call positions. The only difference is that two different bindings flowing into the same parameter position from two different call sites stay separate.

Capture-chain propagation still applies (if `__lifted_N`'s capture is called, the enclosing function's corresponding parameter is HO at that callee's call sites).

### lambda_specialize (new behavior)

For each HO call site `c` with lambda set `S_c`:

1. Look up or create a specialized clone of the callee, keyed on `(callee_func, S_c)`.
2. In the clone, substitute the HO parameter's type with the tag union `S_c` (or with the singleton variant if `|S_c| == 1`).
3. Rewrite the call site to target the clone, and the closure-passing argument to construct the appropriate tag variant.
4. If the clone itself contains HO calls whose lambda sets depend on the substituted parameter, recurse — those inner call sites now have known sets too.

After specialization there are no `Closure` nodes and no HO parameters. Every call has a first-order target. The Phase E lowering single-variant shortcut fires whenever `|S_c| == 1` — which, with this pass, is the common case for `List.walk` and friends.

The keying step deduplicates: if two call sites pass the same lambda set to the same callee, they share one specialization.

### Downstream passes

Unchanged. `decl_info`, `reachable::prune`, SSA lower, opt, and eval all see a first-order module with normal tag unions. The Phase E machinery in `lower/` already handles the singleton-tag-union shortcut — no lowering changes needed.

## Implementation order

Each stage is independently testable.

### Stage 1 — call-site ids

Add a `CallSiteId` numbering pass (or extend existing AST nodes with a stable id). Verify it survives through `lambda_lift` so `lambda_solve` can key on it.

### Stage 2 — non-merging solve

Rewrite `lambda_solve` to track `call_site_id → lambda_set` without bidirectional merging. Capture-chain propagation stays. Verify on a small program with two `List.walk` call sites carrying different closures that the two sets stay separate.

### Stage 3 — per-call-site specialization

Rewrite `lambda_specialize` to clone callees per call site. Drop the `__apply_K` dispatcher synthesis (the dispatch falls out of pattern matching on the cloned signature's tag union parameter). Verify that singleton sets produce direct calls and multi-variant sets produce normal `if … is …` dispatch.

### Stage 4 — recursion

Handle HOFs that pass closures to other HOFs. The cloned callee may itself have HO call sites whose sets are now resolved; recurse the specialization. Verify with a `compose : (b -> c), (a -> b) -> (a -> c)` style example.

### Stage 5 — verification

Pin tests asserting:
- `walk_singleton_no_dispatcher` — a `List.walk` call with a single concrete closure produces no `__apply_K` and no payload heap alloc.
- `walk_heterogeneous_tag_dispatch` — a position receiving two different closures gets a 2-variant tag union, dispatched without heap.
- `compose_specialized_through_chain` — nested HO calls specialize transitively, no residual HO parameters.

### Stage 6 — cleanup

Delete the merged-set data structures and dispatcher-synthesis code in `lambda_specialize`. Remove the `_K` apply naming convention from `decl_info` and `reachable::prune`. Update `notes/compiler-passes.md` to reflect the new behavior.

## Trade-offs

**Code-size growth.** Per-call-site cloning duplicates HOFs. For Ori — total, no general recursion, small programs — this is fine; the same trade-off Rust mono accepts. If it ever isn't, the escape valve is opt-in *erasure* (typed function pointer + opaque captures pointer) for specific positions, à la Rust `dyn`. Not in scope for this plan.

**Specialization key equivalence.** Two call sites producing structurally equal lambda sets should share one specialization. Naive pointer equality on the set value won't work — we need structural equivalence, with care around recursive sets. Same problem the Roc RFC discusses for type-specialization keys; same solution (compare structurally, optionally intern). Probably defer until measured.

**Abilities / dispatch tables.** Out of scope. Ori doesn't have abilities; this plan is purely about closures.

## Non-goals

- No new IR.
- No changes to SSA lower.
- No changes to RC/FBIP.
- No erasure / `dyn` story.
- No incremental compilation or per-module caching.

## Open questions

- Do we need a `CallSiteId` newtype, or can existing expression-position info do the job? (Probably the latter — every `Call` AST node already has a unique position.)
- Specialization clones may produce many functions with similar bodies. Is some merging worthwhile after the fact, or does dead-code elimination clean it up well enough? Probably the latter, but verify with a real program.
- How do we cap recursive specialization for self-referential HO chains? Termination should follow from total recursion, but worth sanity-checking once the implementation exists.
