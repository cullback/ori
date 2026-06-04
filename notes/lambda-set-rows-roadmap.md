# Roadmap: lambda-set-rows + Core completion

Extend `Type::Arrow(args, ret)` to `Type::Arrow(args, ret, lambda_set)`
where `lambda_set` is a row variable tracking which closure tags can
flow through the function position. Roc's design. Closes a large
fraction of the workaround surface that exists today because schemes
say "Arrow" while bodies need "this specific closure-tag-union."

This roadmap is the planning artifact. See
`notes/lambda-set-specialization.md` for the language-level design
(unchanged); this file is *how to ship it*.

## Why now

The pre-infer lambda lift on the `lambda-rewrite` branch (June 2026)
left three workarounds in place because the alternative was a
multi-week type-system project:

1. `lower::to_slots`' Multi→Single materialization for HO call
   boundaries — schemes carry `Type::Arrow` (1 RcPtr slot expected)
   while closure values are multi-slot, so we wrap them in a heap
   shell.
2. `lambda::narrow::retype_scheme_params` — rewrites HO param
   positions in cloned schemes from Arrow to closure-union after
   the fact, so lower can see the shape.
3. `mono::SpecRequest::extra_mapping` + transparent-aware
   `extract_substitution_with` + `Scheme::var_concretes` — three
   side-channels carrying type info that the scheme itself should
   have carried structurally.

Each workaround exists *because* schemes can't say "the closure that
flows here is one of these tags." Lambda set rows fix that at the
type system level; the workarounds collapse.

## Surface area

From the codebase survey:

| Site type | Count | Concentrated in |
|---|---|---|
| `Type::Arrow(...)` construction | 42 | infer.rs (19), mono.rs (8), specialize.rs (5) |
| `Type::Arrow(p, r)` pattern matches | 22 | specialize.rs (5), narrow.rs (3), engine.rs (4) |
| Closure construction sites | 1 | infer.rs (Closure handler) |
| Closure use sites (HOF call) | implicit | every method-call/call on a function value |

The row-polymorphism template already exists in `Type::Record` and
`Type::TagUnion`'s `rest: Option<Box<Type>>` field. We mirror it.

## Status (as of 2026-06-04)

  - **A**: shipped. `Type::Arrow` extended; all engine.rs internals
    handle the new field; 67 sites mechanically updated.
  - **B**: shipped. `ExprKind::Closure` produces an Arrow with a
    closed-singleton row. Eta-expanded closures populate the same way.
  - **C**: shipped. `unify_lambda_sets` merges closed singletons by
    union (lambda-set semantics, unlike value tag unions). Every
    Arrow construction site now uses `engine.fresh_arrow` for an
    open row. `mono::collect_lambda_set_vars` excludes row vars from
    mangled names.
  - **D**: shipped. `extract_substitution_with` recurses through the
    Arrow's lambda set, so the per-call-site closure-set value flows
    into `args` (the spec_map key). Two call sites with different
    closure sets now naturally produce different mono specializations.
  - **E (partial)**: `lower::expand_slots` reads closure shape from
    the Arrow's row (singleton → decompose, multi → D2). **Full
    narrow delete blocked**: `lambda::specialize` still creates ONE
    shared TagDecl per lambda-set across all mono specs of the HOF,
    so the closure VALUE flowing into a mono spec carries the merged
    tag-union TYPE. Lower's value-side construction then takes the
    multi-variant D2 shape regardless of the Arrow row's singleton
    content. Fixing this needs either per-mono-spec TagDecls from
    specialize, or mono to splice closure-tag rewrites into the body
    alongside type substitution. `narrow.rs` stays for now.
  - **F (partial)**: empirically removed each workaround in turn.
    `Scheme::var_concretes` deleted — fully subsumed by row tracking.
    The others (extra_mapping, transparent-aware extract,
    apply_mapping Record-merge-rest, lower shell-wrap) are
    **load-bearing for transparent newtypes** like `Set` —
    independent of lambda-set rows, would need their own dedicated
    cleanup. Shell-wrap specifically also blocked by the same
    specialize-shared-TagDecl issue as full E.
  - **G**: shipped (roadmap kept current).
  - **H (partial)**: List.walk_until + other stdlib HOFs not yet
    ported. Significant new SSA-loop work (~50 lines) — deferred.
  - **I**: shipped trivially — `Stmt::Guard` was already desugared
    in `lower_block`'s early-out. Confirmed no current test hits the
    "not yet supported" arm.
  - **J**: not started. Local-receiver method calls still bail at
    `lower.rs:420`.
  - **K**: shipped. Added `Expr::Cast` variant; unary numeric
    conversions (`to_u8`, `from_u8`, `to_u64`, `to_i64`, `to_bits`,
    `from_bits`) now lower through Core.
  - **L (blocked)**: tried `binder_slots.len()==1 && slot_tys.len()>1`
    → bind to wrapper RcPtr. Removed the original error but pushed
    the failure downstream (nested patterns need multi-slot locals
    or materialization). Full fix needs `flatten_patterns` and/or
    Core `Ctx::locals` to support multi-slot binders. Deferred.
  - **L+**: structural constructors (uppercase Call targets not in
    declared TypeAnnos) now emit `Expr::Con` in Core instead of
    `Expr::App`. Closes Pos/Neg/Wrapped/Wrap-style patterns.
  - **M, N, O**: not started.

**Test coverage on Core: 82.9% → 86.4%** (9 more tests through
Core, no regressions). All 308 tests pass throughout.

### Phase L's sub-fixes that shipped

  - Structural constructors (uppercase Call targets with no
    declared TypeAnno) emit `Expr::Con` instead of `Expr::App`.
    Closes Pos/Neg/Wrapped/Wrap-style patterns. (+4 tests)
  - `lower_destructure` handles Record patterns by reordering
    fields to the canonical sorted-by-name slot order, then
    delegating to the existing Tuple-shaped binding logic. (+3 tests)
  - Match arm binder for multi-slot field bound by a single source
    name loads the wrapper RcPtr at the payload offset (multi-slot
    field data lives in a sub-heap object). Removes the "slot count
    mismatch" error class for Ok/Boxed/etc. but downstream tests
    still bail at "unbound Var" — see below.
  - Phase-E scrutinee dispatch handles N≥3 slots (single-variant
    union with N fields fanned out). Closes 2 of 4 "Match scrutinee
    produced 3 slots" fallbacks.

### Remaining cluster (architectural blockers)

After this session, the residual ~31 fallbacks cluster into:

  - **Multi-slot locals in Core's to_ssa** (~9 tests): nested
    patterns (`Boxed(Ok(x))`), Let bindings whose value produces 2
    slots for 1 binder. `flatten_patterns` introduces sub-pattern
    binders that the multi-slot field wrapper RcPtr doesn't satisfy.
    Fix: extend `to_ssa.ctx.locals` from `HashMap<SymbolId, Value>`
    to `HashMap<SymbolId, Vec<Value>>` (mirror `lower.ctx.locals`),
    OR materialize multi-slot binders into a heap shell that
    downstream code can deref.

  - **`List.walk_until` Core port** (~5 tests): substantial new
    SSA loop with Break/Continue tag inspection. Attempted in this
    session but reverted — the Eq-on-tag in the new loop seemed to
    break unrelated string-interpolation tests in a way that needs
    more investigation. The variant + lower arm + ~100 lines of SSA
    emission would fit in a focused 1–2 day session.

  - **specialize per-set TagDecl refactor** (~5 tests for ListWalk
    multi-slot + apply arity mismatches): the same blocker that
    prevented full Phase E delete + Phase F shell-wrap removal.
    `lambda::specialize` emits ONE TagDecl per lambda-set across
    all mono specs of an HOF; the closure VALUE then carries the
    merged tag-union TYPE and lower's value-side construction takes
    the multi-variant D2 shape regardless of the singleton row.

  - **Validation warning cluster** (~7 tests): "RcPtr vs I64 return
    type", "branch arg type mismatch I64 vs RcPtr". Subtle scheme/
    type misalignment in the HOF path. Likely also relates to the
    specialize per-set blocker.

  - **Long tail of 1-off issues**: `Wrap` fieldless scrutinee with
    binders, "expected single slot for ExprKind Tuple", a couple of
    transparent-newtype destructure cases.

### Suggested next session

1. **Multi-slot `to_ssa.locals`** (1–2 days) → unblocks ~9 tests
   in the nested-pattern cluster. Lowest-architecture-investment
   single change that touches the most tests.
2. **specialize per-set TagDecls** (2–3 days) → unblocks ~5 tests
   AND completes Phases E+F. Higher leverage but deeper change.
3. **List.walk_until port** (1–2 days) → +5 tests. Independent
   of the other two.

These three alone would close ~19 of the residual 31 fallbacks,
bringing Core coverage to ~94%.

## What lambda-set rows actually delivered

Quantifiable wins from this project (Phases A–G):

  - **Truthful schemes**: every Arrow position in `func_schemes`
    carries the closure set that can flow through it.
  - **Per-call-site specialization**: mono naturally produces
    distinct apply specs for distinct closure sets, without narrow's
    cloning machinery doing the work upstream of mono. (narrow's
    clone path is now algorithmically redundant — it stays only
    because of the specialize-shared-TagDecl coupling.)
  - **`Scheme::var_concretes` deleted**: ~50 lines + a side-channel
    that existed only because the previous architecture couldn't
    track late-resolved type-arg bindings structurally.
  - **`lower::expand_slots`** reads closure shape directly from the
    Arrow row — no longer dependent on narrow's `retype_scheme_params`
    for the slot-count answer.

What this project did **not** deliver (because of the
specialize-shared-TagDecl coupling and the transparent-newtype
foreign-var cluster):

  - Full deletion of `lambda::narrow` (~1300 lines).
  - Removal of `lower::to_slots` shell-wrap.
  - Removal of `SpecRequest::extra_mapping`, transparent-aware
    extract, `apply_mapping` Record-merge-rest hack.

The path to those is the **lambda::specialize per-set TagDecl
refactor** (a focused 1–2 day project that emits one TagDecl per
mono-spec instead of one shared TagDecl across mono-specs of the
same HOF).

## Suggested follow-up before tackling H+

The biggest remaining structural blocker is `lambda::specialize`'s
shared-TagDecl model. A focused follow-up:

  1. Walk the mono'd module per `__lifted_N` function name.
  2. For each mono spec of an HOF, find the closure tags actually
     reachable (by walking the spec body for `Closure {func, ...}`
     constructors, or reading the spec's HO param Arrow row).
  3. Emit one TagDecl per `(hof_spec, ho_param_position)` pair.
  4. Update the call sites in that spec's body to use the spec's
     TagDecl tag.
  5. Update `__apply_K`'s synthesized body to dispatch over the
     spec's tags.

After that lands: Phase E's full narrow delete, F's shell-wrap
removal, and a much smaller narrow.rs (maybe 200 lines vs 1300).
Estimated 1–3 days.

If that work is deferred, Phases H–O can still proceed
independently — they're about Core IR completion, not the
lambda-set machinery.

## Phases

Each phase ends with **all 308 tests green** so bisection works.
Phases A–B are pure additive; C is the risky one; D–F are where the
real simplifications land.

### Phase A — mechanical extension (1–2 days)

Add the field. Default to closed-empty at every site. Zero behavior
change.

- `engine.rs`: add `pub type LambdaSet = Option<Box<Type>>`. Change
  `Type::Arrow(Vec<Type>, Box<Type>)` to
  `Type::Arrow(Vec<Type>, Box<Type>, LambdaSet)`.
- ~42 construction sites: pass `None` (closed empty row).
- ~22 pattern matches: `Type::Arrow(p, r)` → `Type::Arrow(p, r, _)`.
- `engine.rs::unify` for Arrow: ignore the row (treat as `_`).
- `engine.rs::free_vars`, `occurs_in`, `display_type`: recurse through
  the row.

**Tests green.** Pure refactor. Fully reversible.

### Phase B — populate rows at construction (2–3 days)

Now produce real row info. Still no consumer reads it.

- **infer's `ExprKind::Closure` handler**: the returned Arrow's row =
  `Some(TagUnion{tags: [(__ClosureTag_N, [])], rest: None})` — a
  closed singleton row identifying the closure's tag.
- **lambda inference points** (post-eta in `post_infer`): same.
- **HOF param positions in method/builtin schemes**: row =
  `Some(Var(fresh))` — open, waiting for unification.
- **`func_schemes` rebuild** at infer-end: preserve the row through
  `engine.resolve`.
- **`mono::normalize_type`**: preserve the row (don't force-close).

**Tests green.** Rows carry truthful info nowhere read yet.

### Phase C — row-aware unification + closing (2–3 days) — **HIGH RISK**

The hard part. Mirror `unify_records` / `unify_tag_unions` for Arrow
rows. Two closures into the same HOF param merge into a 2-tag union.

- `unify_arrows`: after unifying params + ret, unify the two rows
  using the existing TagUnion row machinery (the row content *is* a
  TagUnion of closure tags).
- Add Arrow analog of `close_open_tag_row` in `resolve_and_verify`:
  remaining open Arrow rows close to whatever set was observed.
- Handle recursion carefully: `(a -> b) -> c` has a row on the outer
  Arrow AND a row on the inner Arrow.

**Tests green.** Schemes now carry accurate lambda-set info on every
Arrow position. Nothing downstream uses it yet.

**Risk:** Row unification is subtle. Plan a day of debugging edge
cases (recursive Arrows, partially-closed rows, eta'd closures with
no captures). The `lambda-rewrite` branch's `lambda::solve` pass is
the reference for "what's a correct lambda set" — its results should
match what unification produces.

### Phase D — mono specializes on lambda set (3–5 days)

This is where the architecture changes. mono's `spec_map` key gains a
lambda-set signature.

- Change `spec_map: HashMap<(String, Vec<Type>), SymbolId>` to
  `HashMap<(String, Vec<Type>, Vec<LambdaSetSig>), SymbolId>` where
  `LambdaSetSig` is a canonical sorted list of tag names per HO param
  position.
- `specialize_by_sym`: extract lambda set from concrete arrow's row,
  use as part of the key.
- `process_request`: bake the lambda set into the body — every Arrow
  position in the body's substituted types reflects the call site's
  set.

After this phase, two call sites of `walk_until` with different
closures get different mono'd versions naturally — without
`lambda::narrow` doing per-call-site cloning.

### Phase E — collapse narrow + retype_scheme_params (2–3 days)

`narrow.rs` is ~1300 lines. With Phase D, most of it is dead.

- Delete `collect_sites` + `clone_expr` per-call-site cloning — mono
  row-specialization does this.
- Delete `retype_scheme_params` — schemes are already correct.
- Keep whatever singleton-tag-decl synthesis is genuinely additive
  (likely just the apply-function specialization for singleton sets;
  move to `specialize.rs` if it's small).
- Expected ~800 lines deleted.

### Phase F — remove HO workarounds (1–2 days)

The payoff. Workarounds installed because schemes lied are no longer
needed.

- `lower::to_slots`: delete the Multi→Single materialization for HO
  call boundaries. HO params now have multi-slot scheme types; call
  sites pass multi-slot directly.
- `mono::SpecRequest::extra_mapping`: delete. Row inference puts the
  info structurally into the scheme.
- `mono::extract_substitution_with`'s transparent-aware unwrap: keep
  for genuine transparent newtypes; drop if rows make it redundant.
- `Scheme::var_concretes`: delete. Late-resolved vars no longer leak
  because the row carries the info.
- `mono::apply_mapping` Record-merge-rest hack: re-evaluate; rows
  should make this case not arise.

### Phase G — doc + final cleanup (1 day)

- Update `notes/lambda-set-specialization.md`: collapse the "DONE
  with a pivot" + "(superseded)" sections into one "DONE" section
  describing the final shape.
- Run `cargo test`, `cargo clippy --all`, fix nits.
- Decide whether to squash phases A–F into one commit or keep
  granular (granular is fine; phases are bisectable).

## Total estimate: 12–19 days

One person, focused. Wide range because Phase C can eat 1–4 days
depending on how clean the row-unification mirror is.

## What this delivers

- **Truthful schemes.** Every Arrow position in `func_schemes` says
  exactly which closures can flow through it.
- **No shell-wrap.** HO call boundaries pass multi-slot closure values
  directly — same shape as records-as-args.
- **Per-call-site specialization for free.** mono naturally produces
  one version per lambda set; `lambda::narrow` collapses to almost
  nothing.
- **Three workarounds gone.** `extra_mapping`, `var_concretes`,
  Multi→Single materialization — all delete-able.
- **Net delta:** −1500 to −3000 lines.

## What this does NOT deliver

This roadmap closes the **closure-shape** fallbacks in the Core IR
pipeline. Several **independent** fallback categories remain — be
honest about them.

### Core fallbacks closed by lambda-set-rows

These all fall back today because Core doesn't know the multi-slot
shape of closure values:

- Closure passed as a function parameter (non-singleton dispatch).
- Closure returned from a function.
- Closure stored in a record or tuple field.
- Closure as a list element.
- `ListWalk` with multi-slot elements (closures count).

After lambda-set-rows: schemes tell Core the actual closure shape.
Core's existing SROA machinery handles them like any other multi-slot
aggregate.

### Core fallbacks that REMAIN after lambda-set-rows

Independent work, not in scope of this roadmap:

1. **Stdlib intrinsics without Core inlining.** Core handles
   `List.walk`, `List.set`, `List.append`, `List.range`, `List.len`,
   `List.get`. Everything else (`List.map`, `List.filter`, user
   library functions) falls back because Core can't inline their
   internals. Fix requires either per-function hand-lowering or
   `@cata`/`@build` annotations on stdlib functions (open question
   in `notes/core-ir.md`).

2. **Guard expressions.** `Stmt::Guard` (`let x = ... if cond`) not
   yet lowered through Core. Independent threading work in
   `passes/core/lower.rs`.

3. **`__builtin.*` intrinsics.** Numeric builtins (`I64.add`, etc.)
   route through a separate path Core doesn't handle. Mostly fine
   because the existing intrinsic path is hot, but means Core can't
   inline arithmetic across stdlib calls.

4. **Local-receiver method calls.** `x.method(...)` where `x` is a
   local value (not a type prefix). Core only handles
   type-qualified calls. Requires modeling value-as-receiver
   dispatch.

5. **Nested pattern guards / deep destructuring.** Some pattern
   shapes (`lower.rs:1728, 1746`) aren't handled in Core's match
   lowering.

6. **`Fold` / `Lambda` / `Closure` AST nodes at Core entry.** Should
   never happen post-lift; signals a pre-Core pipeline bug. After
   lambda-set-rows, the `Closure` arm in Core can be updated to
   actually lower closures (not just bail) — this is part of what
   the rows enable.

**See Phases H–O below** for the detailed residual plan that closes
each of these categories.

## Phases H–N: residual to zero Core fallbacks

After A–G, the structural project is done. The remaining work is a
series of focused passes per fallback category. Each gets the same
"green at every phase" treatment.

Before starting H, instrument the fallback counter:

- Run `cargo test --quiet -- --ignored zzz_core_coverage_summary 2>&1`
  to see current fallback reasons + counts. The output enumerates the
  exact categories below with empirical weights — use it to prioritize
  if the estimates here are wrong.
- Add similar instrumentation for the AOC / stdlib test programs so
  we see real-world fallback rates, not just unit-test rates.

### Phase H — stdlib HOFs in Core (1 week)

The biggest residual category. Core knows `List.walk`, `List.set`,
`List.append`, `List.range`, `List.len`, `List.get`. Most HOF-rich
real-world code uses the others, which all fall back.

After Phase F, multi-slot closures work in Core, so this is now
unblocked.

Add a Core arm per stdlib HOF:

- `List.map` — fuses to a single Build with element-wise lambda apply.
- `List.filter` — fuses to a Build with predicate-gated push.
- `List.fold` / `List.foldr` — same shape as `List.walk` but with
  different argument order; mostly mechanical.
- `List.concat` / `List.concat_map` — Build with nested push.
- `List.zip` / `List.unzip` — parallel iteration over two trios.
- `List.take` / `List.drop` — bounded Build.
- `List.any` / `List.all` — short-circuiting fold.
- `Set.from_list`, `Set.walk`, `Map.from_list`, `Map.walk` — same
  story for Set/Map. Plus their internals (insert, lookup) once
  Core handles the iteration.

Split per-function. Each adds one Core arm + one test. Order by
empirical fallback frequency from the coverage summary.

**Sub-phases H1–HN.** Estimated 1–2 days per HOF; ~10 HOFs.

### Phase I — `Stmt::Guard` in Core (2 days)

`let x = ... if cond` (a guard statement). Currently `passes/core/lower.rs:1272`
bails. Thread guard evaluation through Core's match lowering:

- A guard inside a match arm becomes an extra branch on the inferred
  condition's Bool — collapse to a Match with two arms (the guarded
  body, and fall-through to the next pattern).
- A top-level guard in a block becomes a one-arm if.

The shape is already present in existing-lower; mostly transcription.

### Phase J — local-receiver method calls in Core (2–3 days)

`x.method(...)` where `x` is a local value (not a type prefix like
`I64.add`). Currently `passes/core/lower.rs:420` bails. Resolve
through the same mechanism existing-lower uses: look up the method
on the receiver's resolved type, emit a direct call to the mangled
method name.

Most of the dispatch logic already exists in mono's `MethodCall`
handler — Core just needs to read the `resolved` field set by infer's
`post_infer` and emit a plain Call.

### Phase K — `__builtin.*` intrinsics in Core (2 days)

Numeric builtins (`I64.add`, `U32.shl`, `F64.sqrt`, etc.) currently
route through existing-lower's intrinsic path. Add a Core arm that
emits the corresponding SSA primitive directly.

Most of these are 1-instruction lowerings; mechanical. The
`crate::numeric` module enumerates them — table-drive the Core arm
from that.

### Phase L — deep pattern destructuring in Core (2–3 days)

Nested patterns like `: Cons(Cons(x, _), _) then ...` and record
patterns with subpatterns currently bail at `passes/core/lower.rs:1728`,
`:1746`. Extend Core's `Match` lowering to handle:

- Nested Con patterns (recursive destructuring).
- Record patterns with non-trivial field subpatterns.
- List patterns with rest-bindings and nested element patterns.

Same shape as existing-lower's pattern matcher; transcription.

### Phase M — stdlib annotation system (1 week, optional)

A scalable alternative to Phase H's per-function arms. Add
`@cata`/`@build` annotations to stdlib functions, with a Core arm
that interprets them generically:

- `@cata` means "this function is a fold over the first argument" —
  Core fuses it with upstream Builds.
- `@build` means "this function constructs a list" — Core fuses it
  with downstream catas.
- Together they implement deforestation generically.

This is the right long-term shape — adding a new stdlib HOF then
only requires the annotation, not a Core arm. But it's optional: if
Phase H gets us to "everything important works," skip M.

Discussion in `notes/core-ir.md` line 305+ on the annotation design
and the empirical gate ("measure fusion benefit on a real program")
that this would unlock.

### Phase N — retire existing-lower (3–5 days)

The payoff. With Core handling everything, the AST→SSA fallback
path can go.

- Delete `src/lower/` entirely. ~3000 lines.
- Delete the fallback in `main.rs::compile` — Core is the only path.
- Delete `compile_until_lower` and any test-only paths that exist
  because of the fallback.
- Delete `mono.singletons`, `mono.tag_targets` (these exist mostly
  for existing-lower's walk emission; Core uses its own resolution).
- Delete `ssa::validate`'s warning-vs-error distinction — Core never
  emits warnings.

Run full suite. Run AOC programs. Run any benchmarks. If anything
regresses on output (correctness) or performance, file a follow-up;
don't restore existing-lower.

This is the moment the project is "done."

### Phase O — final cleanup + docs (1 day)

- Update `CLAUDE.md` to reflect the single-pipeline architecture.
- Update `notes/core-ir.md` with the empirical fusion results.
- Update `src/lower/README.md` → delete or point at `src/passes/core/`.
- Squash if desired.

## Full project: total estimate

| Block | Phases | Days |
|---|---|---|
| Structural: lambda-set-rows | A–G | 12–19 |
| Residual: stdlib HOFs | H1–HN | 10–20 |
| Residual: guards | I | 2 |
| Residual: local-receiver methods | J | 2–3 |
| Residual: __builtin intrinsics | K | 2 |
| Residual: deep patterns | L | 2–3 |
| Optional: annotation system | M | 5–7 |
| Retire existing-lower | N | 3–5 |
| Final cleanup | O | 1 |
| **TOTAL (without M)** | | **34–55 days** |
| **TOTAL (with M)** | | **39–62 days** |

One person, focused. Call it **7–12 weeks** wall-clock if it gets
priority, or 3–6 months if it's part-time alongside other work.

## Sequencing rationale

Lambda-set-rows (A–G) is the right first block because:

1. It closes the **largest single category** of Core fallbacks (HO
   closures across every shape).
2. It deletes the most ad-hoc surface (~1500–3000 lines of
   workarounds and side-channels).
3. It's the **only structural piece** left — once truthful schemes
   exist, H–O are grinding work with no architectural decisions
   blocking them.

H–O are sequenced by empirical impact:

- **H first** because stdlib HOFs are the dominant fallback category
  in real programs. Use the coverage summary to validate ordering.
- **I, J, K, L** are independent — work them in parallel if you
  have multiple people, or by empirical weight if solo.
- **M is optional** — only do it if Phase H feels too verbose, or
  if you want the deforestation benefits.
- **N** is the destination. Don't start until H–L are solid and
  the coverage summary shows zero fallbacks across the test suite.

## What "done" looks like

After Phase N:

- One pipeline. `lower::lower` deleted. `main.rs::compile` has no
  fallback branch.
- Every test passes through Core.
- `ssa::validate` is the only correctness gate post-lowering — and
  it passes on every program.
- The compiler is meaningfully smaller (~5000 lines deleted
  total across A–N).
- Core IR's optimization opportunities (deforestation, fold fusion)
  become tractable to add — the SSA after Core is in a more uniform
  shape than the SSA after existing-lower.
