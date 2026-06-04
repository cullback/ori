# Lambda set rows: implementation roadmap

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

### Order to tackle the residual

If "Core is complete with zero fallbacks" is the ultimate goal, here's
the suggested follow-on after lambda-set-rows:

| After this roadmap | Estimated effort | Why it matters |
|---|---|---|
| Closure as param/return/aggregate field | (lands with lambda-set-rows) | huge swath of HO programs |
| Stdlib `List.map` / `List.filter` / `List.fold` in Core | 1 week | covers most HOF use cases |
| Guard expressions | 2 days | unblocks pattern-heavy code |
| Local-receiver method calls (`x.method()`) | 2–3 days | common syntactic pattern |
| Stdlib intrinsic annotation system (`@cata`/`@build`) | 1 week | scalable, unblocks future stdlib |
| Deep pattern destructuring in Core | 2–3 days | edge cases |

**Total residual scope after lambda-set-rows: ~3–4 weeks of focused
work to fully retire the AST→SSA fallback path.**

## Sequencing decision

Lambda-set-rows is the right next step because:

1. It closes the **largest single category** of Core fallbacks (HO
   closures across every shape).
2. It deletes the most ad-hoc surface (~1500–3000 lines of
   workarounds and side-channels).
3. The remaining residual is straightforward grinding (per-intrinsic
   Core lowering, pattern surface) — no further type-system work
   needed.

After this lands, "drive Core fallbacks to zero" becomes a series of
small focused passes rather than a structural project.
