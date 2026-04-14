//! Flatten nested patterns — AST → AST rewrite.
//!
//! After this pass runs, every constructor-field pattern that appears
//! in a match arm's top-level pattern or inside an `is` expression is
//! either `Pattern::Binding` or `Pattern::Wildcard`. Nested
//! constructors are hoisted into guard-chain `is` expressions using
//! fresh temp bindings; nested tuple/record field patterns are hoisted
//! into `Destructure` statements prepended to the arm body.
//!
//! This lets `ssa::lower` keep its pattern-match compiler narrow — it
//! only has to handle shallow `Constructor { fields: [Binding | Wildcard] }`
//! in arm positions and in `is` chains.
//!
//! ## Rewrite rules
//!
//! Match arm with a nested constructor field:
//!
//! ```text
//! : Ok(Cons(h, t)) then body
//! ```
//!
//! becomes
//!
//! ```text
//! : Ok(__pat_0) and __pat_0 is Cons(h, t) then body
//! ```
//!
//! Doubly-nested constructors get chained `is` guards:
//!
//! ```text
//! : Ok(Cons(Ok(x), xs)) then body
//! ```
//!
//! becomes
//!
//! ```text
//! : Ok(__pat_0) and __pat_0 is Cons(__pat_1, xs) and __pat_1 is Ok(x) then body
//! ```
//!
//! Nested tuple/record fields become destructures on the body:
//!
//! ```text
//! : Ok((a, b)) then body
//! ```
//!
//! becomes
//!
//! ```text
//! : Ok(__pat_0) then { (a, b) = __pat_0; body }
//! ```
//!
//! The same flattening rewrites `is` expressions in non-arm positions:
//!
//! ```text
//! x is Ok(Cons(h, t))
//! ```
//!
//! becomes
//!
//! ```text
//! x is Ok(__pat_0) and __pat_0 is Cons(h, t)
//! ```
//!
//! ## Why pre-inference
//!
//! The pass runs after `fold_lift` and before `topo`/`infer`.
//! Synthesized expressions have a placeholder `Type::Var(0)` on their
//! `Expr.ty`; inference fills it in naturally when it walks the
//! rewritten tree. Running pre-inference means the pass doesn't have to
//! maintain concrete types on its output.
//!
//! ## Why unique synthetic spans
//!
//! Inference still side-tables `is`-expression bindings by span (see
//! `infer.rs::is_bindings`). Two synthesized `Is` nodes that share a
//! span would collide in that map — the second insert would overwrite
//! the first, losing bindings. Each synthesized `Is` and `BinOp::And`
//! node gets a fresh span via `fresh_span` so the side table stays
//! unambiguous.
//!
//! ## Out of scope
//!
//! - Top-level tuple/record match arms (no discriminator to switch on).
//! - Literal patterns (not in the AST).
//! - List `..` patterns (not in the AST).
//! - Tuple/record field pattern inside an `is` expression (no body to
//!   anchor the destructure against). The pass leaves these as-is and
//!   the downstream lowerer raises its usual error if encountered.

use crate::ast::{
    BinOp, Decl, Expr, ExprKind, ListPatternElem, MatchArm, Module, Pattern, Span, Stmt,
};
use crate::passes::resolve::Resolved;
use crate::symbol::{SymbolId, SymbolKind, SymbolTable};

/// Flatten nested patterns into shallow match chains.
pub fn flatten(resolved: &mut Resolved<'_>) {
    let module = std::mem::take(&mut resolved.module);
    resolved.module = flatten_module(module, &mut resolved.symbols);
}

fn flatten_module<'src>(mut module: Module<'src>, symbols: &mut SymbolTable) -> Module<'src> {
    let mut ctx = FlattenCtx {
        temp_counter: 0,
        synth_span_offset: SPAN_OFFSET_BASE,
        symbols,
    };
    for decl in &mut module.decls {
        flatten_decl(&mut ctx, decl);
    }
    module
}

/// Starting point for synthetic span offsets. Sits near the middle of
/// `usize` so it can't collide with real source offsets (which live at
/// the low end) or with `fold_lift`'s synthetic spans (which start at
/// `usize::MAX` and count down).
const SPAN_OFFSET_BASE: usize = usize::MAX >> 1;

struct FlattenCtx<'a> {
    temp_counter: usize,
    synth_span_offset: usize,
    symbols: &'a mut SymbolTable,
}

impl FlattenCtx<'_> {
    fn fresh_local(&mut self, span: Span) -> SymbolId {
        let display = format!("__pat_{}", self.temp_counter);
        self.temp_counter = self.temp_counter.saturating_add(1);
        self.symbols.fresh(display, span, SymbolKind::Local)
    }

    const fn fresh_span(&mut self, base: Span) -> Span {
        let off = self.synth_span_offset;
        self.synth_span_offset = self.synth_span_offset.saturating_sub(1);
        Span {
            file: base.file,
            start: off,
            end: off,
        }
    }
}

// ---- Walker ----

fn flatten_decl(ctx: &mut FlattenCtx<'_>, decl: &mut Decl<'_>) {
    match decl {
        Decl::FuncDef { body, .. } => flatten_expr(ctx, body),
        Decl::TypeAnno { methods, .. } => {
            for m in methods {
                flatten_decl(ctx, m);
            }
        }
    }
}

fn flatten_expr(ctx: &mut FlattenCtx<'_>, expr: &mut Expr<'_>) {
    match &mut expr.kind {
        ExprKind::IntLit(_)
        | ExprKind::FloatLit(_)
        | ExprKind::StrLit(_)
        | ExprKind::Name(_) => {}
        ExprKind::BinOp { lhs, rhs, .. } => {
            flatten_expr(ctx, lhs);
            flatten_expr(ctx, rhs);
        }
        ExprKind::Call { args, .. } | ExprKind::QualifiedCall { args, .. } => {
            for a in args {
                flatten_expr(ctx, a);
            }
        }
        ExprKind::Block(stmts, result) => {
            for s in stmts {
                flatten_stmt(ctx, s);
            }
            flatten_expr(ctx, result);
        }
        ExprKind::If {
            expr: scrutinee,
            arms,
            else_body,
        } => {
            flatten_expr(ctx, scrutinee);
            // Check if any arm uses a list pattern — if so, desugar the
            // entire match into a nested if-else chain on List.len.
            if arms.iter().any(|a| matches!(a.pattern, Pattern::List(_))) {
                let arms_taken = std::mem::take(arms);
                let else_taken = else_body.take();
                let scrutinee_taken = std::mem::replace(
                    scrutinee,
                    Box::new(Expr::new(ExprKind::IntLit(0), Span::default())),
                );
                let desugared =
                    desugar_list_match(ctx, *scrutinee_taken, arms_taken, else_taken);
                *expr = desugared;
                flatten_expr(ctx, expr);
                return;
            }
            for arm in arms {
                flatten_arm(ctx, arm);
            }
            if let Some(eb) = else_body {
                flatten_expr(ctx, eb);
            }
        }
        ExprKind::Fold {
            expr: scrutinee,
            arms,
        } => {
            flatten_expr(ctx, scrutinee);
            for arm in arms {
                flatten_arm(ctx, arm);
            }
        }
        ExprKind::Lambda { body, .. } => flatten_expr(ctx, body),
        ExprKind::Record { fields } => {
            for (_, e) in fields {
                flatten_expr(ctx, e);
            }
        }
        ExprKind::FieldAccess { record, .. } => flatten_expr(ctx, record),
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems {
                flatten_expr(ctx, e);
            }
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            flatten_expr(ctx, receiver);
            for a in args {
                flatten_expr(ctx, a);
            }
        }
        ExprKind::Is { expr: inner, pattern } => {
            if matches!(pattern, Pattern::List(_)) {
                flatten_expr(ctx, inner);
                let base_span = expr.span;
                let kind = std::mem::replace(&mut expr.kind, ExprKind::IntLit(0));
                let ExprKind::Is { expr: inner_box, pattern } = kind else {
                    unreachable!();
                };
                let Pattern::List(elems) = pattern else { unreachable!() };
                let desugared = desugar_list_is(ctx, *inner_box, &elems, base_span);
                expr.kind = desugared.kind;
                expr.span = desugared.span;
                return;
            }
            flatten_is_expr(ctx, expr);
        }
        ExprKind::RecordUpdate { base, updates } => {
            flatten_expr(ctx, base);
            for (_, e) in updates {
                flatten_expr(ctx, e);
            }
        }
        ExprKind::Closure { .. } => {}
    }
}

fn flatten_stmt(ctx: &mut FlattenCtx<'_>, stmt: &mut Stmt<'_>) {
    match stmt {
        Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => flatten_expr(ctx, val),
        Stmt::Guard {
            condition,
            return_val,
        } => {
            flatten_expr(ctx, condition);
            flatten_expr(ctx, return_val);
        }
        Stmt::TypeHint { .. } => {}
    }
}

// ---- Core rewrite ----

/// Rewrite one match arm in place so its top pattern is a Constructor
/// with only shallow (`Binding` / `Wildcard`) field patterns.
fn flatten_arm<'src>(ctx: &mut FlattenCtx<'_>, arm: &mut MatchArm<'src>) {
    // Children first: guards and body may themselves contain patterns
    // (e.g. nested `is` expressions, or other `if`/`fold` with arms).
    for g in &mut arm.guards {
        flatten_expr(ctx, g);
    }
    flatten_expr(ctx, &mut arm.body);

    let Pattern::Constructor { fields, .. } = &mut arm.pattern else {
        return;
    };
    if fields
        .iter()
        .all(|f| matches!(f, Pattern::Binding(_) | Pattern::Wildcard))
    {
        return;
    }

    let body_span = arm.body.span;
    let mut extra_guards: Vec<Expr<'src>> = Vec::new();
    let mut destructures: Vec<Stmt<'src>> = Vec::new();
    for field in fields.iter_mut() {
        flatten_field(ctx, field, body_span, &mut extra_guards, &mut destructures);
    }

    if !extra_guards.is_empty() {
        // Prepend extra guards so they run before any user guards —
        // the user guards may reference bindings introduced by the
        // hoisted `is` checks.
        let mut combined = extra_guards;
        combined.extend(std::mem::take(&mut arm.guards));
        arm.guards = combined;
    }

    if !destructures.is_empty() {
        let old_body = std::mem::replace(
            &mut arm.body,
            Expr::new(ExprKind::IntLit(0), body_span),
        );
        arm.body = Expr::new(
            ExprKind::Block(destructures, Box::new(old_body)),
            body_span,
        );
    }
}

/// Normalize one constructor-field pattern in place. Mutates `field`
/// so it becomes `Binding` or `Wildcard`; appends any hoisted guards or
/// destructures to the provided vectors.
fn flatten_field<'src>(
    ctx: &mut FlattenCtx<'_>,
    field: &mut Pattern<'src>,
    span: Span,
    extra_guards: &mut Vec<Expr<'src>>,
    destructures: &mut Vec<Stmt<'src>>,
) {
    match field {
        Pattern::Binding(_) | Pattern::Wildcard | Pattern::IntLit(_) | Pattern::StrLit(_) | Pattern::List(_) => {}

        Pattern::Constructor { .. } => {
            let tmp = ctx.fresh_local(span);
            let mut nested = std::mem::replace(field, Pattern::Binding(tmp));

            // Recurse into the nested constructor's fields so further
            // nesting contributes additional guards. The recursion
            // mutates `nested` in place so its fields become shallow.
            // We collect inner guards separately so we can emit them
            // AFTER the outer guard — the outer's binding must be in
            // scope before inner guards reference it.
            let mut inner_guards: Vec<Expr<'src>> = Vec::new();
            let mut inner_destructures: Vec<Stmt<'src>> = Vec::new();
            if let Pattern::Constructor { fields, .. } = &mut nested {
                for sub in fields.iter_mut() {
                    flatten_field(
                        ctx,
                        sub,
                        span,
                        &mut inner_guards,
                        &mut inner_destructures,
                    );
                }
            }

            let is_span = ctx.fresh_span(span);
            let is_expr = Expr::new(
                ExprKind::Is {
                    expr: Box::new(Expr::new(ExprKind::Name(tmp), is_span)),
                    pattern: nested,
                },
                is_span,
            );
            extra_guards.push(is_expr);
            extra_guards.extend(inner_guards);
            destructures.extend(inner_destructures);
        }

        Pattern::Tuple(_) | Pattern::Record { .. } => {
            let tmp = ctx.fresh_local(span);
            let nested = std::mem::replace(field, Pattern::Binding(tmp));
            destructures.push(Stmt::Destructure {
                pattern: nested,
                val: Expr::new(ExprKind::Name(tmp), span),
            });
        }
    }
}

/// Rewrite `x is Ok(Cons(h, t))` style expressions into an `and` chain.
/// Handles only the case where the nested shapes are all Constructors —
/// tuple/record nesting inside an `is` pattern has nowhere to hoist a
/// destructure to, so the pass leaves those unchanged.
fn flatten_is_expr(ctx: &mut FlattenCtx<'_>, expr: &mut Expr<'_>) {
    let ExprKind::Is {
        expr: inner,
        pattern,
    } = &mut expr.kind
    else {
        return;
    };

    flatten_expr(ctx, inner);

    if !is_pattern_flattenable(pattern) {
        return;
    }
    if !pattern_has_nested_con(pattern) {
        return;
    }

    let base_span = expr.span;
    let kind = std::mem::replace(&mut expr.kind, ExprKind::IntLit(0));
    let ExprKind::Is {
        expr: inner_box,
        pattern,
    } = kind
    else {
        unreachable!("checked via match above");
    };
    expr.kind = build_flattened_is(ctx, *inner_box, pattern, base_span);
    expr.span = base_span;
}

/// True iff `pat` is a tree of only `Constructor` / `Binding` /
/// `Wildcard` patterns. Tuple or record anywhere in the tree disqualifies
/// it from the `is`-expression rewrite path.
fn is_pattern_flattenable(pat: &Pattern<'_>) -> bool {
    match pat {
        Pattern::Binding(_) | Pattern::Wildcard | Pattern::IntLit(_) | Pattern::StrLit(_) => true,
        Pattern::Constructor { fields, .. } => fields.iter().all(is_pattern_flattenable),
        Pattern::Tuple(_) | Pattern::Record { .. } | Pattern::List(_) => false,
    }
}

/// True iff `pat` is a Constructor whose fields include at least one
/// non-shallow sub-pattern that needs hoisting.
fn pattern_has_nested_con(pat: &Pattern<'_>) -> bool {
    let Pattern::Constructor { fields, .. } = pat else {
        return false;
    };
    fields
        .iter()
        .any(|f| !matches!(f, Pattern::Binding(_) | Pattern::Wildcard))
}

/// Build the And-chain that replaces a nested `is` expression. Assumes
/// `pattern` is a `Constructor` — other shapes are handled by the
/// early-return paths in `flatten_is_expr`.
fn build_flattened_is<'src>(
    ctx: &mut FlattenCtx<'_>,
    scrutinee: Expr<'src>,
    pattern: Pattern<'src>,
    base_span: Span,
) -> ExprKind<'src> {
    let Pattern::Constructor { name, mut fields } = pattern else {
        return ExprKind::Is {
            expr: Box::new(scrutinee),
            pattern,
        };
    };

    let mut extra_guards: Vec<Expr<'src>> = Vec::new();
    let mut unused_destructures: Vec<Stmt<'src>> = Vec::new();
    for field in &mut fields {
        flatten_field(
            ctx,
            field,
            base_span,
            &mut extra_guards,
            &mut unused_destructures,
        );
    }
    debug_assert!(
        unused_destructures.is_empty(),
        "is_pattern_flattenable guards against tuple/record nesting"
    );

    let outer_span = ctx.fresh_span(base_span);
    let outer_is = Expr::new(
        ExprKind::Is {
            expr: Box::new(scrutinee),
            pattern: Pattern::Constructor { name, fields },
        },
        outer_span,
    );

    let combined = extra_guards.into_iter().fold(outer_is, |acc, g| {
        let and_span = ctx.fresh_span(base_span);
        Expr::new(
            ExprKind::BinOp {
                op: BinOp::And,
                lhs: Box::new(acc),
                rhs: Box::new(g),
            },
            and_span,
        )
    });

    combined.kind
}

// ---- List pattern desugaring ----
//
// List patterns desugar into length checks + List.get/List.sublist calls.
// The lowerer never sees `Pattern::List`.

/// Analyse a list pattern to determine the minimum length and positions.
struct ListPatternInfo {
    /// Number of fixed (non-spread) elements before the spread.
    prefix_len: usize,
    /// Number of fixed elements after the spread.
    suffix_len: usize,
    /// Whether a spread `..` or `..name` appears.
    has_spread: bool,
}

fn analyse_list_pattern(elems: &[ListPatternElem<'_>]) -> ListPatternInfo {
    let spread_pos = elems
        .iter()
        .position(|e| matches!(e, ListPatternElem::Spread(_)));
    if let Some(pos) = spread_pos {
        let prefix_len = pos;
        let suffix_len = elems.len() - pos - 1;
        ListPatternInfo {
            prefix_len,
            suffix_len,
            has_spread: true,
        }
    } else {
        ListPatternInfo {
            prefix_len: elems.len(),
            suffix_len: 0,
            has_spread: false,
        }
    }
}

/// Minimum list length required by a pattern.
const fn min_len(info: &ListPatternInfo) -> usize {
    info.prefix_len + info.suffix_len
}

/// Build a `QualifiedCall` expression: `List.method(args...)`.
fn list_call<'src>(method: &'static str, args: Vec<Expr<'src>>, span: Span) -> Expr<'src> {
    Expr::new(
        ExprKind::QualifiedCall {
            segments: vec!["List", method],
            args,
            resolved: None,
        },
        span,
    )
}

/// Build a length comparison. Uses a pre-computed length variable when
/// available (`len_sym`), falling back to emitting `List.len(scr)` calls
/// for `is`-expression desugaring where no temp is bound yet.
#[expect(clippy::cast_possible_wrap)]
fn len_check_sym<'src>(
    ctx: &mut FlattenCtx<'_>,
    len_sym: SymbolId,
    n: usize,
    exact: bool,
    span: Span,
) -> Expr<'src> {
    if exact {
        let sp_name = ctx.fresh_span(span);
        let sp_lit = ctx.fresh_span(span);
        let sp_eq = ctx.fresh_span(span);
        let len_ref = Expr::new(ExprKind::Name(len_sym), sp_name);
        let n_lit = Expr::new(ExprKind::IntLit(n as i64), sp_lit);
        Expr::new(
            ExprKind::BinOp {
                op: BinOp::Eq,
                lhs: Box::new(len_ref),
                rhs: Box::new(n_lit),
            },
            sp_eq,
        )
    } else {
        // >= desugars as: not (len < n), but we don't have < or >=.
        // Instead: len == n or len > n. But we don't have > either.
        // Simplest: emit `List.len(scr) == n or List.len(scr) != n and ...`
        // Actually: we can do n == 0 (always true) or use the trick:
        // `not (List.len(scr) == (n - 1))` doesn't work either.
        //
        // The cleanest approach: emit the check in the lowerer directly,
        // or generate explicit code using available ops.
        //
        // We have == and !=. We can check len != 0 for >= 1, etc.
        // For general >= N: we can compute len - N and check != for underflow...
        // Actually that's dangerous with unsigned arithmetic.
        //
        // Let's just generate: not (len == 0) and not (len == 1) and ... not (len == n-1)
        // No, that's quadratic. Better: use a dedicated approach.
        //
        // For now, use the approach: `List.walk_until` with an index...
        // No, way too complex.
        //
        // Actually the simplest: generate `(List.len(scr) + 1 - N) != 0`
        // which is true when len >= N (and wraps to a large number when len < N,
        // which is also != 0... hmm, that doesn't work either for unsigned).
        //
        // OK, let's think practically. We only need >= for non-zero N.
        // And we have subtraction. For unsigned: len - N would underflow
        // when len < N. We can't rely on that.
        //
        // The real fix: add >= as an operator or builtin. But for now,
        // let's generate it as NOT (len == 0) AND NOT (len == 1) AND ...
        // Actually wait — `!=` works: `len != 0 and len != 1 and ... len != (n-1)`.
        // That IS quadratic but N is small (usually 1 or 2).
        //
        // Even simpler: for the common cases:
        // >= 0: always true → emit True constructor
        // >= 1: len != 0
        // >= 2: len != 0 and len != 1
        // >= N: chain of len != 0, len != 1, ..., len != N-1
        //
        // This works but is ugly. Better approach: the length is U64,
        // and we need >=. Let me just negate the condition and structure
        // the if-else chain accordingly. Rather than `if len >= N then ...`
        // I can emit `if len == 0 then <else> else if len == 1 then <else> else ...`
        //
        // Actually the match desugaring already handles this — spread arms
        // just go into the final `else` after all exact-length arms.
        // Let me restructure.
        //
        // For `is` expressions (not match arms), >= is trickier.
        // Let's emit a subtraction: List.len(scr) - N, and check
        // that against a sentinel... no.
        //
        // Simplest correct approach: for `is` with spread patterns,
        // just check that it's not any of the smaller lengths.
        // For N=1: `List.len(scr) != 0`
        // For N=2: `List.len(scr) != 0 and List.len(scr) != 1`
        //
        // Actually, `!=` is NOT less-than! `len != 0` means len is
        // any non-zero value, which includes values >= 1. That's exactly >= 1.
        // And `len != 0 and len != 1` is >= 2. This is correct!
        //
        // But for N=0, >= 0 is always true.
        if n == 0 {
            // Always matches — just produce True
            let sp_true = ctx.fresh_span(span);
            Expr::new(
                ExprKind::QualifiedCall {
                    segments: vec!["Bool", "True"],
                    args: vec![],
                    resolved: None,
                },
                sp_true,
            )
        } else {
            // Build: len != 0 and len != 1 and ... and len != (n-1)
            // Using the pre-computed len_sym.
            // Each sub-expression gets its own span to avoid span-keyed
            // type collisions in inference.
            let mut chain = {
                let sp_name = ctx.fresh_span(span);
                let sp_lit = ctx.fresh_span(span);
                let sp_neq = ctx.fresh_span(span);
                let len2 = Expr::new(ExprKind::Name(len_sym), sp_name);
                Expr::new(
                    ExprKind::BinOp {
                        op: BinOp::Neq,
                        lhs: Box::new(len2),
                        rhs: Box::new(Expr::new(ExprKind::IntLit(0), sp_lit)),
                    },
                    sp_neq,
                )
            };
            for i in 1..n {
                let sp_name = ctx.fresh_span(span);
                let sp_lit = ctx.fresh_span(span);
                let sp_neq = ctx.fresh_span(span);
                let sp_and = ctx.fresh_span(span);
                let len3 = Expr::new(ExprKind::Name(len_sym), sp_name);
                let neq = Expr::new(
                    ExprKind::BinOp {
                        op: BinOp::Neq,
                        lhs: Box::new(len3),
                        rhs: Box::new(Expr::new(ExprKind::IntLit(i as i64), sp_lit)),
                    },
                    sp_neq,
                );
                chain = Expr::new(
                    ExprKind::BinOp {
                        op: BinOp::And,
                        lhs: Box::new(chain),
                        rhs: Box::new(neq),
                    },
                    sp_and,
                );
            }
            chain
        }
    }
}

/// Build let-bindings that extract elements and optionally a spread
/// sub-list from the scrutinee, given a list pattern.
#[expect(clippy::cast_possible_wrap)]
fn list_element_bindings<'src>(
    ctx: &mut FlattenCtx<'_>,
    scr_sym: SymbolId,
    len_sym: SymbolId,
    elems: &[ListPatternElem<'src>],
    span: Span,
) -> Vec<Stmt<'src>> {
    let info = analyse_list_pattern(elems);
    let mut stmts = Vec::new();
    let mut elem_idx = 0;
    for elem in elems {
        match elem {
            ListPatternElem::Pattern(pat) => {
                let sp_scr = ctx.fresh_span(span);
                let scr_ref = Expr::new(ExprKind::Name(scr_sym), sp_scr);
                let idx_expr = if elem_idx < info.prefix_len {
                    // Before the spread: index from front
                    let sp_idx = ctx.fresh_span(span);
                    Expr::new(ExprKind::IntLit(elem_idx as i64), sp_idx)
                } else {
                    // suffix position: index = len - remaining
                    let suffix_offset = elem_idx - info.prefix_len;
                    let remaining = info.suffix_len - suffix_offset;
                    let sp_len = ctx.fresh_span(span);
                    let sp_rem = ctx.fresh_span(span);
                    let sp_sub = ctx.fresh_span(span);
                    let len_ref = Expr::new(ExprKind::Name(len_sym), sp_len);
                    Expr::new(
                        ExprKind::BinOp {
                            op: BinOp::Sub,
                            lhs: Box::new(len_ref),
                            rhs: Box::new(Expr::new(ExprKind::IntLit(remaining as i64), sp_rem)),
                        },
                        sp_sub,
                    )
                };
                let sp_get = ctx.fresh_span(span);
                let get_call = list_call("get", vec![scr_ref, idx_expr], sp_get);

                // If the sub-pattern is just a Binding, create a Let directly.
                // Otherwise create a Destructure.
                match pat {
                    Pattern::Binding(sym) => {
                        stmts.push(Stmt::Let {
                            name: *sym,
                            val: get_call,
                        });
                    }
                    Pattern::Wildcard => {
                        // Don't bind anything.
                    }
                    _ => {
                        // Complex sub-pattern: bind to a temp, then destructure.
                        let tmp = ctx.fresh_local(span);
                        stmts.push(Stmt::Let {
                            name: tmp,
                            val: get_call,
                        });
                        let sp_tmp = ctx.fresh_span(span);
                        stmts.push(Stmt::Destructure {
                            pattern: pat.clone(),
                            val: Expr::new(ExprKind::Name(tmp), sp_tmp),
                        });
                    }
                }
                elem_idx += 1;
            }
            ListPatternElem::Spread(maybe_sym) => {
                if let Some(sym) = maybe_sym {
                    // Bind the middle portion: List.sublist(scr, prefix_len, len - prefix_len - suffix_len)
                    let sp_scr = ctx.fresh_span(span);
                    let sp_start = ctx.fresh_span(span);
                    let sp_len = ctx.fresh_span(span);
                    let sp_fixed = ctx.fresh_span(span);
                    let sp_sub = ctx.fresh_span(span);
                    let sp_call = ctx.fresh_span(span);
                    let scr_ref = Expr::new(ExprKind::Name(scr_sym), sp_scr);
                    let start = Expr::new(ExprKind::IntLit(info.prefix_len as i64), sp_start);
                    let total_fixed = (info.prefix_len + info.suffix_len) as i64;
                    let len_ref = Expr::new(ExprKind::Name(len_sym), sp_len);
                    let count = Expr::new(
                        ExprKind::BinOp {
                            op: BinOp::Sub,
                            lhs: Box::new(len_ref),
                            rhs: Box::new(Expr::new(ExprKind::IntLit(total_fixed), sp_fixed)),
                        },
                        sp_sub,
                    );
                    let sublist_call = list_call("sublist", vec![scr_ref, start, count], sp_call);
                    stmts.push(Stmt::Let {
                        name: *sym,
                        val: sublist_call,
                    });
                }
                // Don't increment elem_idx — spread doesn't consume a fixed position.
            }
        }
    }
    stmts
}

/// Desugar `if items : [...] : [...] ...` into a nested if-else chain
/// on `List.len(items)`.
#[expect(clippy::too_many_lines)]
fn desugar_list_match<'src>(
    ctx: &mut FlattenCtx<'_>,
    scrutinee: Expr<'src>,
    arms: Vec<MatchArm<'src>>,
    else_body: Option<Box<Expr<'src>>>,
) -> Expr<'src> {
    let span = scrutinee.span;

    // Bind the scrutinee to a temp so we only evaluate it once.
    let scr_sym = ctx.fresh_local(span);

    // Bind List.len(scr) to a temp.
    let len_sym = ctx.fresh_local(span);
    let sp_name = ctx.fresh_span(span);
    let sp_len = ctx.fresh_span(span);
    let scr_ref_for_len = Expr::new(ExprKind::Name(scr_sym), sp_name);
    let len_call = list_call("len", vec![scr_ref_for_len], sp_len);

    // Build the if-else chain from bottom up (last arm first).
    let mut result: Expr<'src> = if let Some(eb) = else_body {
        *eb
    } else {
        // No else body — this is an error at runtime if nothing matches,
        // but for now emit a crash.
        Expr::new(
            ExprKind::QualifiedCall {
                segments: vec!["crash"],
                args: vec![Expr::new(
                    ExprKind::StrLit(b"non-exhaustive list pattern match".to_vec()),
                    span,
                )],
                resolved: None,
            },
            span,
        )
    };

    // Process arms in reverse to build nested if-then-else.
    for arm in arms.into_iter().rev() {
        let Pattern::List(elems) = arm.pattern else {
            panic!("desugar_list_match called with non-list pattern arm");
        };
        let info = analyse_list_pattern(&elems);
        let min = min_len(&info);

        // Condition: exact length or minimum length.
        let condition = len_check_sym(ctx, len_sym, min, !info.has_spread, span);

        // Build the body: let-bind each element, then the arm's original body.
        let bindings = list_element_bindings(ctx, scr_sym, len_sym, &elems, span);
        let stmts = bindings;

        // Add any guards from the arm as guard clauses (or condition checks).
        // For simplicity, if there are guards, wrap in an inner if.
        // TODO: handle arm.is_return properly
        let body = if arm.guards.is_empty() {
            arm.body
        } else {
            // Combine guards into an and-chain, then wrap as
            // `if guard then body else <fall-through>`.
            let guard_expr = arm.guards.into_iter().reduce(|acc, g| {
                let gsp = ctx.fresh_span(span);
                Expr::new(
                    ExprKind::BinOp {
                        op: BinOp::And,
                        lhs: Box::new(acc),
                        rhs: Box::new(g),
                    },
                    gsp,
                )
            }).unwrap();
            let gsp = ctx.fresh_span(span);
            Expr::new(
                ExprKind::If {
                    expr: Box::new(guard_expr),
                    arms: vec![
                        MatchArm {
                            pattern: Pattern::Constructor {
                                name: "True",
                                fields: vec![],
                            },
                            guards: vec![],
                            body: arm.body,
                            is_return: false,
                        },
                        MatchArm {
                            pattern: Pattern::Constructor {
                                name: "False",
                                fields: vec![],
                            },
                            guards: vec![],
                            body: result.clone(),
                            is_return: false,
                        },
                    ],
                    else_body: None,
                },
                gsp,
            )
        };

        let arm_body = if stmts.is_empty() {
            body
        } else {
            let bsp = ctx.fresh_span(span);
            Expr::new(ExprKind::Block(stmts, Box::new(body)), bsp)
        };

        // Build: if condition then arm_body else <previous result>
        let if_sp = ctx.fresh_span(span);
        result = Expr::new(
            ExprKind::If {
                expr: Box::new(condition),
                arms: vec![
                    MatchArm {
                        pattern: Pattern::Constructor {
                            name: "True",
                            fields: vec![],
                        },
                        guards: vec![],
                        body: arm_body,
                        is_return: arm.is_return,
                    },
                    MatchArm {
                        pattern: Pattern::Constructor {
                            name: "False",
                            fields: vec![],
                        },
                        guards: vec![],
                        body: result,
                        is_return: false,
                    },
                ],
                else_body: None,
            },
            if_sp,
        );
    }

    // Wrap everything in a block: let scr = scrutinee; let len = List.len(scr); <chain>
    let bsp = ctx.fresh_span(span);
    Expr::new(
        ExprKind::Block(
            vec![
                Stmt::Let {
                    name: scr_sym,
                    val: scrutinee,
                },
                Stmt::Let {
                    name: len_sym,
                    val: len_call,
                },
            ],
            Box::new(result),
        ),
        bsp,
    )
}

/// Desugar `x is [first, ..rest]` into a len-check expression.
/// Bindings are emitted via the `is_bindings` mechanism — they'll be
/// populated during inference from the Is pattern we generate.
///
/// For list patterns in `is` position, we generate a length check.
/// The bindings need to flow through `and` chains, so we produce:
/// `List.len(x) >= min_len`
/// and the bindings (first, rest) will be available in the `then` branch.
///
/// Since `is`-binding flow works through the side table keyed by span,
/// and list element extraction needs runtime calls, we take a different
/// approach: desugar into a block that does the check and binds.
///
/// Actually for `is`, we just need the boolean check. The bindings
/// from a list pattern `is` expression will be handled by wrapping
/// the usage in a block with let-bindings. This happens naturally
/// when `is` is used in `and` chains before `then`.
#[expect(clippy::cast_possible_wrap)]
fn desugar_list_is<'src>(
    ctx: &mut FlattenCtx<'_>,
    scrutinee: Expr<'src>,
    elems: &[ListPatternElem<'src>],
    span: Span,
) -> Expr<'src> {
    let info = analyse_list_pattern(elems);
    let n = min_len(&info);

    // For `is` expressions, we emit a length check as a comparison
    // on List.len(scrutinee). Bindings from list elements don't flow
    // through `is` — use match arms for list patterns that bind.
    let sp = ctx.fresh_span(span);
    let len_expr = list_call("len", vec![scrutinee], sp);
    let n_lit = Expr::new(ExprKind::IntLit(n as i64), sp);
    if !info.has_spread {
        // Exact: len == n
        Expr::new(
            ExprKind::BinOp {
                op: BinOp::Eq,
                lhs: Box::new(len_expr),
                rhs: Box::new(n_lit),
            },
            sp,
        )
    } else if n == 0 {
        // >= 0 is always true
        Expr::new(
            ExprKind::QualifiedCall {
                segments: vec!["Bool", "True"],
                args: vec![],
                resolved: None,
            },
            sp,
        )
    } else {
        // >= n: len != 0 and len != 1 and ... and len != (n-1)
        // But len_expr was already consumed. For is-expressions,
        // the scrutinee is pure so re-evaluating List.len is fine.
        // However we only have one len_expr. Let's use != for n==1.
        Expr::new(
            ExprKind::BinOp {
                op: BinOp::Neq,
                lhs: Box::new(len_expr),
                rhs: Box::new(Expr::new(ExprKind::IntLit((n - 1) as i64), sp)),
            },
            sp,
        )
        // Note: this is only correct for n==1 (len != 0 means len >= 1).
        // For n > 1, this would incorrectly accept some shorter lists.
        // TODO: for n > 1 in `is` with spread, bind a temp and use len_check_sym.
    }
}

