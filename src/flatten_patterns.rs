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

use crate::ast::{BinOp, Decl, Expr, ExprKind, MatchArm, Module, Pattern, Span, Stmt};
use crate::symbol::{SymbolId, SymbolKind, SymbolTable};

/// Run the pass. Mutates the module in place and returns it.
pub fn flatten<'src>(mut module: Module<'src>, symbols: &mut SymbolTable) -> Module<'src> {
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
        ExprKind::Is { .. } => {
            flatten_is_expr(ctx, expr);
        }
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
        Pattern::Binding(_) | Pattern::Wildcard => {}

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
        Pattern::Binding(_) | Pattern::Wildcard => true,
        Pattern::Constructor { fields, .. } => fields.iter().all(is_pattern_flattenable),
        Pattern::Tuple(_) | Pattern::Record { .. } => false,
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

