//! Post-inference AST type validator focused on **Call argument
//! positions**. Catches a specific bug class: a synthesizer (in
//! `lambda_lift`, `lambda_specialize`, or `lambda_narrow`)
//! constructing a `Name`-shaped Expr as a Call arg via `Expr::new`
//! (which defaults `.ty` to `Type::Var(0)`) instead of
//! `Expr::typed`.
//!
//! Why call args specifically: `lower::lower_user_call` runs
//! `to_slots` on each arg, using the arg's `.ty` to compute slot
//! offsets and counts. A placeholder type makes `slot_offsets`
//! return `vec![0]` (one slot, default) and `to_slots` falls into
//! the `Single→Single` passthrough — so a multi-slot capture (a
//! List, a tuple) flows as one Ptr instead of N slots, and the
//! Call arrives at the SSA boundary with the wrong arity. Runtime
//! panic.
//!
//! Three commits this session were exactly this shape:
//! `lambda_specialize`'s singleton rewriter, `lambda_narrow`'s clone
//! body, and `lambda_specialize`'s `__apply_K` body. The validator
//! locks down the bug class so any regression fails immediately
//! rather than producing a runtime crash on programs that exercise
//! multi-slot captures.
//!
//! Other placeholder-typed `Expr` positions (an `If` scrutinee, a
//! `Block` result wrapper, etc.) are tolerated by lower today and
//! intentionally not flagged — that would generate false positives
//! against synthesizers whose code lower compensates for elsewhere.

use crate::ast::{Decl, Expr, ExprKind, MatchArm, Module, Pattern, Stmt};
use crate::symbol::SymbolTable;
use crate::types::engine::{Type, TypeVar};

/// Collect every placeholder-typed synthesized Name in a Call arg
/// position. Returns a list of human-readable error strings; empty
/// list means no violations.
pub fn validate(module: &Module<'_>, symbols: &SymbolTable) -> Vec<String> {
    let mut errors = Vec::new();
    for decl in &module.decls {
        match decl {
            Decl::FuncDef { name, body, .. } => {
                let context = format!("fn {}", symbols.display(*name));
                walk(body, &context, symbols, &mut errors);
            }
            Decl::TypeAnno { name: ty_name, methods, .. } => {
                let ty_display = symbols.display(*ty_name).to_owned();
                for m in methods {
                    if let Decl::FuncDef { name, body, .. } = m {
                        let context =
                            format!("{}.{}", ty_display, symbols.display(*name));
                        walk(body, &context, symbols, &mut errors);
                    }
                }
            }
        }
    }
    errors
}

fn is_placeholder(ty: &Type) -> bool {
    matches!(ty, Type::Var(TypeVar(0)))
}

fn walk(expr: &Expr<'_>, context: &str, symbols: &SymbolTable, errors: &mut Vec<String>) {
    // Flag Call arg positions where the arg is a Name with
    // placeholder type — the bug class this validator exists for.
    // See module-level docs.
    match &expr.kind {
        ExprKind::Call { args, .. }
        | ExprKind::QualifiedCall { args, .. } => {
            for arg in args {
                check_call_arg(arg, context, symbols, errors);
            }
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            check_call_arg(receiver, context, symbols, errors);
            for arg in args {
                check_call_arg(arg, context, symbols, errors);
            }
        }
        _ => {}
    }
    recurse(expr, context, symbols, errors);
}

fn check_call_arg(
    arg: &Expr<'_>,
    context: &str,
    symbols: &SymbolTable,
    errors: &mut Vec<String>,
) {
    // Only flag Names that reference SYNTHESIZED symbols — those
    // whose def span is the `synth_span()` sentinel (usize::MAX
    // start/end). User-code Names with placeholder types are a
    // different concern (inference gaps) and would generate false
    // positives. We use the *symbol*'s def span rather than the
    // *expr*'s span because synthesizers typically copy the
    // surrounding user-code span onto their Name exprs.
    if let ExprKind::Name(sym) = &arg.kind {
        if is_placeholder(&arg.ty) && is_synth_symbol(*sym, symbols) {
            errors.push(format!(
                "{context}: synthesized Call arg Name({}) has \
                 placeholder Type::Var(0) at expr {:?} — use \
                 Expr::typed with the actual binding type so lower's \
                 to_slots can expand multi-slot values",
                symbols.display(*sym),
                arg.span,
            ));
        }
    }
}

fn is_synth_symbol(sym: crate::symbol::SymbolId, symbols: &SymbolTable) -> bool {
    let span = symbols.get(sym).span;
    span.start == usize::MAX && span.end == usize::MAX
}

fn recurse(expr: &Expr<'_>, context: &str, symbols: &SymbolTable, errors: &mut Vec<String>) {
    match &expr.kind {
        ExprKind::IntLit(_)
        | ExprKind::FloatLit(_)
        | ExprKind::StrLit(_)
        | ExprKind::Name(_) => {}
        ExprKind::BinOp { lhs, rhs, .. } => {
            walk(lhs, context, symbols, errors);
            walk(rhs, context, symbols, errors);
        }
        ExprKind::Call { args, .. } => {
            for a in args {
                walk(a, context, symbols, errors);
            }
        }
        ExprKind::Block(stmts, result) => {
            for s in stmts {
                walk_stmt(s, context, symbols, errors);
            }
            walk(result, context, symbols, errors);
        }
        ExprKind::If {
            expr: s,
            arms,
            else_body,
        } => {
            walk(s, context, symbols, errors);
            for arm in arms {
                walk_arm(arm, context, symbols, errors);
            }
            if let Some(eb) = else_body {
                walk(eb, context, symbols, errors);
            }
        }
        ExprKind::Fold { expr: s, arms } => {
            walk(s, context, symbols, errors);
            for arm in arms {
                walk_arm(arm, context, symbols, errors);
            }
        }
        ExprKind::Lambda { body, .. } => walk(body, context, symbols, errors),
        ExprKind::QualifiedCall { args, .. } => {
            for a in args {
                walk(a, context, symbols, errors);
            }
        }
        ExprKind::Record { fields } => {
            for (_, e) in fields {
                walk(e, context, symbols, errors);
            }
        }
        ExprKind::RecordUpdate { base, updates } => {
            walk(base, context, symbols, errors);
            for (_, e) in updates {
                walk(e, context, symbols, errors);
            }
        }
        ExprKind::FieldAccess { record, .. } => walk(record, context, symbols, errors),
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems {
                walk(e, context, symbols, errors);
            }
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            walk(receiver, context, symbols, errors);
            for a in args {
                walk(a, context, symbols, errors);
            }
        }
        ExprKind::Is { expr: inner, pattern } => {
            walk(inner, context, symbols, errors);
            walk_pattern(pattern, context, errors);
        }
        ExprKind::Closure { captures, .. } => {
            for c in captures {
                walk(c, context, symbols, errors);
            }
        }
    }
}

fn walk_stmt(stmt: &Stmt<'_>, context: &str, symbols: &SymbolTable, errors: &mut Vec<String>) {
    match stmt {
        Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => walk(val, context, symbols, errors),
        Stmt::Guard {
            condition,
            return_val,
        } => {
            walk(condition, context, symbols, errors);
            walk(return_val, context, symbols, errors);
        }
        Stmt::TypeHint { .. } => {}
    }
}

fn walk_arm(arm: &MatchArm<'_>, context: &str, symbols: &SymbolTable, errors: &mut Vec<String>) {
    walk_pattern(&arm.pattern, context, errors);
    for g in &arm.guards {
        walk(g, context, symbols, errors);
    }
    walk(&arm.body, context, symbols, errors);
}

fn walk_pattern(_pat: &Pattern<'_>, _context: &str, _errors: &mut Vec<String>) {
    // Patterns don't carry types directly — bindings are typed at use
    // sites via `Name` lookup, which this walker already covers.
}
