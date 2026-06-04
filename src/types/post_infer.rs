//! Post-inference AST rewrites: resolve types, method resolutions, and
//! eta-expand constructor/method references.
//!
//! Runs as a single combined walk over the module after inference
//! completes, replacing three separate tree traversals with one.

use std::collections::HashMap;

use crate::ast::{self, Decl, Expr, ExprId, ExprKind, Module, Span, Stmt};
use crate::symbol::{SymbolId, SymbolKind, SymbolTable};
use crate::types::engine::{Scheme, Type};

/// A callable reference (constructor or method) that inference marked
/// for eta-expansion into an explicit lambda.
pub enum EtaInfo {
    /// Constructor eta-expansion. Carries the constructor's
    /// `SymbolId` so the rewrite can emit `Call { target }`.
    Constructor { con_sym: SymbolId },
    /// Method-reference eta-expansion. Carries the type and
    /// method names so the rewrite can emit the `QualifiedCall`
    /// that the method dispatch pipeline expects.
    Method {
        type_name: String,
        method_name: String,
    },
}

/// Combined post-inference rewrite. In one walk:
/// 1. Copies resolved types from `expr_types` onto `Expr::ty`.
/// 2. Copies method resolutions from `resolutions` onto
///    `MethodCall.resolved` / `QualifiedCall.resolved`.
/// 3. Rewrites constructor/method references marked in `eta` into
///    `ExprKind::Closure { func: __lifted_eta_K, captures: [] }`,
///    synthesizing the `__lifted_eta_K` FuncDef whose body is the
///    underlying constructor/method call. New decls and their
///    schemes are accumulated into `synthesized` for the caller to
///    splice into the module + func_schemes after this walk.
pub fn rewrite(
    module: &mut Module<'_>,
    expr_types: &HashMap<ExprId, Type>,
    resolutions: &HashMap<ExprId, String>,
    eta: &HashMap<ExprId, EtaInfo>,
    symbols: &mut SymbolTable,
    synthesized: &mut Vec<(Decl<'static>, Scheme)>,
) {
    let mut counter: usize = 0;
    for decl in &mut module.decls {
        rewrite_decl(decl, expr_types, resolutions, eta, symbols, synthesized, &mut counter);
    }
}

fn rewrite_decl(
    decl: &mut Decl<'_>,
    expr_types: &HashMap<ExprId, Type>,
    resolutions: &HashMap<ExprId, String>,
    eta: &HashMap<ExprId, EtaInfo>,
    symbols: &mut SymbolTable,
    synthesized: &mut Vec<(Decl<'static>, Scheme)>,
    counter: &mut usize,
) {
    match decl {
        Decl::FuncDef { body, .. } => {
            rewrite_expr(body, expr_types, resolutions, eta, symbols, synthesized, counter);
        }
        Decl::TypeAnno { methods, .. } => {
            for m in methods {
                rewrite_decl(m, expr_types, resolutions, eta, symbols, synthesized, counter);
            }
        }
    }
}

fn rewrite_expr(
    expr: &mut Expr<'_>,
    expr_types: &HashMap<ExprId, Type>,
    resolutions: &HashMap<ExprId, String>,
    eta: &HashMap<ExprId, EtaInfo>,
    symbols: &mut SymbolTable,
    synthesized: &mut Vec<(Decl<'static>, Scheme)>,
    counter: &mut usize,
) {
    // Step 1: write resolved type onto this node.
    if let Some(ty) = expr_types.get(&expr.id) {
        expr.ty = ty.clone();
    }

    // Step 2: write method resolution onto this node (before recursing,
    // so the resolution is in place for eta-expansion checks below).
    match &mut expr.kind {
        ExprKind::QualifiedCall { resolved, .. }
        | ExprKind::MethodCall { resolved, .. } => {
            if let Some(r) = resolutions.get(&expr.id) {
                *resolved = Some(r.clone());
            }
        }
        _ => {}
    }

    // Recurse into children.
    match &mut expr.kind {
        ExprKind::IntLit(_)
        | ExprKind::FloatLit(_)
        | ExprKind::StrLit(_)
        | ExprKind::Name(_) => {}
        ExprKind::BinOp { lhs, rhs, .. } => {
            rewrite_expr(lhs, expr_types, resolutions, eta, symbols, synthesized, counter);
            rewrite_expr(rhs, expr_types, resolutions, eta, symbols, synthesized, counter);
        }
        ExprKind::Call { args, .. } | ExprKind::QualifiedCall { args, .. } => {
            for a in args {
                rewrite_expr(a, expr_types, resolutions, eta, symbols, synthesized, counter);
            }
        }
        ExprKind::Block(stmts, result) => {
            for stmt in stmts {
                rewrite_stmt(stmt, expr_types, resolutions, eta, symbols, synthesized, counter);
            }
            rewrite_expr(result, expr_types, resolutions, eta, symbols, synthesized, counter);
        }
        ExprKind::If {
            expr: scrutinee,
            arms,
            else_body,
        } => {
            rewrite_expr(scrutinee, expr_types, resolutions, eta, symbols, synthesized, counter);
            for arm in arms {
                rewrite_arm(arm, expr_types, resolutions, eta, symbols, synthesized, counter);
            }
            if let Some(eb) = else_body {
                rewrite_expr(eb, expr_types, resolutions, eta, symbols, synthesized, counter);
            }
        }
        ExprKind::Fold {
            expr: scrutinee,
            arms,
        } => {
            rewrite_expr(scrutinee, expr_types, resolutions, eta, symbols, synthesized, counter);
            for arm in arms {
                rewrite_arm(arm, expr_types, resolutions, eta, symbols, synthesized, counter);
            }
        }
        ExprKind::Lambda { .. } => {
            unreachable!("lift_pre_infer removes all Lambda nodes; eta-expansion now emits Closure")
        }
        ExprKind::Record { fields } => {
            for (_, e) in fields {
                rewrite_expr(e, expr_types, resolutions, eta, symbols, synthesized, counter);
            }
        }
        ExprKind::FieldAccess { record, .. } => {
            rewrite_expr(record, expr_types, resolutions, eta, symbols, synthesized, counter);
        }
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems {
                rewrite_expr(e, expr_types, resolutions, eta, symbols, synthesized, counter);
            }
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            rewrite_expr(receiver, expr_types, resolutions, eta, symbols, synthesized, counter);
            for a in args {
                rewrite_expr(a, expr_types, resolutions, eta, symbols, synthesized, counter);
            }
        }
        ExprKind::Is { expr: inner, .. } => {
            rewrite_expr(inner, expr_types, resolutions, eta, symbols, synthesized, counter);
        }
        ExprKind::RecordUpdate { base, updates } => {
            rewrite_expr(base, expr_types, resolutions, eta, symbols, synthesized, counter);
            for (_, e) in updates {
                rewrite_expr(e, expr_types, resolutions, eta, symbols, synthesized, counter);
            }
        }
        ExprKind::Closure { captures, .. } => {
            for c in captures {
                rewrite_expr(c, expr_types, resolutions, eta, symbols, synthesized, counter);
            }
        }
    }

    // Step 3 (post-order): eta-expand marked callable references.
    if let Some(info) = eta.get(&expr.id)
        && matches!(
            &expr.kind,
            ExprKind::Name(_) | ExprKind::FieldAccess { .. }
        )
        && matches!(&expr.ty, Type::Arrow(_, _))
    {
        eta_expand(expr, info, symbols, synthesized, counter);
    }
}

fn rewrite_arm(
    arm: &mut ast::MatchArm<'_>,
    expr_types: &HashMap<ExprId, Type>,
    resolutions: &HashMap<ExprId, String>,
    eta: &HashMap<ExprId, EtaInfo>,
    symbols: &mut SymbolTable,
    synthesized: &mut Vec<(Decl<'static>, Scheme)>,
    counter: &mut usize,
) {
    for g in &mut arm.guards {
        rewrite_expr(g, expr_types, resolutions, eta, symbols, synthesized, counter);
    }
    rewrite_expr(&mut arm.body, expr_types, resolutions, eta, symbols, synthesized, counter);
}

fn rewrite_stmt(
    stmt: &mut Stmt<'_>,
    expr_types: &HashMap<ExprId, Type>,
    resolutions: &HashMap<ExprId, String>,
    eta: &HashMap<ExprId, EtaInfo>,
    symbols: &mut SymbolTable,
    synthesized: &mut Vec<(Decl<'static>, Scheme)>,
    counter: &mut usize,
) {
    match stmt {
        Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => {
            rewrite_expr(val, expr_types, resolutions, eta, symbols, synthesized, counter);
        }
        Stmt::Guard {
            condition,
            return_val,
        } => {
            rewrite_expr(condition, expr_types, resolutions, eta, symbols, synthesized, counter);
            rewrite_expr(return_val, expr_types, resolutions, eta, symbols, synthesized, counter);
        }
        Stmt::TypeHint { .. } => {}
    }
}

// ---- Eta expansion ----

/// Replace a marked callable reference with an `ExprKind::Closure`
/// pointing at a freshly-synthesized `__lifted_eta_K` FuncDef that
/// forwards its arguments to the underlying call.
///
/// The eta'd lambda has no captures (its body only references its
/// own params and the global constructor/method), so the resulting
/// Closure has an empty `captures` vector. The lifted FuncDef and
/// its monomorphic Scheme are pushed to `synthesized` for the
/// caller to splice into the module + func_schemes after the walk.
fn eta_expand(
    expr: &mut Expr<'_>,
    info: &EtaInfo,
    symbols: &mut SymbolTable,
    synthesized: &mut Vec<(Decl<'static>, Scheme)>,
    counter: &mut usize,
) {
    let Type::Arrow(param_types, ret_ty) = expr.ty.clone() else {
        unreachable!("caller checked expr.ty is Arrow");
    };
    let span = expr.span;
    let param_syms: Vec<SymbolId> = (0..param_types.len())
        .map(|i| {
            let name = format!("__eta_{i}");
            symbols.fresh(name, span, SymbolKind::Local)
        })
        .collect();
    let call_args: Vec<Expr<'static>> = param_syms
        .iter()
        .zip(param_types.iter())
        .map(|(sym, ty)| {
            let mut name_expr = Expr::new(ExprKind::Name(*sym), span);
            name_expr.ty = ty.clone();
            name_expr
        })
        .collect();

    let inner_kind = match info {
        EtaInfo::Constructor { con_sym } => ExprKind::Call {
            target: *con_sym,
            args: call_args,
        },
        EtaInfo::Method {
            type_name,
            method_name,
        } => {
            let type_seg: &'static str = Box::leak(type_name.clone().into_boxed_str());
            let method_seg: &'static str = Box::leak(method_name.clone().into_boxed_str());
            let resolved = is_numeric_builtin(type_name, method_name)
                .then(|| format!("__builtin.{method_name}"));
            ExprKind::QualifiedCall {
                segments: vec![type_seg, method_seg],
                args: call_args,
                resolved,
            }
        }
    };
    let mut body_expr = Expr::new(inner_kind, span);
    body_expr.ty = (*ret_ty).clone();

    let id = *counter;
    *counter += 1;
    let lifted_name = format!("__lifted_eta_{id}");
    let lifted_sym = symbols.fresh(&lifted_name, span, SymbolKind::Func);

    let scheme = Scheme::mono(Type::Arrow(param_types, ret_ty));
    let lifted_decl: Decl<'static> = Decl::FuncDef {
        span: synth_span(span),
        name: lifted_sym,
        params: param_syms,
        body: body_expr,
        doc: None,
    };
    synthesized.push((lifted_decl, scheme));

    expr.kind = ExprKind::Closure {
        func: lifted_sym,
        captures: Vec::new(),
    };
}

fn synth_span(s: Span) -> Span {
    s
}

/// True if `type_name.method` is a compiler-intrinsic numeric method.
pub fn is_numeric_builtin(type_name: &str, method: &str) -> bool {
    crate::numeric::NumericType::from_name(type_name)
        .is_some_and(|num| num.has_builtin_method(method))
}
