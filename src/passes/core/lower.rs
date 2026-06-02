//! AST → Core lowering.
//!
//! Translates the post-mono, post-lambda-lift, post-pattern-flattened
//! AST into the Core IR. The full mapping table:
//!
//! | AST | Core |
//! |---|---|
//! | `IntLit/FloatLit/StrLit` | `Lit` |
//! | `Name` | `Var` (locals) or `App` with 0 args (top-level value refs) |
//! | `Call`, `QualifiedCall`, `MethodCall` | `App` |
//! | `BinOp` | `App` to a builtin (binops are functions in Core) |
//! | `Block(stmts, last)` | nested `Let`s ending in `last` |
//! | `If` | `Match` with bool patterns |
//! | `Fold` | `Cata` |
//! | `Record` | `Record` |
//! | `RecordUpdate` | sequence of `Let` + `Record` with updated fields |
//! | `FieldAccess` | `App` to a field projector |
//! | `Tuple` | `Record` with positional field names |
//! | `ListLit` | nested `Con(Cons, ...)` ending in `Con(Nil)` |
//! | `Is` | `Match` |
//! | `Lambda`, `Closure` | should not appear (eliminated by lambda passes) |
//!
//! ## Status
//!
//! Minimal slice: `IntLit`, `FloatLit`, `StrLit`, `Name`, `Block` with
//! `Let`-only statements. Other variants return `Err` until we need
//! them — keeps the slice small enough to round-trip end-to-end and
//! flush out the supporting-context shape before we go wide.

use crate::ast::{Expr as AstExpr, ExprKind, MatchArm as AstMatchArm, Pattern as AstPattern, Stmt};
use crate::symbol::{FieldInterner, SymbolTable};

use super::expr::{Expr, Literal, MatchArm, Pattern};

/// Context for AST→Core lowering — references the supporting tables
/// that the translation needs.
///
/// - `fields`: resolves `FieldSym` → string for `Record` fields.
/// - `symbols`: resolves `SymbolId` → mangled display name for `Call`
///   targets, so the resulting Core::App uniformly carries a `String`
///   target (same shape as resolved `MethodCall` / `QualifiedCall`).
pub struct LowerCtx<'a> {
    pub fields: &'a FieldInterner,
    pub symbols: &'a SymbolTable,
}

/// Lower a single AST expression into Core. Convenience for tests
/// that don't touch records or named-call targets — uses empty
/// supporting tables, so `Call`, `Record`, etc. will surface
/// "unbound symbol" errors instead of working.
pub fn lower_expr(ast: &AstExpr<'_>) -> Result<Expr, String> {
    static EMPTY_FIELDS: std::sync::OnceLock<FieldInterner> = std::sync::OnceLock::new();
    static EMPTY_SYMBOLS: std::sync::OnceLock<SymbolTable> = std::sync::OnceLock::new();
    let ctx = LowerCtx {
        fields: EMPTY_FIELDS.get_or_init(FieldInterner::new),
        symbols: EMPTY_SYMBOLS.get_or_init(SymbolTable::new),
    };
    lower_expr_with(&ctx, ast)
}

/// Lower with an explicit context. Use this when the program touches
/// records — without the `FieldInterner`, field names can't be
/// resolved.
pub fn lower_expr_with(ctx: &LowerCtx<'_>, ast: &AstExpr<'_>) -> Result<Expr, String> {
    match &ast.kind {
        ExprKind::IntLit(n) => Ok(Expr::Lit {
            value: Literal::Int(*n),
            ty: ast.ty.clone(),
        }),

        ExprKind::FloatLit(f) => Ok(Expr::Lit {
            value: Literal::Float(*f),
            ty: ast.ty.clone(),
        }),

        ExprKind::StrLit(bytes) => Ok(Expr::Lit {
            value: Literal::Str(bytes.clone()),
            ty: ast.ty.clone(),
        }),

        ExprKind::Name(sym) => Ok(Expr::Var {
            sym: *sym,
            ty: ast.ty.clone(),
        }),

        ExprKind::Block(stmts, last) => lower_block(ctx, stmts, last),

        ExprKind::BinOp { op, lhs, rhs } => Ok(Expr::BinOp {
            op: *op,
            lhs: Box::new(lower_expr_with(ctx, lhs)?),
            rhs: Box::new(lower_expr_with(ctx, rhs)?),
            ty: ast.ty.clone(),
        }),

        ExprKind::Call { target, args } => {
            let arg_exprs: Vec<Expr> = args
                .iter()
                .map(|a| lower_expr_with(ctx, a))
                .collect::<Result<_, _>>()?;
            Ok(Expr::App {
                target: ctx.symbols.display(*target).to_owned(),
                args: arg_exprs,
                ty: ast.ty.clone(),
            })
        }

        ExprKind::QualifiedCall { resolved, args, .. } => {
            let name = resolved
                .as_ref()
                .ok_or_else(|| "core::lower_expr: QualifiedCall unresolved".to_string())?;
            let arg_exprs: Vec<Expr> = args
                .iter()
                .map(|a| lower_expr_with(ctx, a))
                .collect::<Result<_, _>>()?;
            Ok(Expr::App {
                target: name.clone(),
                args: arg_exprs,
                ty: ast.ty.clone(),
            })
        }

        ExprKind::MethodCall { receiver, args, resolved, .. } => {
            let name = resolved
                .as_ref()
                .ok_or_else(|| "core::lower_expr: MethodCall unresolved".to_string())?;
            // Method calls pass the receiver as the first argument
            // to the dispatched function, then the rest. This matches
            // the existing AST→SSA convention.
            let mut arg_exprs: Vec<Expr> = Vec::with_capacity(args.len() + 1);
            arg_exprs.push(lower_expr_with(ctx, receiver)?);
            for a in args {
                arg_exprs.push(lower_expr_with(ctx, a)?);
            }
            Ok(Expr::App {
                target: name.clone(),
                args: arg_exprs,
                ty: ast.ty.clone(),
            })
        }

        ExprKind::Tuple(_) | ExprKind::Record { .. } => {
            // Aggregates are SROA'd at AST→Core into slot lists, not
            // represented as Core IR nodes. The slot-decomposition
            // path goes through `lower_expr_slots` (not yet wired in
            // through `lower_expr`). For now, programs that hit a
            // Tuple/Record at expression position via this entry are
            // unsupported.
            Err(format!(
                "core::lower_expr: {} requires slot-decomposition path \
                 (lower_expr_slots) — not yet wired",
                ast_kind_name(&ast.kind)
            ))
        }

        ExprKind::If { expr, arms, else_body } => {
            // `If` is sugar for `Match` — the AST already represents
            // it that way (scrutinee + arms). The optional `else_body`
            // becomes a Wildcard arm at the end.
            let scrutinee = lower_expr_with(ctx, expr)?;
            let mut core_arms: Vec<MatchArm> = arms
                .iter()
                .map(|a| lower_match_arm(ctx, a))
                .collect::<Result<_, _>>()?;
            if let Some(else_expr) = else_body {
                let body = lower_expr_with(ctx, else_expr)?;
                core_arms.push(MatchArm { pattern: Pattern::Wildcard, body });
            }
            Ok(Expr::Match {
                scrutinee: Box::new(scrutinee),
                arms: core_arms,
                ty: ast.ty.clone(),
            })
        }

        // Everything else: not yet implemented. We surface the
        // discriminant name so debugging tells us exactly which
        // variant to add next.
        other => Err(format!("core::lower_expr: unsupported ExprKind: {}", ast_kind_name(other))),
    }
}

/// Lower a block to a chain of `Let`s. `(let x = e1; let y = e2; ...; body)`
/// becomes `Let(x, e1, Let(y, e2, ..., body))`. Non-`Let` statements
/// (`Destructure`, `Guard`, `TypeHint`) error out for now — they need
/// dedicated treatment when we grow the slice.
fn lower_block(ctx: &LowerCtx<'_>, stmts: &[Stmt<'_>], last: &AstExpr<'_>) -> Result<Expr, String> {
    let body_ty = last.ty.clone();
    let mut result = lower_expr_with(ctx, last)?;
    // Fold from right to left: the innermost `Let` wraps the body;
    // each outer `Stmt::Let` wraps the partial result.
    for stmt in stmts.iter().rev() {
        match stmt {
            Stmt::Let { name, val } => {
                let value = lower_expr_with(ctx, val)?;
                result = Expr::Let {
                    binder: *name,
                    value: Box::new(value),
                    body: Box::new(result),
                    ty: body_ty.clone(),
                };
            }
            Stmt::TypeHint { .. } => {
                // Type hints are pre-inference annotations and
                // carry no Core meaning — inference has already
                // applied them.
            }
            Stmt::Destructure { .. } => {
                return Err("core::lower_block: Stmt::Destructure not yet supported".into());
            }
            Stmt::Guard { .. } => {
                return Err("core::lower_block: Stmt::Guard not yet supported".into());
            }
        }
    }
    Ok(result)
}

/// Lower a single match arm. Pre-flatten patterns have nested shapes;
/// post-flatten they're shallow — `Constructor`, `IntLit`, `StrLit`,
/// `Wildcard`, or `Binding`. Guards (`and cond`) aren't yet handled
/// at the Core layer — we error out on them so the caller knows.
fn lower_match_arm(ctx: &LowerCtx<'_>, arm: &AstMatchArm<'_>) -> Result<MatchArm, String> {
    if !arm.guards.is_empty() {
        return Err("core::lower_match_arm: guarded arms not yet supported".into());
    }
    if arm.is_return {
        return Err("core::lower_match_arm: return arms not yet supported".into());
    }
    let pattern = lower_pattern(&arm.pattern)?;
    let body = lower_expr_with(ctx, &arm.body)?;
    Ok(MatchArm { pattern, body })
}

fn lower_pattern(pat: &AstPattern<'_>) -> Result<Pattern, String> {
    match pat {
        AstPattern::Constructor { name, fields } => {
            // Post-flatten, every field is either a Binding or a
            // Wildcard. Convert to a flat list of binder symbols —
            // wildcards become a placeholder; the lowering's
            // codegen-side knows to skip them by checking against
            // a sentinel SymbolId. For now, only accept Binding
            // and Wildcard fields and error on richer shapes.
            let mut binders = Vec::with_capacity(fields.len());
            for f in fields {
                match f {
                    AstPattern::Binding(sym) => binders.push(*sym),
                    AstPattern::Wildcard => {
                        // Use SymbolId(u32::MAX) as a sentinel
                        // "unbound" marker. The Core→SSA pass
                        // recognizes this and doesn't bind it.
                        binders.push(crate::symbol::SymbolId(u32::MAX));
                    }
                    other => {
                        return Err(format!(
                            "core::lower_pattern: nested pattern field not supported \
                             (post-flatten should have left only Binding/Wildcard, \
                             saw {other:?})"
                        ));
                    }
                }
            }
            Ok(Pattern::Constructor {
                tag: (*name).to_owned(),
                binders,
            })
        }
        AstPattern::IntLit(n) => Ok(Pattern::IntLit(*n)),
        AstPattern::StrLit(bytes) => Ok(Pattern::StrLit(bytes.clone())),
        AstPattern::Wildcard => Ok(Pattern::Wildcard),
        AstPattern::Binding(sym) => Ok(Pattern::Binding(*sym)),
        AstPattern::Record { .. } | AstPattern::List(_) | AstPattern::Tuple(_) => {
            Err(format!(
                "core::lower_pattern: nested pattern shape not supported \
                 (post-flatten should have eliminated these): {pat:?}"
            ))
        }
    }
}

/// Short name for an `ExprKind` discriminant — used only in error
/// messages so a caller hitting an unimplemented variant sees which
/// one without us deriving Debug-via-display elsewhere.
fn ast_kind_name(kind: &ExprKind<'_>) -> &'static str {
    match kind {
        ExprKind::IntLit(_) => "IntLit",
        ExprKind::FloatLit(_) => "FloatLit",
        ExprKind::StrLit(_) => "StrLit",
        ExprKind::Name(_) => "Name",
        ExprKind::BinOp { .. } => "BinOp",
        ExprKind::Call { .. } => "Call",
        ExprKind::Block(..) => "Block",
        ExprKind::If { .. } => "If",
        ExprKind::Fold { .. } => "Fold",
        ExprKind::Lambda { .. } => "Lambda",
        ExprKind::QualifiedCall { .. } => "QualifiedCall",
        ExprKind::Record { .. } => "Record",
        ExprKind::RecordUpdate { .. } => "RecordUpdate",
        ExprKind::FieldAccess { .. } => "FieldAccess",
        ExprKind::Tuple(_) => "Tuple",
        ExprKind::ListLit(_) => "ListLit",
        ExprKind::MethodCall { .. } => "MethodCall",
        ExprKind::Is { .. } => "Is",
        ExprKind::Closure { .. } => "Closure",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{ExprKind, Span};
    use crate::source::FileId;
    use crate::symbol::SymbolId;
    use crate::types::engine::Type;

    fn dummy_span() -> Span {
        Span { file: FileId(0), start: 0, end: 0 }
    }

    fn i64_ty() -> Type {
        Type::Con("I64".to_string())
    }

    fn is_i64(ty: &Type) -> bool {
        matches!(ty, Type::Con(c) if c == "I64")
    }

    #[test]
    fn lowers_int_literal() {
        let ast = AstExpr::typed(ExprKind::IntLit(42), dummy_span(), i64_ty());
        let core = lower_expr(&ast).unwrap();
        match core {
            Expr::Lit { value: Literal::Int(n), ty } => {
                assert_eq!(n, 42);
                assert!(is_i64(&ty));
            }
            other => panic!("expected Lit::Int, got {other:?}"),
        }
    }

    #[test]
    fn lowers_name_to_var() {
        let sym = SymbolId(7);
        let ast = AstExpr::typed(ExprKind::Name(sym), dummy_span(), i64_ty());
        let core = lower_expr(&ast).unwrap();
        match core {
            Expr::Var { sym: got, ty } => {
                assert_eq!(got, sym);
                assert!(is_i64(&ty));
            }
            other => panic!("expected Var, got {other:?}"),
        }
    }

    #[test]
    fn lowers_block_to_let_chain() {
        // AST equivalent of:
        //   let x = 1
        //   let y = 2
        //   y
        let x = SymbolId(1);
        let y = SymbolId(2);
        let one = AstExpr::typed(ExprKind::IntLit(1), dummy_span(), i64_ty());
        let two = AstExpr::typed(ExprKind::IntLit(2), dummy_span(), i64_ty());
        let y_ref = AstExpr::typed(ExprKind::Name(y), dummy_span(), i64_ty());
        let block = AstExpr::typed(
            ExprKind::Block(
                vec![
                    Stmt::Let { name: x, val: one },
                    Stmt::Let { name: y, val: two },
                ],
                Box::new(y_ref),
            ),
            dummy_span(),
            i64_ty(),
        );

        let core = lower_expr(&block).unwrap();
        // Outermost should be Let(x, _, Let(y, _, Var(y))).
        let Expr::Let { binder: outer, body: outer_body, .. } = core else {
            panic!("expected outer Let");
        };
        assert_eq!(outer, x);
        let Expr::Let { binder: inner, body: inner_body, .. } = *outer_body else {
            panic!("expected inner Let");
        };
        assert_eq!(inner, y);
        let Expr::Var { sym: got, .. } = *inner_body else {
            panic!("expected inner Var");
        };
        assert_eq!(got, y);
    }

    #[test]
    fn lowers_binop() {
        use crate::ast::BinOp;
        let lhs = AstExpr::typed(ExprKind::IntLit(1), dummy_span(), i64_ty());
        let rhs = AstExpr::typed(ExprKind::IntLit(2), dummy_span(), i64_ty());
        let add = AstExpr::typed(
            ExprKind::BinOp { op: BinOp::Add, lhs: Box::new(lhs), rhs: Box::new(rhs) },
            dummy_span(),
            i64_ty(),
        );
        let core = lower_expr(&add).unwrap();
        let Expr::BinOp { op, lhs, rhs, .. } = core else {
            panic!("expected BinOp, got {core:?}");
        };
        assert_eq!(op, BinOp::Add);
        assert!(matches!(*lhs, Expr::Lit { value: Literal::Int(1), .. }));
        assert!(matches!(*rhs, Expr::Lit { value: Literal::Int(2), .. }));
    }

    #[test]
    fn lowers_if_to_match_with_constructor_arm() {
        // Construct the AST for:
        //   if x : True then 1 : False then 2
        // post-flatten this becomes a Match on a Bool with two
        // constructor arms.
        let x_sym = SymbolId(1);
        let scrutinee = AstExpr::typed(
            ExprKind::Name(x_sym),
            dummy_span(),
            Type::Con("Bool".to_string()),
        );
        let arm_true = crate::ast::MatchArm {
            pattern: AstPattern::Constructor { name: "True", fields: vec![] },
            guards: vec![],
            body: AstExpr::typed(ExprKind::IntLit(1), dummy_span(), i64_ty()),
            is_return: false,
        };
        let arm_false = crate::ast::MatchArm {
            pattern: AstPattern::Constructor { name: "False", fields: vec![] },
            guards: vec![],
            body: AstExpr::typed(ExprKind::IntLit(2), dummy_span(), i64_ty()),
            is_return: false,
        };
        let if_ast = AstExpr::typed(
            ExprKind::If {
                expr: Box::new(scrutinee),
                arms: vec![arm_true, arm_false],
                else_body: None,
            },
            dummy_span(),
            i64_ty(),
        );

        let core = lower_expr(&if_ast).unwrap();
        let Expr::Match { arms, .. } = core else {
            panic!("expected Match");
        };
        assert_eq!(arms.len(), 2);
        match &arms[0].pattern {
            Pattern::Constructor { tag, binders } => {
                assert_eq!(tag, "True");
                assert!(binders.is_empty());
            }
            other => panic!("expected Constructor pattern, got {other:?}"),
        }
        match &arms[1].pattern {
            Pattern::Constructor { tag, binders } => {
                assert_eq!(tag, "False");
                assert!(binders.is_empty());
            }
            other => panic!("expected Constructor pattern, got {other:?}"),
        }
    }

    #[test]
    fn unsupported_returns_err_with_variant_name() {
        let ast = AstExpr::typed(
            ExprKind::Lambda { params: vec![], body: Box::new(
                AstExpr::typed(ExprKind::IntLit(0), dummy_span(), i64_ty())
            )},
            dummy_span(),
            i64_ty(),
        );
        let err = lower_expr(&ast).unwrap_err();
        assert!(err.contains("Lambda"), "error should name the variant: {err}");
    }
}
