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

use crate::ast::{Expr as AstExpr, ExprKind, Stmt};

use super::expr::{Expr, Literal};

/// Lower a single AST expression into Core. Returns `Err(reason)` for
/// AST shapes we haven't implemented yet — the caller decides whether
/// to skip the function, fall back to the existing AST→SSA pipeline,
/// or fail.
pub fn lower_expr(ast: &AstExpr<'_>) -> Result<Expr, String> {
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

        ExprKind::Block(stmts, last) => lower_block(stmts, last),

        ExprKind::BinOp { op, lhs, rhs } => Ok(Expr::BinOp {
            op: *op,
            lhs: Box::new(lower_expr(lhs)?),
            rhs: Box::new(lower_expr(rhs)?),
            ty: ast.ty.clone(),
        }),

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
fn lower_block(stmts: &[Stmt<'_>], last: &AstExpr<'_>) -> Result<Expr, String> {
    let body_ty = last.ty.clone();
    let mut result = lower_expr(last)?;
    // Fold from right to left: the innermost `Let` wraps the body;
    // each outer `Stmt::Let` wraps the partial result.
    for stmt in stmts.iter().rev() {
        match stmt {
            Stmt::Let { name, val } => {
                let value = lower_expr(val)?;
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
