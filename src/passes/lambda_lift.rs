#![allow(
    clippy::too_many_lines,
    clippy::doc_markdown,
    clippy::needless_pass_by_value,
    reason = "lambda lift is an AST walker"
)]

//! Lambda lifting — convert every `Lambda` into a top-level `FuncDef`
//! with captures as extra leading parameters, replacing the Lambda node
//! with a `Closure { func, captures }` value.
//!
//! After this pass, no `ExprKind::Lambda` nodes survive in the module.
//! Every former lambda is a named `FuncDef` with signature
//! `(cap0, cap1, ..., param0, param1, ...) -> ret`.

use std::collections::HashSet;

use crate::ast::{self, Decl, Expr, ExprKind, Module, Span, Stmt};
use crate::symbol::{SymbolId, SymbolKind, SymbolTable};

/// Lift all lambdas in the module to top-level FuncDefs.
pub fn lift<'src>(module: Module<'src>, symbols: &mut SymbolTable) -> Module<'src> {
    let mut ctx = LiftCtx {
        symbols,
        lifted: Vec::new(),
        counter: 0,
    };

    // Process each decl. Lifted functions created during a decl's
    // processing are prepended before it so they appear earlier in
    // topo order — inner lambdas before outer, all before the
    // function whose body references their Closure nodes.
    let mut new_decls: Vec<Decl<'src>> = Vec::new();
    for d in module.decls {
        let before = ctx.lifted.len();
        let d = ctx.lift_decl(d);
        new_decls.extend(ctx.lifted.drain(before..));
        new_decls.push(d);
    }

    Module {
        exports: module.exports,
        imports: module.imports,
        decls: new_decls,
    }
}

struct LiftCtx<'a, 'src> {
    symbols: &'a mut SymbolTable,
    lifted: Vec<Decl<'src>>,
    counter: usize,
}

impl<'src> LiftCtx<'_, 'src> {
    fn fresh_name(&mut self, span: Span) -> SymbolId {
        let name = format!("__lifted_{}", self.counter);
        self.counter += 1;
        self.symbols.fresh(name, span, SymbolKind::Func)
    }

    fn lift_decl(&mut self, decl: Decl<'src>) -> Decl<'src> {
        match decl {
            Decl::FuncDef {
                span,
                name,
                params,
                body,
                doc,
            } => {
                let body = self.lift_expr(body);
                Decl::FuncDef {
                    span,
                    name,
                    params,
                    body,
                    doc,
                }
            }
            Decl::TypeAnno {
                span,
                name,
                type_params,
                ty,
                where_clause,
                methods,
                kind,
                doc,
            } => {
                let methods = methods.into_iter().map(|m| self.lift_decl(m)).collect();
                Decl::TypeAnno {
                    span,
                    name,
                    type_params,
                    ty,
                    where_clause,
                    methods,
                    kind,
                    doc,
                }
            }
        }
    }

    /// Walk an expression bottom-up, lifting lambdas to top-level.
    fn lift_expr(&mut self, mut expr: Expr<'src>) -> Expr<'src> {
        // First recurse into children so nested lambdas are lifted
        // before their parents.
        expr.kind = match expr.kind {
            ExprKind::Lambda { params, body } => {
                let body = self.lift_expr(*body);
                return self.lift_lambda(params, body, expr.span, expr.ty);
            }
            ExprKind::BinOp { op, lhs, rhs } => ExprKind::BinOp {
                op,
                lhs: Box::new(self.lift_expr(*lhs)),
                rhs: Box::new(self.lift_expr(*rhs)),
            },
            ExprKind::Call { target, args } => ExprKind::Call {
                target,
                args: args.into_iter().map(|a| self.lift_expr(a)).collect(),
            },
            ExprKind::QualifiedCall {
                segments,
                args,
                resolved,
            } => ExprKind::QualifiedCall {
                segments,
                args: args.into_iter().map(|a| self.lift_expr(a)).collect(),
                resolved,
            },
            ExprKind::Block(stmts, result) => {
                let stmts = stmts.into_iter().map(|s| self.lift_stmt(s)).collect();
                ExprKind::Block(stmts, Box::new(self.lift_expr(*result)))
            }
            ExprKind::If {
                expr: scrutinee,
                arms,
                else_body,
            } => ExprKind::If {
                expr: Box::new(self.lift_expr(*scrutinee)),
                arms: arms.into_iter().map(|a| self.lift_arm(a)).collect(),
                else_body: else_body.map(|e| Box::new(self.lift_expr(*e))),
            },
            ExprKind::Fold {
                expr: scrutinee,
                arms,
            } => ExprKind::Fold {
                expr: Box::new(self.lift_expr(*scrutinee)),
                arms: arms.into_iter().map(|a| self.lift_arm(a)).collect(),
            },
            ExprKind::Record { fields } => ExprKind::Record {
                fields: fields
                    .into_iter()
                    .map(|(f, e)| (f, self.lift_expr(e)))
                    .collect(),
            },
            ExprKind::RecordUpdate { base, updates } => ExprKind::RecordUpdate {
                base: Box::new(self.lift_expr(*base)),
                updates: updates
                    .into_iter()
                    .map(|(f, e)| (f, self.lift_expr(e)))
                    .collect(),
            },
            ExprKind::FieldAccess { record, field } => ExprKind::FieldAccess {
                record: Box::new(self.lift_expr(*record)),
                field,
            },
            ExprKind::Tuple(elems) => {
                ExprKind::Tuple(elems.into_iter().map(|e| self.lift_expr(e)).collect())
            }
            ExprKind::ListLit(elems) => {
                ExprKind::ListLit(elems.into_iter().map(|e| self.lift_expr(e)).collect())
            }
            ExprKind::MethodCall {
                receiver,
                method,
                args,
                resolved,
            } => ExprKind::MethodCall {
                receiver: Box::new(self.lift_expr(*receiver)),
                method,
                args: args.into_iter().map(|a| self.lift_expr(a)).collect(),
                resolved,
            },
            ExprKind::Is { expr: inner, pattern } => ExprKind::Is {
                expr: Box::new(self.lift_expr(*inner)),
                pattern,
            },
            ExprKind::Closure { func, captures } => ExprKind::Closure {
                func,
                captures: captures.into_iter().map(|c| self.lift_expr(c)).collect(),
            },
            // Leaves — no children to recurse into.
            kind @ (ExprKind::IntLit(_)
            | ExprKind::FloatLit(_)
            | ExprKind::StrLit(_)
            | ExprKind::Name(_)) => kind,
        };
        expr
    }

    fn lift_stmt(&mut self, stmt: Stmt<'src>) -> Stmt<'src> {
        match stmt {
            Stmt::Let { name, val } => Stmt::Let {
                name,
                val: self.lift_expr(val),
            },
            Stmt::Destructure { pattern, val } => Stmt::Destructure {
                pattern,
                val: self.lift_expr(val),
            },
            Stmt::Guard {
                condition,
                return_val,
            } => Stmt::Guard {
                condition: self.lift_expr(condition),
                return_val: self.lift_expr(return_val),
            },
            Stmt::TypeHint { .. } => stmt,
        }
    }

    fn lift_arm(&mut self, arm: ast::MatchArm<'src>) -> ast::MatchArm<'src> {
        ast::MatchArm {
            pattern: arm.pattern,
            guards: arm.guards.into_iter().map(|g| self.lift_expr(g)).collect(),
            body: self.lift_expr(arm.body),
            is_return: arm.is_return,
        }
    }

    /// Convert a Lambda into a top-level FuncDef + a Closure value.
    fn lift_lambda(
        &mut self,
        params: Vec<SymbolId>,
        body: Expr<'src>,
        span: Span,
        ty: crate::types::engine::Type,
    ) -> Expr<'src> {
        // Compute free variables of the body w.r.t. the lambda params.
        let bound: HashSet<SymbolId> = params.iter().copied().collect();
        let captures = ast::free_names(&body, &bound, &mut HashSet::new(), &|sym| {
            !matches!(self.symbols.get(sym).kind, SymbolKind::Local)
        });

        // Create capture parameter symbols for the lifted function.
        let capture_params: Vec<SymbolId> = captures
            .iter()
            .map(|&cap| {
                let cap_name = format!("{}_cap", self.symbols.display(cap));
                self.symbols.fresh(cap_name, span, SymbolKind::Local)
            })
            .collect();

        // Rewrite the body: replace each captured variable reference
        // with the corresponding capture parameter.
        let body = substitute_captures(&body, &captures, &capture_params);

        // Build the lifted function: captures first, then original params.
        let func_sym = self.fresh_name(span);
        let mut all_params = capture_params.clone();
        all_params.extend(params);

        self.lifted.push(Decl::FuncDef {
            span,
            name: func_sym,
            params: all_params,
            body,
            doc: None,
        });

        // Return a Closure node that packs the captured values.
        let capture_exprs: Vec<Expr<'src>> = captures
            .iter()
            .map(|&cap| Expr::new(ExprKind::Name(cap), span))
            .collect();

        let mut closure = Expr::new(
            ExprKind::Closure {
                func: func_sym,
                captures: capture_exprs,
            },
            span,
        );
        closure.ty = ty;
        closure
    }
}

/// Replace references to captured variables with their corresponding
/// capture parameters in the lifted function body.
fn substitute_captures<'src>(
    expr: &Expr<'src>,
    captures: &[SymbolId],
    capture_params: &[SymbolId],
) -> Expr<'src> {
    let mut result = expr.clone();
    subst_expr(&mut result, captures, capture_params);
    result
}

fn subst_expr(expr: &mut Expr<'_>, captures: &[SymbolId], params: &[SymbolId]) {
    match &mut expr.kind {
        ExprKind::Name(sym) => {
            if let Some(idx) = captures.iter().position(|c| c == sym) {
                *sym = params[idx];
            }
        }
        ExprKind::Call { target, args } => {
            if let Some(idx) = captures.iter().position(|c| c == target) {
                *target = params[idx];
            }
            for a in args {
                subst_expr(a, captures, params);
            }
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            subst_expr(lhs, captures, params);
            subst_expr(rhs, captures, params);
        }
        ExprKind::QualifiedCall { args, .. } => {
            for a in args {
                subst_expr(a, captures, params);
            }
        }
        ExprKind::Block(stmts, result) => {
            for s in stmts {
                subst_stmt(s, captures, params);
            }
            subst_expr(result, captures, params);
        }
        ExprKind::If {
            expr: scrutinee,
            arms,
            else_body,
        } => {
            subst_expr(scrutinee, captures, params);
            for arm in arms {
                for g in &mut arm.guards {
                    subst_expr(g, captures, params);
                }
                subst_expr(&mut arm.body, captures, params);
            }
            if let Some(eb) = else_body {
                subst_expr(eb, captures, params);
            }
        }
        ExprKind::Fold {
            expr: scrutinee,
            arms,
        } => {
            subst_expr(scrutinee, captures, params);
            for arm in arms {
                for g in &mut arm.guards {
                    subst_expr(g, captures, params);
                }
                subst_expr(&mut arm.body, captures, params);
            }
        }
        ExprKind::Lambda { body, .. } => subst_expr(body, captures, params),
        ExprKind::Record { fields } => {
            for (_, e) in fields {
                subst_expr(e, captures, params);
            }
        }
        ExprKind::RecordUpdate { base, updates } => {
            subst_expr(base, captures, params);
            for (_, e) in updates {
                subst_expr(e, captures, params);
            }
        }
        ExprKind::FieldAccess { record, .. } => subst_expr(record, captures, params),
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems {
                subst_expr(e, captures, params);
            }
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            subst_expr(receiver, captures, params);
            for a in args {
                subst_expr(a, captures, params);
            }
        }
        ExprKind::Is { expr: inner, .. } => subst_expr(inner, captures, params),
        ExprKind::Closure { captures: caps, .. } => {
            for c in caps {
                subst_expr(c, captures, params);
            }
        }
        ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) => {}
    }
}

fn subst_stmt(stmt: &mut Stmt<'_>, captures: &[SymbolId], params: &[SymbolId]) {
    match stmt {
        Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => {
            subst_expr(val, captures, params);
        }
        Stmt::Guard {
            condition,
            return_val,
        } => {
            subst_expr(condition, captures, params);
            subst_expr(return_val, captures, params);
        }
        Stmt::TypeHint { .. } => {}
    }
}
