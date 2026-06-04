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

use std::collections::{HashMap, HashSet};

use crate::ast::{self, Decl, Expr, ExprKind, Module, Span, Stmt};
use crate::passes::resolve::Resolved;
use crate::symbol::{SymbolId, SymbolKind, SymbolTable};

/// Pre-inference lambda lift: convert every `Lambda` into a
/// top-level `FuncDef __lifted_N(captures..., params...)` plus an
/// `ExprKind::Closure { func: __lifted_N, captures: [Name(c0), ...] }`
/// at the lambda site. **Runs before inference.**
///
/// Inference types the `Closure` node by looking up `__lifted_N`'s
/// scheme (computed during this same infer pass, ordered first by
/// topo) and producing `Arrow(remaining_params, ret)` after dropping
/// the leading N capture params. That keeps closures Arrow-typed at
/// inference time — sidestepping the Arrow-vs-TagUnion unification
/// gap — while still freeing later passes to synthesize per-call-site
/// closure tag unions in `lambda::specialize`.
///
/// After this runs:
/// - Every former `Lambda` is `ExprKind::Closure { func, captures }`.
/// - Top-level `__lifted_N` FuncDefs exist for the lambda bodies.
/// - `func_schemes` is *not* touched — that table doesn't exist yet
///   pre-infer; inference will populate it.
pub fn lift_pre_infer(resolved: &mut Resolved<'_>) {
    let module = std::mem::take(&mut resolved.module);
    resolved.module = lift_module_pre_infer(module, &mut resolved.symbols);
}

fn lift_module_pre_infer<'src>(
    module: Module<'src>,
    symbols: &mut SymbolTable,
) -> Module<'src> {
    let mut ctx = PreInferLiftCtx {
        symbols,
        synthesized: Vec::new(),
        counter: 0,
    };

    // Process each decl in order. Synthesized __lifted_N and
    // __ClosureType_N decls created during a decl's processing
    // are prepended before it so they appear earlier in
    // declaration order — needed for the topo pass (which runs
    // after lift, pre-infer) to order them as dependencies of
    // their use sites.
    let mut new_decls: Vec<Decl<'src>> = Vec::new();
    for d in module.decls {
        let before = ctx.synthesized.len();
        let d = ctx.lift_decl(d);
        new_decls.extend(ctx.synthesized.drain(before..));
        new_decls.push(d);
    }

    Module {
        exports: module.exports,
        imports: module.imports,
        decls: new_decls,
    }
}

struct PreInferLiftCtx<'a, 'src> {
    symbols: &'a mut SymbolTable,
    /// Decls synthesized during lifting: `__lifted_N` FuncDefs and
    /// `__ClosureType_N` TypeAnnos, in the order they were created
    /// (inner lambdas first, ready to be prepended).
    synthesized: Vec<Decl<'src>>,
    /// Monotonic counter for fresh names. Each lambda burns one
    /// counter value across all three synthesized names
    /// (`__lifted_N`, `__ClosureType_N`, `__ClosureTag_N`).
    counter: usize,
}

impl<'src> PreInferLiftCtx<'_, 'src> {
    fn fresh_id(&mut self) -> usize {
        let id = self.counter;
        self.counter += 1;
        id
    }

    fn lift_decl(&mut self, decl: Decl<'src>) -> Decl<'src> {
        match decl {
            Decl::FuncDef { span, name, params, body, doc } => {
                let body = self.lift_expr(body);
                Decl::FuncDef { span, name, params, body, doc }
            }
            Decl::TypeAnno { span, name, type_params, ty, where_clause, methods, kind, doc } => {
                let methods = methods.into_iter().map(|m| self.lift_decl(m)).collect();
                Decl::TypeAnno { span, name, type_params, ty, where_clause, methods, kind, doc }
            }
        }
    }

    fn lift_expr(&mut self, mut expr: Expr<'src>) -> Expr<'src> {
        // Post-order: lift child lambdas first so capture-substitution
        // operates on already-lifted child expressions.
        expr.kind = match expr.kind {
            ExprKind::Lambda { params, body } => {
                let body = self.lift_expr(*body);
                return self.lift_lambda(params, body, expr.span);
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
            ExprKind::QualifiedCall { segments, args, resolved } => ExprKind::QualifiedCall {
                segments,
                args: args.into_iter().map(|a| self.lift_expr(a)).collect(),
                resolved,
            },
            ExprKind::Block(stmts, result) => {
                let stmts = stmts.into_iter().map(|s| self.lift_stmt(s)).collect();
                ExprKind::Block(stmts, Box::new(self.lift_expr(*result)))
            }
            ExprKind::If { expr: scr, arms, else_body } => ExprKind::If {
                expr: Box::new(self.lift_expr(*scr)),
                arms: arms.into_iter().map(|a| self.lift_arm(a)).collect(),
                else_body: else_body.map(|e| Box::new(self.lift_expr(*e))),
            },
            ExprKind::Fold { expr: scr, arms } => ExprKind::Fold {
                expr: Box::new(self.lift_expr(*scr)),
                arms: arms.into_iter().map(|a| self.lift_arm(a)).collect(),
            },
            ExprKind::Record { fields } => ExprKind::Record {
                fields: fields.into_iter().map(|(f, e)| (f, self.lift_expr(e))).collect(),
            },
            ExprKind::RecordUpdate { base, updates } => ExprKind::RecordUpdate {
                base: Box::new(self.lift_expr(*base)),
                updates: updates.into_iter().map(|(f, e)| (f, self.lift_expr(e))).collect(),
            },
            ExprKind::FieldAccess { record, field } => ExprKind::FieldAccess {
                record: Box::new(self.lift_expr(*record)),
                field,
            },
            ExprKind::Tuple(elems) => ExprKind::Tuple(
                elems.into_iter().map(|e| self.lift_expr(e)).collect()
            ),
            ExprKind::ListLit(elems) => ExprKind::ListLit(
                elems.into_iter().map(|e| self.lift_expr(e)).collect()
            ),
            ExprKind::MethodCall { receiver, method, args, resolved } => ExprKind::MethodCall {
                receiver: Box::new(self.lift_expr(*receiver)),
                method,
                args: args.into_iter().map(|a| self.lift_expr(a)).collect(),
                resolved,
            },
            ExprKind::Is { expr: inner, pattern } => ExprKind::Is {
                expr: Box::new(self.lift_expr(*inner)),
                pattern,
            },
            ExprKind::Closure { .. } => {
                panic!(
                    "ExprKind::Closure should not exist pre-infer — \
                     lift_pre_infer is the only producer of closure values \
                     and it emits Call(closure_tag, captures) directly"
                );
            }
            kind @ (ExprKind::IntLit(_)
            | ExprKind::FloatLit(_)
            | ExprKind::StrLit(_)
            | ExprKind::Name(_)) => kind,
        };
        expr
    }

    fn lift_stmt(&mut self, stmt: Stmt<'src>) -> Stmt<'src> {
        match stmt {
            Stmt::Let { name, val } => Stmt::Let { name, val: self.lift_expr(val) },
            Stmt::Destructure { pattern, val } => Stmt::Destructure {
                pattern,
                val: self.lift_expr(val),
            },
            Stmt::Guard { condition, return_val } => Stmt::Guard {
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

    /// Convert a Lambda expression to a lifted FuncDef + a Closure
    /// node at the call site.
    ///
    ///   1. Mint __lifted_N symbol.
    ///   2. Compute captures (lexical free vars w.r.t. lambda params).
    ///   3. Synthesize a FuncDef __lifted_N(c0, c1, ..., p0, p1, ...)
    ///      whose body is the lambda body with captures substituted
    ///      to the new capture parameters.
    ///   4. Return ExprKind::Closure { func: __lifted_N, captures }
    ///      at the lambda site.
    ///
    /// No type information is consulted. Captures are detected
    /// lexically. Inference will type the Closure node by looking up
    /// __lifted_N's scheme and dropping the leading N capture params.
    /// Downstream lambda passes (solve/specialize/narrow) operate on
    /// Closure nodes as today; specialize is still responsible for
    /// synthesizing closure tag unions per call-site set.
    fn lift_lambda(
        &mut self,
        params: Vec<SymbolId>,
        body: Expr<'src>,
        span: Span,
    ) -> Expr<'src> {
        let id = self.fresh_id();
        let lifted_name = format!("__lifted_{id}");
        let lifted_sym = self.symbols.fresh(&lifted_name, span, SymbolKind::Func);

        // Lexical captures: free names of the body that aren't the
        // lambda's own params. `is_known` returns true to EXCLUDE the
        // symbol — so we exclude top-level constructors/functions;
        // locals fall through and are captured.
        let bound: HashSet<SymbolId> = params.iter().copied().collect();
        let captures = ast::free_names(&body, &bound, &mut HashSet::new(), &|sym| {
            !matches!(self.symbols.get(sym).kind, SymbolKind::Local)
        });

        // Mint fresh capture parameter symbols for the lifted
        // function.
        let capture_params: Vec<SymbolId> = captures
            .iter()
            .map(|&cap| {
                let cap_name = format!("{}_cap", self.symbols.display(cap));
                self.symbols.fresh(cap_name, span, SymbolKind::Local)
            })
            .collect();

        // Rewrite the body: replace each captured local with the
        // corresponding capture parameter sym.
        let body = substitute_captures(&body, &captures, &capture_params);

        // Build FuncDef for the lifted function: captures first,
        // then original params. Inference derives its scheme.
        let mut all_params = capture_params.clone();
        all_params.extend(params);
        let lifted_decl = Decl::FuncDef {
            span,
            name: lifted_sym,
            params: all_params,
            body,
            doc: None,
        };
        self.synthesized.push(lifted_decl);

        // Replace the Lambda with a Closure node. Captures are Name
        // refs to the captured locals (still in scope where the
        // lambda appeared). Type is left as the inference placeholder
        // — infer's ExprKind::Closure arm fills it in.
        let capture_exprs: Vec<Expr<'src>> = captures
            .iter()
            .map(|&cap| Expr::new(ExprKind::Name(cap), span))
            .collect();
        Expr::new(
            ExprKind::Closure {
                func: lifted_sym,
                captures: capture_exprs,
            },
            span,
        )
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
