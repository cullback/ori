//! Fold lifting — AST → AST rewrite that eliminates [`ast::ExprKind::Fold`].
//!
//! Each `fold` expression becomes a call to a fresh `__fold_N` helper
//! function appended to the module. The helper takes the scrutinee as
//! its first parameter plus one additional parameter per captured free
//! variable. Inside the helper, the scrutinee is matched against each
//! arm and recursive constructor fields are rebound via explicit
//! recursive calls (shadowing the pattern bindings).
//!
//! Runs post-resolve, pre-inference: the synthesized helpers get their
//! types filled in naturally when inference runs. Recursive fields are
//! detected syntactically from `Decl::TypeAnno` declarations, so no
//! type information is needed.
//!
//! After this pass no `Fold` nodes remain in the `ast::Module`, and the
//! SSA lowerer no longer has to know about them.

use std::collections::{HashMap, HashSet};

use crate::ast;
use crate::symbol::{SymbolId, SymbolKind, SymbolTable};

/// Lift every `Fold` expression in `module` to a top-level `__fold_N`
/// helper function. Returns the rewritten module. `symbols` is used to
/// allocate fresh `SymbolId`s for each synthesized helper.
pub fn lift<'src>(mut module: ast::Module<'src>, symbols: &mut SymbolTable) -> ast::Module<'src> {
    let recursive_fields = collect_recursive_fields(&module, symbols);

    let mut ctx = LiftCtx {
        counter: 0,
        synth_span_counter: 0,
        synthesized: Vec::new(),
        recursive_fields: &recursive_fields,
        symbols,
    };

    for decl in &mut module.decls {
        lift_decl(&mut ctx, decl);
    }
    module.decls.extend(ctx.synthesized);
    module
}

// ---- Lift context ----

struct LiftCtx<'a, 'src> {
    counter: usize,
    /// Counter used to mint unique synthetic spans. Multiple synthesized
    /// nodes (the scrutinee `Name` ref, recursive calls, helper body)
    /// would otherwise all share the original fold's span, and
    /// `write_types_back` keys on span — so collisions cause type
    /// info to bleed between unrelated synthesized nodes in snapshots.
    synth_span_counter: usize,
    synthesized: Vec<ast::Decl<'src>>,
    /// Per-constructor recursive-field flags: `recursive_fields[con]` is
    /// a vector of booleans, one per field of that constructor.
    recursive_fields: &'a HashMap<&'src str, Vec<bool>>,
    /// Owns symbol IDs for synthesized helpers AND for the synthesized
    /// parameters/local bindings inside each helper.
    symbols: &'a mut SymbolTable,
}

impl LiftCtx<'_, '_> {
    /// Mint a fresh synthetic span derived from `base.file`. Uses
    /// high-offset values (`usize::MAX - n`) so it cannot collide with
    /// real source offsets in any plausible file.
    const fn fresh_span(&mut self, base: ast::Span) -> ast::Span {
        let off = usize::MAX - self.synth_span_counter;
        self.synth_span_counter = self.synth_span_counter.saturating_add(1);
        ast::Span {
            file: base.file,
            start: off,
            end: off,
        }
    }
}

// ---- Pre-pass: collect metadata ----

/// For every tag in every `TagUnion` declaration, record which fields
/// have a type that refers back to the enclosing type (i.e., are
/// structurally recursive). Mirrors `decl_info::register_tag_union`.
fn collect_recursive_fields<'src>(
    module: &ast::Module<'src>,
    symbols: &SymbolTable,
) -> HashMap<&'src str, Vec<bool>> {
    let mut out = HashMap::new();
    for decl in &module.decls {
        collect_rec_from_decl(decl, &mut out, symbols);
    }
    out
}

fn collect_rec_from_decl<'src>(
    decl: &ast::Decl<'src>,
    out: &mut HashMap<&'src str, Vec<bool>>,
    symbols: &SymbolTable,
) {
    if let ast::Decl::TypeAnno {
        name: type_name,
        ty: ast::TypeExpr::TagUnion(tags, _),
        methods,
        ..
    } = decl
    {
        let type_name_str = symbols.display(*type_name);
        for tag in tags {
            let flags: Vec<bool> = tag
                .fields
                .iter()
                .map(|f| {
                    matches!(
                        f,
                        ast::TypeExpr::Named(n) | ast::TypeExpr::App(n, _) if *n == type_name_str
                    )
                })
                .collect();
            out.insert(tag.name, flags);
        }
        for m in methods {
            collect_rec_from_decl(m, out, symbols);
        }
    }
}

// ---- Walker ----

fn lift_decl<'src>(ctx: &mut LiftCtx<'_, 'src>, decl: &mut ast::Decl<'src>) {
    match decl {
        ast::Decl::FuncDef { body, .. } => lift_expr(ctx, body),
        ast::Decl::TypeAnno { methods, .. } => {
            for m in methods {
                lift_decl(ctx, m);
            }
        }
    }
}

/// Post-order traversal: transform children first so inner folds are
/// already lifted by the time we look at the outer one. If the current
/// expression is a `Fold`, replace it with a `Call` to a synthesized
/// helper and append the helper to `ctx.synthesized`.
fn lift_expr<'src>(ctx: &mut LiftCtx<'_, 'src>, expr: &mut ast::Expr<'src>) {
    // Recurse into children first (post-order).
    match &mut expr.kind {
        ast::ExprKind::IntLit(_)
        | ast::ExprKind::FloatLit(_)
        | ast::ExprKind::StrLit(_)
        | ast::ExprKind::Name(_) => {}
        ast::ExprKind::BinOp { lhs, rhs, .. } => {
            lift_expr(ctx, lhs);
            lift_expr(ctx, rhs);
        }
        ast::ExprKind::Call { args, .. } | ast::ExprKind::QualifiedCall { args, .. } => {
            for a in args {
                lift_expr(ctx, a);
            }
        }
        ast::ExprKind::Block(stmts, result) => {
            for s in stmts {
                lift_stmt(ctx, s);
            }
            lift_expr(ctx, result);
        }
        ast::ExprKind::If {
            expr: scrutinee,
            arms,
            else_body,
        } => {
            lift_expr(ctx, scrutinee);
            for arm in arms {
                for g in &mut arm.guards {
                    lift_expr(ctx, g);
                }
                lift_expr(ctx, &mut arm.body);
            }
            if let Some(eb) = else_body {
                lift_expr(ctx, eb);
            }
        }
        ast::ExprKind::Fold {
            expr: scrutinee,
            arms,
        } => {
            lift_expr(ctx, scrutinee);
            for arm in arms {
                for g in &mut arm.guards {
                    lift_expr(ctx, g);
                }
                lift_expr(ctx, &mut arm.body);
            }
        }
        ast::ExprKind::Lambda { body, .. } => lift_expr(ctx, body),
        ast::ExprKind::Record { fields } => {
            for (_, e) in fields {
                lift_expr(ctx, e);
            }
        }
        ast::ExprKind::FieldAccess { record, .. } => lift_expr(ctx, record),
        ast::ExprKind::Tuple(elems) | ast::ExprKind::ListLit(elems) => {
            for e in elems {
                lift_expr(ctx, e);
            }
        }
        ast::ExprKind::MethodCall { receiver, args, .. } => {
            lift_expr(ctx, receiver);
            for a in args {
                lift_expr(ctx, a);
            }
        }
        ast::ExprKind::Is { expr: inner, .. } => lift_expr(ctx, inner),
        ast::ExprKind::RecordUpdate { base, updates } => {
            lift_expr(ctx, base);
            for (_, e) in updates {
                lift_expr(ctx, e);
            }
        }
    }

    // Post-order transform: if this is a Fold, replace it.
    if !matches!(&expr.kind, ast::ExprKind::Fold { .. }) {
        return;
    }
    let span = expr.span;
    // Swap the Fold out with a dummy so we can own its contents.
    let kind = std::mem::replace(&mut expr.kind, ast::ExprKind::IntLit(0));
    let ast::ExprKind::Fold {
        expr: scrutinee,
        arms,
    } = kind
    else {
        unreachable!("checked via matches! above");
    };
    let (new_kind, helper) = build_lifted_call(ctx, *scrutinee, arms, span);
    expr.kind = new_kind;
    ctx.synthesized.push(helper);
}

fn lift_stmt<'src>(ctx: &mut LiftCtx<'_, 'src>, stmt: &mut ast::Stmt<'src>) {
    match stmt {
        ast::Stmt::Let { val, .. } | ast::Stmt::Destructure { val, .. } => {
            lift_expr(ctx, val);
        }
        ast::Stmt::Guard {
            condition,
            return_val,
        } => {
            lift_expr(ctx, condition);
            lift_expr(ctx, return_val);
        }
        ast::Stmt::TypeHint { .. } => {}
    }
}

// ---- Lift transformation ----

/// Build the `Call { target: __fold_N, args: [scrutinee, ...captures] }`
/// expression that replaces an in-place `Fold`, and the `__fold_N`
/// `FuncDef` that will be appended to the module.
fn build_lifted_call<'src>(
    ctx: &mut LiftCtx<'_, 'src>,
    scrutinee: ast::Expr<'src>,
    arms: Vec<ast::MatchArm<'src>>,
    span: ast::Span,
) -> (ast::ExprKind<'src>, ast::Decl<'src>) {
    // Compute free-variable captures as `SymbolId`s. `ast::free_names`
    // collects every referenced `SymbolId` that isn't bound inside the
    // arms — we filter out top-level globals (Func/Type/Method) below
    // so only true locals become captures.
    let captures = collect_captures(&arms, ctx.symbols);

    // Allocate the helper's `SymbolId` from the symbol table. Display
    // name follows the old `__fold_N` convention so ssa mangling and
    // snapshots stay consistent.
    let helper_display = format!("__fold_{}", ctx.counter);
    let helper_sym = ctx.symbols.fresh(helper_display, span, SymbolKind::Func);
    ctx.counter = ctx.counter.saturating_add(1);

    // Allocate a fresh `SymbolId` for the scrutinee parameter and one
    // per capture. The helper's parameters are all locals.
    let scrut_param_sym = ctx
        .symbols
        .fresh("__fold_scrutinee", span, SymbolKind::Local);

    // Inside the helper body, references to each captured variable
    // must point at the helper's own parameter (not the outer scope's
    // SymbolId). Build a substitution map from outer-capture-sym to
    // helper-param-sym and apply it to each arm body.
    let mut capture_param_syms: Vec<SymbolId> = Vec::with_capacity(captures.len());
    let mut subst: HashMap<SymbolId, SymbolId> = HashMap::new();
    for &cap_sym in &captures {
        let display = ctx.symbols.display(cap_sym).to_owned();
        let param_sym = ctx.symbols.fresh(display, span, SymbolKind::Local);
        capture_param_syms.push(param_sym);
        subst.insert(cap_sym, param_sym);
    }

    let mut params: Vec<SymbolId> = Vec::with_capacity(captures.len().saturating_add(1));
    params.push(scrut_param_sym);
    params.extend(capture_param_syms.iter().copied());

    // Transform each arm: substitute outer captures to helper params,
    // and if the pattern has recursive fields bound to names, prepend
    // let-bindings that shadow those names with recursive calls to
    // the helper.
    let mut transformed_arms: Vec<ast::MatchArm<'src>> = Vec::with_capacity(arms.len());
    for arm in arms {
        let substituted = substitute_arm(arm, &subst);
        transformed_arms.push(transform_arm(
            ctx,
            substituted,
            helper_sym,
            &capture_param_syms,
            scrut_param_sym,
        ));
    }

    // Helper body: `if __fold_scrutinee ...arms...`. Use distinct
    // synthetic spans for every new node so `write_types_back` doesn't
    // overwrite each one with the same entry.
    let scrut_span = ctx.fresh_span(span);
    let if_span = ctx.fresh_span(span);
    let scrut_ref = ast::Expr::new(ast::ExprKind::Name(scrut_param_sym), scrut_span);
    let helper_body = ast::Expr::new(
        ast::ExprKind::If {
            expr: Box::new(scrut_ref),
            arms: transformed_arms,
            else_body: None,
        },
        if_span,
    );

    let helper_decl = ast::Decl::FuncDef {
        span,
        name: helper_sym,
        params,
        body: helper_body,
        doc: None,
    };

    // Replacement call: `__fold_N(scrutinee, ...captures)`. The scrutinee
    // is the original expression (keeps its source span); each capture
    // Name ref gets its own fresh span. Captures here reference the
    // OUTER scope's SymbolIds (not the helper's params).
    let mut call_args: Vec<ast::Expr<'src>> = Vec::with_capacity(captures.len().saturating_add(1));
    call_args.push(scrutinee);
    for &cap in &captures {
        let cap_span = ctx.fresh_span(span);
        call_args.push(ast::Expr::new(ast::ExprKind::Name(cap), cap_span));
    }
    let call_kind = ast::ExprKind::Call {
        target: helper_sym,
        args: call_args,
    };

    (call_kind, helper_decl)
}

/// Compute the free `SymbolId`s of the arm bodies and guards, excluding
/// pattern bindings and top-level globals (Func/Type/Method). Returns
/// a stable-ordered vec (first-referenced-first).
fn collect_captures(arms: &[ast::MatchArm<'_>], symbols: &SymbolTable) -> Vec<SymbolId> {
    let is_global = |sym: SymbolId| {
        !matches!(symbols.get(sym).kind, SymbolKind::Local)
    };
    let mut captures: Vec<SymbolId> = Vec::new();
    let mut seen: HashSet<SymbolId> = HashSet::new();

    for arm in arms {
        let mut bound: HashSet<SymbolId> = HashSet::new();
        arm.pattern.bind_syms(&mut bound);
        for e in arm.guards.iter().chain(std::iter::once(&arm.body)) {
            for sym in ast::free_names(e, &bound, &mut seen, &is_global) {
                captures.push(sym);
            }
        }
    }
    captures
}

/// For each recursive field in a constructor arm pattern that is bound
/// by name, prepend `let <name> = __fold_N(<name>, ...captures)` to the
/// arm body so the user's code sees the recursed value instead of the
/// raw sub-tree. Wildcard fields are skipped (no name to rebind).
fn transform_arm<'src>(
    ctx: &mut LiftCtx<'_, 'src>,
    arm: ast::MatchArm<'src>,
    helper_sym: SymbolId,
    capture_param_syms: &[SymbolId],
    _scrut_param_sym: SymbolId,
) -> ast::MatchArm<'src> {
    let ast::MatchArm {
        pattern,
        guards,
        body,
        is_return,
    } = arm;

    // Only `Con(..)` patterns can have recursive fields; everything else
    // passes through unchanged.
    let ast::Pattern::Constructor {
        name: con_name,
        fields,
    } = &pattern
    else {
        return ast::MatchArm {
            pattern,
            guards,
            body,
            is_return,
        };
    };

    let flags: &[bool] = ctx
        .recursive_fields
        .get(con_name)
        .map_or(&[], Vec::as_slice);

    // Collect the SymbolIds of recursive fields bound by name. Wildcard
    // and nested patterns are silently skipped.
    let rec_bindings: Vec<SymbolId> = fields
        .iter()
        .enumerate()
        .filter_map(|(i, pat)| {
            if flags.get(i).copied().unwrap_or(false)
                && let ast::Pattern::Binding(sym) = pat
            {
                return Some(*sym);
            }
            None
        })
        .collect();

    if rec_bindings.is_empty() {
        return ast::MatchArm {
            pattern,
            guards,
            body,
            is_return,
        };
    }

    // Wrap the body in a Block with one `let <name> = helper(<name>, captures)`
    // statement per recursive binding. The recursive call uses the
    // pattern-bound symbol as both the read (first arg) and the rebind
    // target — i.e. `let hd = __fold_N(hd, cap1, cap2)`. Note that
    // shadowing is represented by allocating a FRESH SymbolId for the
    // new let, so references after the let use the new sym. Since
    // fold_lift runs before any substitution walks, and the subsequent
    // uses inside the arm's body are already pointing at the pattern
    // binding's original sym... actually, in the existing AST, the
    // body's references point at the pattern-bound `hd` sym. Replacing
    // `hd` with a fresh sym and inserting a `let new_hd = ...` would
    // require walking the body to rewrite references. Simpler: reuse
    // the pattern's SymbolId for the let's name so existing body
    // references continue to point at the same sym. Inference and SSA
    // both treat `let x = ...` as an assignment to `x`, so reusing the
    // sym is equivalent to shadowing.
    let base_span = body.span;
    let mut stmts: Vec<ast::Stmt<'src>> = Vec::with_capacity(rec_bindings.len());
    for &binding_sym in &rec_bindings {
        let mut call_args: Vec<ast::Expr<'src>> =
            Vec::with_capacity(capture_param_syms.len().saturating_add(1));
        let bind_span = ctx.fresh_span(base_span);
        call_args.push(ast::Expr::new(ast::ExprKind::Name(binding_sym), bind_span));
        for &cap_sym in capture_param_syms {
            let cap_span = ctx.fresh_span(base_span);
            call_args.push(ast::Expr::new(ast::ExprKind::Name(cap_sym), cap_span));
        }
        let call_span = ctx.fresh_span(base_span);
        let call = ast::Expr::new(
            ast::ExprKind::Call {
                target: helper_sym,
                args: call_args,
            },
            call_span,
        );
        stmts.push(ast::Stmt::Let {
            name: binding_sym,
            val: call,
        });
    }
    let block_span = ctx.fresh_span(base_span);
    let new_body = ast::Expr::new(ast::ExprKind::Block(stmts, Box::new(body)), block_span);

    ast::MatchArm {
        pattern,
        guards,
        body: new_body,
        is_return,
    }
}

// ---- Capture substitution ----

/// Substitute every `SymbolId` reference (in `Name`, `Call.target`) in
/// an arm body according to `subst`. Used to rewrite outer-capture
/// references to the helper's own parameter bindings.
fn substitute_arm<'src>(
    arm: ast::MatchArm<'src>,
    subst: &HashMap<SymbolId, SymbolId>,
) -> ast::MatchArm<'src> {
    let ast::MatchArm {
        pattern,
        mut guards,
        mut body,
        is_return,
    } = arm;
    for g in &mut guards {
        substitute_expr(g, subst);
    }
    substitute_expr(&mut body, subst);
    ast::MatchArm {
        pattern,
        guards,
        body,
        is_return,
    }
}

fn substitute_expr(expr: &mut ast::Expr<'_>, subst: &HashMap<SymbolId, SymbolId>) {
    match &mut expr.kind {
        ast::ExprKind::Name(sym) => {
            if let Some(&new_sym) = subst.get(sym) {
                *sym = new_sym;
            }
        }
        ast::ExprKind::Call { target, args } => {
            if let Some(&new_sym) = subst.get(target) {
                *target = new_sym;
            }
            for a in args {
                substitute_expr(a, subst);
            }
        }
        ast::ExprKind::QualifiedCall { args, .. } => {
            for a in args {
                substitute_expr(a, subst);
            }
        }
        ast::ExprKind::MethodCall { receiver, args, .. } => {
            substitute_expr(receiver, subst);
            for a in args {
                substitute_expr(a, subst);
            }
        }
        ast::ExprKind::BinOp { lhs, rhs, .. } => {
            substitute_expr(lhs, subst);
            substitute_expr(rhs, subst);
        }
        ast::ExprKind::Block(stmts, result) => {
            for s in stmts {
                substitute_stmt(s, subst);
            }
            substitute_expr(result, subst);
        }
        ast::ExprKind::If {
            expr: scrutinee,
            arms,
            else_body,
        } => {
            substitute_expr(scrutinee, subst);
            for arm in arms {
                for g in &mut arm.guards {
                    substitute_expr(g, subst);
                }
                substitute_expr(&mut arm.body, subst);
            }
            if let Some(eb) = else_body {
                substitute_expr(eb, subst);
            }
        }
        ast::ExprKind::Fold {
            expr: scrutinee,
            arms,
        } => {
            substitute_expr(scrutinee, subst);
            for arm in arms {
                for g in &mut arm.guards {
                    substitute_expr(g, subst);
                }
                substitute_expr(&mut arm.body, subst);
            }
        }
        ast::ExprKind::Lambda { body, .. } => substitute_expr(body, subst),
        ast::ExprKind::Record { fields } => {
            for (_, e) in fields {
                substitute_expr(e, subst);
            }
        }
        ast::ExprKind::FieldAccess { record, .. } => substitute_expr(record, subst),
        ast::ExprKind::Tuple(elems) | ast::ExprKind::ListLit(elems) => {
            for e in elems {
                substitute_expr(e, subst);
            }
        }
        ast::ExprKind::Is { expr: inner, .. } => substitute_expr(inner, subst),
        ast::ExprKind::RecordUpdate { base, updates } => {
            substitute_expr(base, subst);
            for (_, e) in updates {
                substitute_expr(e, subst);
            }
        }
        ast::ExprKind::IntLit(_) | ast::ExprKind::FloatLit(_) | ast::ExprKind::StrLit(_) => {}
    }
}

fn substitute_stmt(stmt: &mut ast::Stmt<'_>, subst: &HashMap<SymbolId, SymbolId>) {
    match stmt {
        ast::Stmt::Let { val, .. } | ast::Stmt::Destructure { val, .. } => {
            substitute_expr(val, subst);
        }
        ast::Stmt::Guard {
            condition,
            return_val,
        } => {
            substitute_expr(condition, subst);
            substitute_expr(return_val, subst);
        }
        ast::Stmt::TypeHint { .. } => {}
    }
}
