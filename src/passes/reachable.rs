//! Reachability — DFS the call graph from `main`, prune dead decls.
//!
//! Step 9 makes this a `Module → Module` pass: [`prune`] returns a
//! new `Module` with every unreachable free `FuncDef` and every
//! unreachable method `FuncDef` dropped. `TypeAnno` decls (and their
//! constructors) stay as-is so `decl_info` can still register
//! constructor metadata for pattern-match lowering.
//!
//! [`compute`] is still exported because `defunc` uses it internally
//! to decide which function bodies to scan for lambda sets.

use std::collections::{HashMap, HashSet};

use crate::ast::{self, Decl, Expr, ExprKind, Module, Stmt};
use crate::passes::decl_info::{DeclInfo, method_key};
use crate::passes::mono::Monomorphized;
use crate::symbol::SymbolTable;

/// Drop unreachable decls from the module.
pub fn prune(mono: &mut Monomorphized<'_>, decls: &DeclInfo) {
    let module = std::mem::take(&mut mono.module);
    mono.module = prune_module(module, decls, &mono.symbols);
}

fn prune_module<'src>(
    module: Module<'src>,
    decls: &DeclInfo,
    symbols: &SymbolTable,
) -> Module<'src> {
    let reachable_set = compute(decls, &module, symbols);

    let mut new_decls: Vec<Decl<'src>> = Vec::new();
    for decl in module.decls {
        // Borrow before the match so the FuncDef arm can inspect
        // fields without moving out of `decl`.
        let keep_func = matches!(
            &decl,
            Decl::FuncDef { name, params, .. }
                if reachable_set.contains(symbols.display(*name))
                    || params.is_empty()
        );
        match decl {
            Decl::FuncDef { .. } => {
                // Keep zero-param value bindings even if reachability
                // doesn't trace them — they're referenced via Name
                // which defunc may rewrite, breaking the trace.
                if keep_func {
                    new_decls.push(decl);
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
                let type_name = symbols.display(name).to_owned();
                let kept_methods: Vec<Decl<'src>> = methods
                    .into_iter()
                    .filter(|m| match m {
                        Decl::FuncDef {
                            name: method_name, ..
                        } => {
                            let method_name_str = symbols.display(*method_name);
                            let mangled = method_key(&type_name, method_name_str);
                            reachable_set.contains(&mangled)
                        }
                        // Annotation-only methods (builtin stdlib
                        // methods like `List.walk`) stay — they
                        // don't have bodies and the lowerer
                        // dispatches them via naming convention.
                        Decl::TypeAnno { .. } => true,
                    })
                    .collect();
                new_decls.push(Decl::TypeAnno {
                    span,
                    name,
                    type_params,
                    ty,
                    where_clause,
                    methods: kept_methods,
                    kind,
                    doc,
                });
            }
        }
    }

    Module {
        exports: module.exports,
        imports: module.imports,
        decls: new_decls,
    }
}

/// Compute the set of reachable function names starting from "main".
///
/// Walks the call graph through user declarations, stdlib methods, and method
/// resolutions, expanding through function aliases.
pub fn compute(
    decls: &DeclInfo,
    module: &ast::Module<'_>,
    symbols: &SymbolTable,
) -> HashSet<String> {
    let mut bodies: HashMap<String, &Expr<'_>> = HashMap::new();

    for decl in &module.decls {
        match decl {
            Decl::FuncDef { name, body, .. } => {
                bodies.insert(symbols.display(*name).to_owned(), body);
            }
            Decl::TypeAnno {
                name: type_name,
                methods,
                ..
            } => {
                let type_name_str = symbols.display(*type_name);
                for m in methods {
                    if let Decl::FuncDef {
                        name: method_name,
                        body,
                        ..
                    } = m
                    {
                        let method_name_str = symbols.display(*method_name);
                        bodies.insert(method_key(type_name_str, method_name_str), body);
                    }
                }
            }
        }
    }

    let mut reachable = HashSet::new();
    let mut worklist = vec!["main".to_owned()];
    while let Some(name) = worklist.pop() {
        if !reachable.insert(name.clone()) {
            continue;
        }
        if let Some(body) = bodies.get(&name) {
            collect_refs(body, &mut worklist, symbols);
        }
    }

    // Post-mono every callsite uses its canonical mangled name, so
    // the old alias-expansion pass (which spread reachability through
    // `module.foo` ↔ `foo`) is obsolete. `decls` stays as a
    // parameter for API compatibility with callers that still want
    // to pass it; it's read only inside `collect_refs`.
    let _ = decls;
    reachable
}

fn is_list_walk(name: &str) -> bool {
    let base = name
        .strip_prefix("List.")
        .or_else(|| name.rsplit_once(".List.").map(|(_, rest)| rest));
    matches!(
        base,
        Some("walk" | "walk_until")
    )
}

#[allow(clippy::too_many_lines)]
fn collect_refs(expr: &Expr<'_>, refs: &mut Vec<String>, symbols: &SymbolTable) {
    match &expr.kind {
        ExprKind::Name(sym) => {
            // A bare name reference might refer to a top-level value
            // binding (zero-param function). Mark it reachable.
            refs.push(symbols.display(*sym).to_owned());
        }
        ExprKind::Call { target, args, .. } => {
            refs.push(symbols.display(*target).to_owned());
            for a in args {
                collect_refs(a, refs, symbols);
            }
        }
        ExprKind::QualifiedCall {
            segments,
            args,
            resolved,
        } => {
            let joined = segments.join(".");
            // Post-defunc, `List.walk` and its variants are lowered
            // by `ssa::lower` with an implicit call to the
            // corresponding `__apply_{mangled}_2` function that
            // defunc synthesized. That call doesn't show up in the
            // AST — it's emitted directly at lower time — so reachable
            // has to be told explicitly.
            if is_list_walk(&joined) {
                refs.push(format!("__apply_{joined}_2"));
            }
            refs.push(joined);
            if let Some(r) = resolved {
                if is_list_walk(r) {
                    refs.push(format!("__apply_{r}_2"));
                }
                refs.push(r.clone());
            }
            for a in args {
                collect_refs(a, refs, symbols);
            }
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            collect_refs(lhs, refs, symbols);
            collect_refs(rhs, refs, symbols);
        }
        ExprKind::Block(stmts, result) => {
            for stmt in stmts {
                match stmt {
                    Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => {
                        collect_refs(val, refs, symbols);
                    }
                    Stmt::Guard {
                        condition,
                        return_val,
                    } => {
                        collect_refs(condition, refs, symbols);
                        collect_refs(return_val, refs, symbols);
                    }
                    Stmt::TypeHint { .. } => {}
                }
            }
            collect_refs(result, refs, symbols);
        }
        ExprKind::If {
            expr: e,
            arms,
            else_body,
        } => {
            collect_refs(e, refs, symbols);
            for arm in arms {
                for guard_expr in &arm.guards {
                    collect_refs(guard_expr, refs, symbols);
                }
                collect_refs(&arm.body, refs, symbols);
            }
            if let Some(eb) = else_body {
                collect_refs(eb, refs, symbols);
            }
        }
        ExprKind::Fold { expr: e, arms } => {
            collect_refs(e, refs, symbols);
            for arm in arms {
                for guard_expr in &arm.guards {
                    collect_refs(guard_expr, refs, symbols);
                }
                collect_refs(&arm.body, refs, symbols);
            }
        }
        ExprKind::Lambda { body, .. } => collect_refs(body, refs, symbols),
        ExprKind::Record { fields } => {
            for (_, e) in fields {
                collect_refs(e, refs, symbols);
            }
        }
        ExprKind::FieldAccess { record, .. } => collect_refs(record, refs, symbols),
        ExprKind::MethodCall {
            receiver,
            args,
            resolved,
            ..
        } => {
            collect_refs(receiver, refs, symbols);
            if let Some(r) = resolved {
                if is_list_walk(r) {
                    refs.push(format!("__apply_{r}_2"));
                }
                refs.push(r.clone());
            }
            for a in args {
                collect_refs(a, refs, symbols);
            }
        }
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems {
                collect_refs(e, refs, symbols);
            }
        }
        ExprKind::Is { expr: inner, .. } => {
            collect_refs(inner, refs, symbols);
        }
        ExprKind::RecordUpdate { base, updates } => {
            collect_refs(base, refs, symbols);
            for (_, e) in updates {
                collect_refs(e, refs, symbols);
            }
        }
        ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) => {}
        ExprKind::Closure { func, captures } => {
            refs.push(symbols.display(*func).to_owned());
            for c in captures {
                collect_refs(c, refs, symbols);
            }
        }
    }
}
