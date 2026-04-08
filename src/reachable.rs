use std::collections::{HashMap, HashSet};

use crate::decl_info::{DeclInfo, method_key};
use crate::syntax::ast::{self, Decl, Expr, ExprKind, Stmt};
use crate::types::infer::InferResult;

/// Compute the set of reachable function names starting from "main".
///
/// Walks the call graph through user declarations, stdlib methods, and method
/// resolutions, expanding through function aliases.
pub fn compute(
    decls: &DeclInfo,
    module: &ast::Module<'_>,
    infer_result: &InferResult,
) -> HashSet<String> {
    let mut bodies: HashMap<String, &Expr<'_>> = HashMap::new();

    for decl in &module.decls {
        match decl {
            Decl::FuncDef { name, body, .. } => {
                bodies.insert((*name).to_owned(), body);
            }
            Decl::TypeAnno {
                name: type_name,
                methods,
                ..
            } => {
                for m in methods {
                    if let Decl::FuncDef {
                        name: method_name,
                        body,
                        ..
                    } = m
                    {
                        bodies.insert(method_key(type_name, method_name), body);
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
            collect_refs(body, &mut worklist);
        }
    }

    // Expand reachable: if a name is reachable, all its aliases are too
    let reachable_snapshot: Vec<String> = reachable.iter().cloned().collect();
    for key in &reachable_snapshot {
        if let Some(aliases) = decls.func_aliases.get(key) {
            for alias in aliases {
                reachable.insert(alias.clone());
            }
        }
    }

    // Add method-resolved functions to reachable set
    let resolved_methods: Vec<String> = infer_result.method_resolutions.values().cloned().collect();
    reachable.extend(resolved_methods);

    reachable
}

fn collect_refs(expr: &Expr<'_>, refs: &mut Vec<String>) {
    match &expr.kind {
        ExprKind::Call { func, args } => {
            refs.push((*func).to_owned());
            for a in args {
                collect_refs(a, refs);
            }
        }
        ExprKind::QualifiedCall { segments, args } => {
            refs.push(segments.join("."));
            for a in args {
                collect_refs(a, refs);
            }
        }
        ExprKind::Name(name) => {
            refs.push((*name).to_owned());
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            collect_refs(lhs, refs);
            collect_refs(rhs, refs);
        }
        ExprKind::Block(stmts, result) => {
            for stmt in stmts {
                match stmt {
                    Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => {
                        collect_refs(val, refs);
                    }
                    Stmt::TypeHint { .. } => {}
                }
            }
            collect_refs(result, refs);
        }
        ExprKind::If {
            expr: e,
            arms,
            else_body,
        } => {
            collect_refs(e, refs);
            for arm in arms {
                collect_refs(&arm.body, refs);
            }
            if let Some(eb) = else_body {
                collect_refs(eb, refs);
            }
        }
        ExprKind::Fold { expr: e, arms } => {
            collect_refs(e, refs);
            for arm in arms {
                collect_refs(&arm.body, refs);
            }
        }
        ExprKind::Lambda { body, .. } => collect_refs(body, refs),
        ExprKind::Record { fields } => {
            for (_, e) in fields {
                collect_refs(e, refs);
            }
        }
        ExprKind::FieldAccess { record, .. } => collect_refs(record, refs),
        ExprKind::MethodCall { receiver, args, .. } => {
            collect_refs(receiver, refs);
            for a in args {
                collect_refs(a, refs);
            }
        }
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems {
                collect_refs(e, refs);
            }
        }
        ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) => {}
    }
}
