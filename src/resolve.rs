use std::collections::{HashMap, HashSet};
use std::path::Path;

use crate::ast;
use crate::error::CompileError;
use crate::source::SourceArena;
use crate::stdlib;
use crate::syntax::parse;
use crate::syntax::raw::{Decl, Module};

/// Tracks which imported types need module qualification.
pub struct ModuleScope {
    /// type name -> module name, for types that need `module.Type` qualification
    pub qualified_types: HashMap<String, String>,
    /// free function name -> module name, for functions that need `module.func` qualification
    pub qualified_funcs: HashMap<String, String>,
    /// Types brought into bare scope via `exposing`
    pub exposed_types: HashSet<String>,
    /// Free functions brought into bare scope via `exposing`
    pub exposed_funcs: HashSet<String>,
}

impl ModuleScope {
    fn new() -> Self {
        Self {
            qualified_types: HashMap::new(),
            qualified_funcs: HashMap::new(),
            exposed_types: HashSet::new(),
            exposed_funcs: HashSet::new(),
        }
    }
}

/// Resolved module.
///
/// `module` is in the elaborated `ast::Module` form, converted from
/// the raw parser output at the end of [`resolve_imports`] so that
/// downstream passes never see the raw shape. `symbols` carries the
/// `SymbolTable` allocated during conversion — passes that need to
/// recover display names from `SymbolId`s look them up here.
pub struct Resolved<'src> {
    pub module: ast::Module<'src>,
    pub scope: ModuleScope,
    pub symbols: crate::symbol::SymbolTable,
    pub fields: crate::symbol::FieldInterner,
}

/// Resolve imports by prepending imported declarations to the module.
/// Checks stdlib first, then looks for `.ori` files relative to `source_dir`.
#[expect(clippy::too_many_lines, reason = "import resolution with validation")]
pub fn resolve_imports<'src>(
    module: Module<'src>,
    arena: &mut SourceArena,
    source_dir: Option<&Path>,
) -> Result<Resolved<'src>, CompileError> {
    let mut scope = ModuleScope::new();
    let mut all_decls: Vec<Decl<'src>> = Vec::new();

    // Auto-import all stdlib modules so they're always available.
    for name in stdlib::MODULES {
        let src = stdlib::get(name).unwrap();
        let file_id = arena.add(format!("<stdlib:{name}>"), src.to_owned());
        let imported = parse::parse(arena.content(file_id), file_id)?;
        let exported: Vec<Decl<'_>> = imported
            .decls
            .into_iter()
            .filter(|d| {
                let n = match d {
                    Decl::TypeAnno { name, .. } | Decl::FuncDef { name, .. } => *name,
                };
                imported.exports.contains(&n)
            })
            .collect();
        all_decls.extend(exported);
    }

    for import in &module.imports {
        // Try stdlib first, then file system
        let imported = if let Some(stdlib_src) = stdlib::get(import.module) {
            let file_id = arena.add(format!("<stdlib:{}>", import.module), stdlib_src.to_owned());
            parse::parse(arena.content(file_id), file_id)?
        } else if let Some(dir) = source_dir {
            // Try name.ori relative to the source file's directory
            let path = dir.join(format!("{}.ori", import.module));
            let content = std::fs::read_to_string(&path).map_err(|e| {
                CompileError::new(format!("cannot import '{}': {e}", import.module))
            })?;
            let file_id = arena.add(path.display().to_string(), content);
            parse::parse(arena.content(file_id), file_id)?
        } else {
            return Err(CompileError::new(format!(
                "unknown module: {}",
                import.module
            )));
        };

        // Check for body-less method declarations in user modules
        let is_stdlib = stdlib::get(import.module).is_some();
        if !is_stdlib {
            for decl in &imported.decls {
                if let Decl::TypeAnno { methods, name, .. } = decl {
                    let func_names: std::collections::HashSet<&str> = methods
                        .iter()
                        .filter_map(|m| {
                            if let Decl::FuncDef { name, .. } = m {
                                Some(*name)
                            } else {
                                None
                            }
                        })
                        .collect();
                    for method in methods {
                        if let Decl::TypeAnno {
                            span,
                            name: method_name,
                            ..
                        } = method
                            && !func_names.contains(method_name)
                        {
                            return Err(CompileError::at(
                                *span,
                                format!("method '{name}.{method_name}' declared but not defined"),
                            ));
                        }
                    }
                }
            }
        }

        // No exports = fully private (nothing importable)
        if imported.exports.is_empty() {
            return Err(CompileError::new(format!(
                "module '{}' has no exports",
                import.module
            )));
        }

        // Include exported decls plus any non-exported decls they
        // transitively depend on. Internal helpers like `chr` need
        // to be compiled but shouldn't be visible to the consumer.
        let export_set: HashSet<&str> = imported.exports.iter().copied().collect();
        let reachable = reachable_decls(&imported.decls, &export_set);
        let included_decls: Vec<Decl<'_>> = imported
            .decls
            .into_iter()
            .filter(|decl| {
                let name = match decl {
                    Decl::TypeAnno { name, .. } | Decl::FuncDef { name, .. } => *name,
                };
                reachable.contains(name)
            })
            .collect();

        // Only register exported names in scope — transitive deps
        // are included for compilation but not importable.
        let is_qualified = import.module.starts_with(|c: char| c.is_ascii_lowercase());

        if is_qualified {
            for decl in &included_decls {
                let name = match decl {
                    Decl::TypeAnno { name, .. } | Decl::FuncDef { name, .. } => *name,
                };
                if !export_set.contains(name) {
                    continue;
                }
                match decl {
                    Decl::TypeAnno { .. } => {
                        if import.exposing.contains(&name) {
                            scope.exposed_types.insert(name.to_owned());
                        } else {
                            scope
                                .qualified_types
                                .insert(name.to_owned(), import.module.to_owned());
                        }
                    }
                    Decl::FuncDef { .. } => {
                        if import.exposing.contains(&name) {
                            scope.exposed_funcs.insert(name.to_owned());
                        } else {
                            scope
                                .qualified_funcs
                                .insert(name.to_owned(), import.module.to_owned());
                        }
                    }
                }
            }
        }

        all_decls.extend(included_decls);
    }
    all_decls.extend(module.decls);

    let resolved = Module {
        exports: vec![],
        imports: vec![],
        decls: all_decls,
    };
    let mut symbols = crate::symbol::SymbolTable::new();
    let mut fields = crate::symbol::FieldInterner::new();
    let module = ast::from_raw(resolved, &mut symbols, &mut fields);
    Ok(Resolved {
        module,
        scope,
        symbols,
        fields,
    })
}

// ---- Transitive dependency computation for imports ----

use crate::syntax::raw::{Expr, ExprKind, ListPatternElem, Pattern, Stmt};

/// Compute the set of declaration names reachable from `roots` via
/// references in function bodies. Returns all names that need to be
/// included for the exported declarations to compile.
fn reachable_decls(decls: &[Decl<'_>], roots: &HashSet<&str>) -> HashSet<String> {
    // Build name → references map
    let mut refs_map: HashMap<&str, HashSet<&str>> = HashMap::new();
    let decl_names: HashSet<&str> = decls
        .iter()
        .map(|d| match d {
            Decl::TypeAnno { name, .. } | Decl::FuncDef { name, .. } => *name,
        })
        .collect();

    for decl in decls {
        match decl {
            Decl::FuncDef { name, body, .. } => {
                let mut names = HashSet::new();
                collect_raw_refs(body, &mut names);
                // Only keep references to other decls in this module
                names.retain(|n| decl_names.contains(n));
                refs_map.insert(name, names);
            }
            Decl::TypeAnno { name, methods, .. } => {
                let mut names = HashSet::new();
                for method in methods {
                    if let Decl::FuncDef { body, .. } = method {
                        collect_raw_refs(body, &mut names);
                    }
                }
                names.retain(|n| decl_names.contains(n));
                refs_map.insert(name, names);
            }
        }
    }

    // BFS from roots
    let mut reachable: HashSet<String> = roots.iter().map(|s| (*s).to_owned()).collect();
    let mut worklist: Vec<&str> = roots.iter().copied().collect();
    while let Some(name) = worklist.pop() {
        if let Some(deps) = refs_map.get(name) {
            #[expect(clippy::iter_over_hash_type, reason = "reachability order doesn't matter")]
            for dep in deps {
                if reachable.insert((*dep).to_owned()) {
                    worklist.push(dep);
                }
            }
        }
    }
    reachable
}

/// Collect all name references from a raw expression tree.
fn collect_raw_refs<'src>(expr: &Expr<'src>, out: &mut HashSet<&'src str>) {
    match &expr.kind {
        ExprKind::Name(n) => {
            out.insert(n);
        }
        ExprKind::Call { func, args } => {
            out.insert(func);
            for a in args {
                collect_raw_refs(a, out);
            }
        }
        ExprKind::QualifiedCall { segments, args } => {
            if let Some(&last) = segments.last() {
                out.insert(last);
            }
            for a in args {
                collect_raw_refs(a, out);
            }
        }
        ExprKind::MethodCall {
            receiver, args, ..
        } => {
            collect_raw_refs(receiver, out);
            for a in args {
                collect_raw_refs(a, out);
            }
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            collect_raw_refs(lhs, out);
            collect_raw_refs(rhs, out);
        }
        ExprKind::Block(stmts, result) => {
            for s in stmts {
                collect_raw_refs_stmt(s, out);
            }
            collect_raw_refs(result, out);
        }
        ExprKind::If {
            expr,
            arms,
            else_body,
        } => {
            collect_raw_refs(expr, out);
            for arm in arms {
                collect_raw_refs_arm(arm, out);
            }
            if let Some(eb) = else_body {
                collect_raw_refs(eb, out);
            }
        }
        ExprKind::Fold { expr, arms } => {
            collect_raw_refs(expr, out);
            for arm in arms {
                collect_raw_refs_arm(arm, out);
            }
        }
        ExprKind::Lambda { body, .. } => collect_raw_refs(body, out),
        ExprKind::Record { fields } => {
            for (_, e) in fields {
                collect_raw_refs(e, out);
            }
        }
        ExprKind::RecordUpdate { base, updates } => {
            collect_raw_refs(base, out);
            for (_, e) in updates {
                collect_raw_refs(e, out);
            }
        }
        ExprKind::FieldAccess { record, .. } => collect_raw_refs(record, out),
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems {
                collect_raw_refs(e, out);
            }
        }
        ExprKind::Is { expr, pattern } => {
            collect_raw_refs(expr, out);
            collect_raw_refs_pattern(pattern, out);
        }
        ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) => {}
    }
}

fn collect_raw_refs_arm<'src>(
    arm: &crate::syntax::raw::MatchArm<'src>,
    out: &mut HashSet<&'src str>,
) {
    collect_raw_refs_pattern(&arm.pattern, out);
    for g in &arm.guards {
        collect_raw_refs(g, out);
    }
    collect_raw_refs(&arm.body, out);
}

fn collect_raw_refs_stmt<'src>(stmt: &Stmt<'src>, out: &mut HashSet<&'src str>) {
    match stmt {
        Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => collect_raw_refs(val, out),
        Stmt::Guard {
            condition,
            return_val,
        } => {
            collect_raw_refs(condition, out);
            collect_raw_refs(return_val, out);
        }
        Stmt::TypeHint { .. } => {}
    }
}

fn collect_raw_refs_pattern<'src>(pat: &Pattern<'src>, out: &mut HashSet<&'src str>) {
    match pat {
        Pattern::Constructor { name, fields } => {
            out.insert(name);
            for f in fields {
                collect_raw_refs_pattern(f, out);
            }
        }
        Pattern::Record { fields, .. } => {
            for (_, p) in fields {
                collect_raw_refs_pattern(p, out);
            }
        }
        Pattern::Tuple(elems) => {
            for p in elems {
                collect_raw_refs_pattern(p, out);
            }
        }
        Pattern::List(elems) => {
            for elem in elems {
                if let ListPatternElem::Pattern(p) = elem {
                    collect_raw_refs_pattern(p, out);
                }
            }
        }
        Pattern::Binding(_) | Pattern::Wildcard | Pattern::IntLit(_) | Pattern::StrLit(_) => {}
    }
}
