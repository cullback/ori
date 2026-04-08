use std::collections::{HashMap, HashSet};
use std::path::Path;

use crate::error::CompileError;
use crate::source::SourceArena;
use crate::stdlib;
use crate::syntax::ast::{Decl, Module};
use crate::syntax::parse;

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
pub struct Resolved<'src> {
    pub module: Module<'src>,
    pub scope: ModuleScope,
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

        // Filter by exports: only include exported declarations
        // No exports = fully private (nothing importable)
        let exported_decls: Vec<Decl<'_>> = if imported.exports.is_empty() {
            return Err(CompileError::new(format!(
                "module '{}' has no exports",
                import.module
            )));
        } else {
            imported
                .decls
                .into_iter()
                .filter(|decl| {
                    let name = match decl {
                        Decl::TypeAnno { name, .. } | Decl::FuncDef { name, .. } => *name,
                    };
                    imported.exports.contains(&name)
                })
                .collect()
        };

        // Lowercase module name -> qualified access; uppercase -> legacy flat merge
        let is_qualified = import.module.starts_with(|c: char| c.is_ascii_lowercase());

        if is_qualified {
            for decl in &exported_decls {
                match decl {
                    Decl::TypeAnno { name, .. } => {
                        if import.exposing.contains(name) {
                            scope.exposed_types.insert((*name).to_owned());
                        } else {
                            scope
                                .qualified_types
                                .insert((*name).to_owned(), import.module.to_owned());
                        }
                    }
                    Decl::FuncDef { name, .. } => {
                        if import.exposing.contains(name) {
                            scope.exposed_funcs.insert((*name).to_owned());
                        } else {
                            scope
                                .qualified_funcs
                                .insert((*name).to_owned(), import.module.to_owned());
                        }
                    }
                }
            }
        }

        all_decls.extend(exported_decls);
    }
    all_decls.extend(module.decls);

    let resolved = Module {
        exports: vec![],
        imports: vec![],
        decls: all_decls,
    };
    Ok(Resolved {
        module: resolved,
        scope,
    })
}
