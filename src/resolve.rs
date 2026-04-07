use std::collections::{HashMap, HashSet};
use std::path::Path;

use crate::error::CompileError;
use crate::stdlib;
use crate::syntax::ast::{Decl, Module};
use crate::syntax::parse;

/// Tracks which imported types need module qualification.
pub struct ModuleScope {
    /// type name → module name, for types that need `module.Type` qualification
    pub qualified_types: HashMap<String, String>,
    /// free function name → module name, for functions that need `module.func` qualification
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

/// Resolved module with owned sources for file-based imports.
/// The `sources` field keeps file contents alive so the module can borrow from them.
pub struct Resolved<'src> {
    pub module: Module<'src>,
    pub scope: ModuleScope,
    /// Owned file contents for file-based imports (must outlive `module`).
    pub _sources: Vec<String>,
}

/// Resolve imports by prepending imported declarations to the module.
/// Checks stdlib first, then looks for `.ori` files relative to `source_dir`.
pub fn resolve_imports<'src>(
    module: Module<'src>,
    source_dir: Option<&Path>,
) -> Result<Resolved<'src>, CompileError> {
    let mut scope = ModuleScope::new();

    if module.imports.is_empty() {
        return Ok(Resolved {
            module,
            scope,
            _sources: vec![],
        });
    }

    let mut sources: Vec<String> = Vec::new();
    let mut all_decls: Vec<Decl<'src>> = Vec::new();

    for import in &module.imports {
        // Try stdlib first, then file system
        let imported = if let Some(stdlib_src) = stdlib::get(import.module) {
            parse::parse(stdlib_src)?
        } else if let Some(dir) = source_dir {
            // Try name.ori relative to the source file's directory
            let path = dir.join(format!("{}.ori", import.module));
            let content = std::fs::read_to_string(&path).map_err(|e| {
                CompileError::new(format!("cannot import '{}': {e}", import.module))
            })?;
            sources.push(content);
            // SAFETY: the source string lives in `sources` which is returned alongside
            // the module, so the borrow is valid for the lifetime of Resolved.
            let src_ref: &str =
                unsafe { &*std::ptr::from_ref::<str>(sources.last().unwrap().as_str()) };
            parse::parse(src_ref)?
        } else {
            return Err(CompileError::new(format!(
                "unknown module: {}",
                import.module
            )));
        };

        // Filter by exports: only include exported declarations
        let exported_decls: Vec<Decl<'_>> = if imported.exports.is_empty() {
            // No exports declaration: everything is public
            imported.decls
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

        // Lowercase module name → qualified access; uppercase → legacy flat merge
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
        _sources: sources,
    })
}
