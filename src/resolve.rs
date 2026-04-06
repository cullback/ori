use std::collections::{HashMap, HashSet};

use crate::stdlib;
use crate::syntax::ast::{Decl, Module};
use crate::syntax::parse;

/// Tracks which imported types need module qualification.
pub struct ModuleScope {
    /// type name → module name, for types that need `module.Type` qualification
    pub qualified_types: HashMap<String, String>,
    /// Types brought into bare scope via `exposing`
    pub exposed_types: HashSet<String>,
}

impl ModuleScope {
    fn new() -> Self {
        Self {
            qualified_types: HashMap::new(),
            exposed_types: HashSet::new(),
        }
    }
}

/// Resolve imports by prepending imported declarations to the module.
/// Returns the flattened module and a scope describing how names are qualified.
pub fn resolve_imports(module: Module<'_>) -> (Module<'_>, ModuleScope) {
    let mut scope = ModuleScope::new();

    if module.imports.is_empty() {
        return (module, scope);
    }

    let mut all_decls = Vec::new();
    for import in &module.imports {
        let src = stdlib::get(import.module)
            .unwrap_or_else(|| panic!("unknown module: {}", import.module));
        let imported = parse::parse(src);

        // Lowercase module name → qualified access; uppercase → legacy flat merge
        let is_qualified = import.module.starts_with(|c: char| c.is_ascii_lowercase());

        if is_qualified {
            for decl in &imported.decls {
                if let Decl::TypeAnno { name, .. } = decl {
                    if import.exposing.contains(name) {
                        scope.exposed_types.insert((*name).to_owned());
                    } else {
                        scope
                            .qualified_types
                            .insert((*name).to_owned(), import.module.to_owned());
                    }
                }
            }
        }

        all_decls.extend(imported.decls);
    }
    all_decls.extend(module.decls);

    let resolved = Module {
        imports: vec![],
        decls: all_decls,
    };
    (resolved, scope)
}
