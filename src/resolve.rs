use crate::ast::Module;
use crate::{parse, stdlib};

/// Resolve imports by prepending imported declarations to the module.
/// Stdlib modules are embedded in the binary. Unknown imports panic.
pub fn resolve_imports(module: Module<'_>) -> Module<'_> {
    if module.imports.is_empty() {
        return module;
    }

    let mut all_decls = Vec::new();
    for import_name in &module.imports {
        let src =
            stdlib::get(import_name).unwrap_or_else(|| panic!("unknown module: {import_name}"));
        let imported = parse::parse(src);
        all_decls.extend(imported.decls);
    }
    all_decls.extend(module.decls);

    Module {
        imports: vec![],
        decls: all_decls,
    }
}
