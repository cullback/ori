//! Identifiers — `SymbolId` for callables/bindings, `TagId` for
//! constructor tags.
//!
//! Both are deliberately opaque newtypes. The v1 prototype doesn't
//! reuse the main `ori` crate's `SymbolTable` — keeping these
//! local makes the IR testable in isolation and forces us to think
//! about what Core actually needs from an identifier.

/// Stable identifier for a top-level definition or a local binding.
///
/// In the full pipeline, this maps 1:1 to the AST's `SymbolId`.
/// Here it's just an opaque integer; the test harness allocates them.
///
/// **Open question:** in the existing implementation, `Var.sym` and
/// `App.target` are the *same* `SymbolId` type — a top-level function
/// and a local binding aren't distinguished syntactically. Should we
/// split them? `Var(LocalId)` vs `App(FuncId)` would catch the
/// "called a local variable like a function" mistake at the type
/// level. Cost: every traversal has to handle two kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SymbolId(pub u32);

/// Constructor tag — the source name of the variant (`"Cons"`,
/// `"Ok"`, `"True"`).
///
/// Tag unions are structural in Ori — the tag name identifies the
/// variant within its union. Strings are the natural representation;
/// could be interned later if profiling shows it matters.
///
/// **Open question:** should this be a `SymbolId` too? Constructors
/// are top-level declarations in the symbol table. Using `String`
/// here means rewrites that match on `tag == "Cons"` work without a
/// symbol-table lookup, but the redundancy with the symbol table is
/// a smell.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TagId(pub String);

impl TagId {
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }

    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}
