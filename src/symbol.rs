//! Symbol table for top-level definitions.
//!
//! Step 6a introduces [`SymbolId`] as a stable identifier for top-level
//! declarations (functions, methods, constructors, types) so that:
//!
//! 1. **Rewrites can synthesize names without leaking strings.**
//!    `fold_lift` used to `Box::leak` every `__fold_N` name because the
//!    AST carried borrowed `&'src str`s. With [`SymbolTable`] owning the
//!    string storage, the rewrite passes mint fresh `SymbolId`s and the
//!    display names live in the table for as long as the compilation
//!    unit needs them — no leaks.
//!
//! 2. **Name lookups are cheaper and more deterministic.** Comparing
//!    two `u32`s beats comparing two strings, and hashing a single
//!    integer beats hashing a variable-length key.
//!
//! 3. **Later passes (mono, defunc rewrite) can freely clone and
//!    rename** without worrying about keeping source-slice lifetimes
//!    valid.
//!
//! Scope of this first migration (6a): only `Decl::FuncDef.name`,
//! `Decl::TypeAnno.name`, and `Call`'s callee use `SymbolId`. Local
//! variable references, pattern constructors, method resolutions, and
//! record field names all stay as borrowed strings until 6b/6c.

use std::collections::HashMap;
use std::fmt;

use crate::ast::Span;

/// Stable identifier for a top-level definition. Allocated by
/// [`SymbolTable::fresh`] and valid for the lifetime of the table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SymbolId(pub u32);

impl fmt::Display for SymbolId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

/// What kind of definition a `SymbolId` refers to. Currently consumed
/// only by `ast_display` for readable snapshots, but later passes can
/// use it to short-circuit lookups (e.g. "is this a constructor?").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code, reason = "populated by resolve, consumed by later passes")]
pub enum SymbolKind {
    /// Free-standing function (`foo = |x| ...`).
    Func,
    /// Method inside a `TypeAnno`'s `.()` block.
    Method,
    /// Type declaration (`Foo : ...`, `Foo := ...`, `Foo :: ...`).
    Type,
    /// Local binding: function/lambda parameter, `let`, pattern binding.
    /// Introduced by the name resolver in `ast::from_raw`.
    Local,
}

/// Metadata stored per [`SymbolId`]. The `display` name is owned by the
/// table; call sites reference it via [`SymbolTable::display`]. The
/// `span` points at the source location of the definition (or at the
/// span of the AST node that triggered synthesis, for compiler-minted
/// symbols).
#[derive(Debug, Clone)]
#[allow(dead_code, reason = "fields read by ast_display and later passes")]
pub struct SymbolInfo {
    pub display: String,
    pub span: Span,
    pub kind: SymbolKind,
}

/// Owns the display names for every [`SymbolId`] in the current
/// compilation. Lookup is `O(1)` and the returned `&str` is valid for
/// the lifetime of the table.
#[derive(Debug, Default)]
pub struct SymbolTable {
    entries: Vec<SymbolInfo>,
}

/// Interned identifier for a record field name (`FieldAccess.field`,
/// `Record.fields` keys, `Pattern::Record.fields` keys,
/// `TypeExpr::Record.fields` keys).
///
/// Step 6c: before this, field names were borrowed `&'src str`s from
/// the source arena. Interning them lets later passes compare fields
/// by `u32` equality and store field metadata in `HashMap<FieldSym, _>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FieldSym(pub u32);

impl fmt::Display for FieldSym {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "%{}", self.0)
    }
}

/// Two-way map between field source names and [`FieldSym`]s. Populated
/// during [`crate::ast::from_raw`] — every field name encountered in a
/// record expression, pattern, or type expression gets interned the
/// first time it's seen.
#[derive(Debug, Default)]
pub struct FieldInterner {
    by_name: HashMap<String, FieldSym>,
    names: Vec<String>,
}

impl FieldInterner {
    pub fn new() -> Self {
        Self {
            by_name: HashMap::new(),
            names: Vec::new(),
        }
    }

    /// Intern `name` and return its [`FieldSym`]. Calling `intern` on
    /// the same name twice returns the same `FieldSym`.
    pub fn intern(&mut self, name: &str) -> FieldSym {
        if let Some(&sym) = self.by_name.get(name) {
            return sym;
        }
        let id = u32::try_from(self.names.len()).expect("too many fields");
        let sym = FieldSym(id);
        self.names.push(name.to_owned());
        self.by_name.insert(name.to_owned(), sym);
        sym
    }

    /// Look up the source name for a `FieldSym`.
    pub fn get(&self, sym: FieldSym) -> &str {
        &self.names[sym.0 as usize]
    }
}

impl SymbolTable {
    pub const fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Allocate a fresh `SymbolId` for a definition with the given
    /// display name, source span, and kind. The returned `SymbolId`
    /// never changes once issued.
    #[allow(clippy::impl_trait_in_params)]
    pub fn fresh(&mut self, display: impl Into<String>, span: Span, kind: SymbolKind) -> SymbolId {
        let id = u32::try_from(self.entries.len()).expect("too many symbols");
        self.entries.push(SymbolInfo {
            display: display.into(),
            span,
            kind,
        });
        SymbolId(id)
    }

    #[allow(
        dead_code,
        reason = "consumed by later steps that need symbol metadata"
    )]
    pub fn get(&self, id: SymbolId) -> &SymbolInfo {
        &self.entries[id.0 as usize]
    }

    /// Shortcut for the common case of just needing the rendered name.
    #[allow(
        dead_code,
        reason = "consumed by later steps that need display lookups"
    )]
    pub fn display(&self, id: SymbolId) -> &str {
        &self.get(id).display
    }
}
