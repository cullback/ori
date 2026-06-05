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
    /// Tag-union constructor. Created both for constructors explicitly
    /// declared via `TypeAnno`'s `[Tag1, Tag2, ...]` form and for
    /// structural constructors discovered by the pre-resolver walk
    /// (uppercase names used in expressions or patterns that weren't
    /// declared anywhere). Inference treats declared and structural
    /// constructors differently: declared ones instantiate a stored
    /// `Scheme`, while structural ones produce an open `Type::TagUnion`
    /// with a single tag.
    Constructor,
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
///
/// `by_display` is a reverse index, populated lazily as symbols are
/// minted via [`SymbolTable::fresh`]. It supports [`SymbolTable::intern`]
/// — Core lowering's lookup-or-create semantics for callable targets
/// that arrive as mangled strings (mono-specialized funcs, synthesized
/// helpers like `__crash`, `__builtin.*` intrinsics). If two symbols
/// happen to share a display name (defensive — callers normally mangle
/// to ensure uniqueness), `by_display` points at the most-recently-minted
/// one. The reverse index is not used for symbol identity comparisons —
/// those still go through `SymbolId`.
#[derive(Debug, Default)]
pub struct SymbolTable {
    entries: Vec<SymbolInfo>,
    by_display: HashMap<String, SymbolId>,
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
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            by_display: HashMap::new(),
        }
    }

    /// Allocate a fresh `SymbolId` for a definition with the given
    /// display name, source span, and kind. The returned `SymbolId`
    /// never changes once issued.
    #[allow(clippy::impl_trait_in_params)]
    pub fn fresh(&mut self, display: impl Into<String>, span: Span, kind: SymbolKind) -> SymbolId {
        let id = u32::try_from(self.entries.len()).expect("too many symbols");
        let display = display.into();
        self.by_display.insert(display.clone(), SymbolId(id));
        self.entries.push(SymbolInfo {
            display,
            span,
            kind,
        });
        SymbolId(id)
    }

    /// Look up a `SymbolId` by display name, or allocate a fresh one
    /// if no symbol with that name has been minted yet. The fresh
    /// entry uses the provided `span` and `kind` — callers should
    /// supply something meaningful (e.g. the call-site span) since
    /// later passes inspect them.
    ///
    /// Used by Core lowering to bridge string-keyed call targets
    /// (`QualifiedCall.resolved`, `MethodCall.resolved`, synthesized
    /// `__crash` etc.) into the `SymbolId`-typed `Expr::App.target`.
    #[allow(clippy::impl_trait_in_params)]
    pub fn intern(&mut self, display: impl AsRef<str>, span: Span, kind: SymbolKind) -> SymbolId {
        let display = display.as_ref();
        if let Some(&sym) = self.by_display.get(display) {
            return sym;
        }
        self.fresh(display.to_owned(), span, kind)
    }

    #[allow(
        dead_code,
        reason = "consumed by later steps that need symbol metadata"
    )]
    pub fn get(&self, id: SymbolId) -> &SymbolInfo {
        &self.entries[id.0 as usize]
    }

    /// Like `get`, but returns None for SymbolIds that haven't been
    /// allocated. Useful when a value may carry a SymbolId from a
    /// different table (or a hand-allocated one in unit tests) and
    /// we'd rather skip the lookup than panic.
    pub fn try_get(&self, id: SymbolId) -> Option<&SymbolInfo> {
        self.entries.get(id.0 as usize)
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

/// Stable `SymbolId`s for compiler-internal primitive operations
/// (arithmetic, comparison, bitwise, casts, list anamorphism). The
/// Core IR represents every primitive as `Expr::App { target: <one
/// of these>, args, ty }` so the "no special variants for primitive
/// ops" property holds: primitives are bodyless `App`s, recognized
/// at Core→SSA via this registry, and dispatched to the right
/// `Inst` (Binary / Cast / inline counter-loop / ...).
///
/// Bootstrap once at the top of the compilation pipeline via
/// [`BuiltinRegistry::bootstrap`]; the resulting `SymbolId`s are
/// then threaded into `LowerCtx` (so AST→Core can stamp them on
/// constructions) and the `to_ssa` `Ctx` (so the dispatch knows
/// which `App` is which builtin).
#[derive(Debug, Clone, Copy)]
pub struct BuiltinRegistry {
    pub add: SymbolId,
    pub sub: SymbolId,
    pub mul: SymbolId,
    pub div: SymbolId,
    pub rem: SymbolId,
    pub eq: SymbolId,
    pub neq: SymbolId,
    pub lt: SymbolId,
    pub gt: SymbolId,
    pub le: SymbolId,
    pub ge: SymbolId,
    pub bit_and: SymbolId,
    pub bit_or: SymbolId,
    pub bit_xor: SymbolId,
    pub shl: SymbolId,
    pub shr: SymbolId,
    /// Regular numeric cast (zero/sign extend or truncate).
    pub cast: SymbolId,
    /// `to_bits` / `from_bits` — same bit pattern, different type.
    pub bitcast: SymbolId,
    /// `List.range(start, end)` — anamorphism producing `[start,
    /// start+1, ..., end-1]`. Element type comes from the `App.ty`
    /// at lower time.
    pub range: SymbolId,
}

impl BuiltinRegistry {
    /// Allocate `SymbolId`s for every primitive. Display names follow
    /// the existing `__builtin.*` convention (so `SymbolTable::display`
    /// renders something sensible in dumps and error messages); the
    /// `SymbolKind::Func` carries the "this names a callable" semantics
    /// even though there's no SSA function with the name — the
    /// `to_ssa` dispatch intercepts before the `Inst::Call` would
    /// otherwise refer to it.
    pub fn bootstrap(symbols: &mut SymbolTable) -> Self {
        let span = Span::default();
        let mut mk = |display: &str| symbols.intern(display, span, SymbolKind::Func);
        Self {
            add: mk("__builtin.add"),
            sub: mk("__builtin.sub"),
            mul: mk("__builtin.mul"),
            div: mk("__builtin.div"),
            rem: mk("__builtin.rem"),
            eq: mk("__builtin.eq"),
            neq: mk("__builtin.neq"),
            lt: mk("__builtin.lt"),
            gt: mk("__builtin.gt"),
            le: mk("__builtin.le"),
            ge: mk("__builtin.ge"),
            bit_and: mk("__builtin.bit_and"),
            bit_or: mk("__builtin.bit_or"),
            bit_xor: mk("__builtin.bit_xor"),
            shl: mk("__builtin.shl"),
            shr: mk("__builtin.shr"),
            cast: mk("__builtin.cast"),
            bitcast: mk("__builtin.bitcast"),
            range: mk("__builtin.list.range"),
        }
    }

    /// Map a `SymbolId` to the builtin it represents, if any. Used
    /// by `to_ssa`'s `App` handler to decide whether to dispatch
    /// (inline op emission) or call (regular function).
    pub fn classify(&self, sym: SymbolId) -> Option<BuiltinKind> {
        use crate::ssa::BinaryOp;
        if sym == self.add { return Some(BuiltinKind::Binary(BinaryOp::Add)); }
        if sym == self.sub { return Some(BuiltinKind::Binary(BinaryOp::Sub)); }
        if sym == self.mul { return Some(BuiltinKind::Binary(BinaryOp::Mul)); }
        if sym == self.div { return Some(BuiltinKind::Binary(BinaryOp::Div)); }
        if sym == self.rem { return Some(BuiltinKind::Binary(BinaryOp::Rem)); }
        if sym == self.eq { return Some(BuiltinKind::Binary(BinaryOp::Eq)); }
        if sym == self.neq { return Some(BuiltinKind::Binary(BinaryOp::Neq)); }
        if sym == self.lt { return Some(BuiltinKind::Binary(BinaryOp::Lt)); }
        if sym == self.gt { return Some(BuiltinKind::Binary(BinaryOp::Gt)); }
        if sym == self.le { return Some(BuiltinKind::Binary(BinaryOp::Le)); }
        if sym == self.ge { return Some(BuiltinKind::Binary(BinaryOp::Ge)); }
        if sym == self.bit_and { return Some(BuiltinKind::Binary(BinaryOp::And)); }
        if sym == self.bit_or { return Some(BuiltinKind::Binary(BinaryOp::Or)); }
        if sym == self.bit_xor { return Some(BuiltinKind::Binary(BinaryOp::Xor)); }
        if sym == self.shl { return Some(BuiltinKind::Binary(BinaryOp::Shl)); }
        if sym == self.shr { return Some(BuiltinKind::Binary(BinaryOp::Shr)); }
        if sym == self.cast { return Some(BuiltinKind::Cast); }
        if sym == self.bitcast { return Some(BuiltinKind::Bitcast); }
        if sym == self.range { return Some(BuiltinKind::Range); }
        None
    }
}

/// What a builtin `SymbolId` represents at to_ssa dispatch time.
#[derive(Debug, Clone, Copy)]
pub enum BuiltinKind {
    /// Two-argument scalar op: `Inst::Binary(op, ...)`.
    Binary(crate::ssa::BinaryOp),
    /// One-argument numeric conversion, zero/sign-extend or truncate.
    /// Destination scalar type is read from `App.ty`.
    Cast,
    /// One-argument bit-pattern reinterpretation. Destination scalar
    /// type from `App.ty`.
    Bitcast,
    /// `range(start, end)` → buffer trio. Element scalar type from
    /// `App.ty` (which is `List(T)`).
    Range,
}
