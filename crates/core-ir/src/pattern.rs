//! Patterns — three shallow shapes.
//!
//! Per the spec, literal patterns (`IntLit`, `StrLit`) are
//! desugared at AST→Core into `Binding(fresh)` + a synthesized
//! `Eq(fresh, lit)` guard at the head of the arm. Nested patterns
//! are flattened upstream by `flatten_patterns`. Three shapes
//! cover everything Core needs.

use crate::sym::{SymbolId, TagId};

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    /// `Cons(x, xs)` — a tag-union constructor with field binders.
    ///
    /// `binders` is `Vec<Vec<SymbolId>>`:
    /// - Outer Vec: one entry per source-level field.
    /// - Inner Vec: the slot symbols that field expands to (1 for
    ///   single-slot scalar fields, N for multi-slot record/tuple/
    ///   trio fields).
    ///
    /// A wildcard binder has its `SymbolId` set to a sentinel value
    /// (the existing impl uses `SymbolId(u32::MAX)`).
    ///
    /// **Open question:** the sentinel-wildcard convention is a
    /// classic "make-illegal-states-representable" smell — an enum
    /// `Binder { Sym(SymbolId), Wildcard }` would catch the
    /// "compared a sentinel value against a real id" bug at the type
    /// level. Cost: every binder access is `match`.
    Constructor {
        tag: TagId,
        binders: Vec<Vec<SymbolId>>,
    },

    /// `_` — match anything, bind nothing.
    Wildcard,

    /// `x` (bare name) — match anything, bind to `x`.
    Binding(SymbolId),
}
