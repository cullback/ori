//! Patterns — three shallow shapes.
//!
//! Literal patterns are desugared at AST→Core. Nested patterns
//! are flattened upstream. Three shapes cover everything Core
//! needs to dispatch.

use crate::sym::{LocalId, TagId};

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    /// `Cons(x, xs)` — a tag-union variant with per-field binders.
    /// One `Binder` per source-level field; nested fields have
    /// been flattened upstream.
    Constructor {
        tag: TagId,
        binders: Vec<Binder>,
    },
    Wildcard,
    Binding(LocalId),
}

/// One field's binder in a `Constructor` pattern.
///
/// `Binder` is an enum — no `u32::MAX` sentinel for wildcards.
/// Wildcards and real binders are structurally distinguishable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Binder {
    Sym(LocalId),
    Wildcard,
}

impl Binder {
    #[must_use]
    pub fn is_wildcard(self) -> bool {
        matches!(self, Self::Wildcard)
    }

    #[must_use]
    pub fn as_sym(self) -> Option<LocalId> {
        match self {
            Self::Sym(s) => Some(s),
            Self::Wildcard => None,
        }
    }
}
