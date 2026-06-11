//! Scalar literals. No `Str` — string literals are `BufLit` of
//! byte-`Int`s.
//!
//! `Int(i64)` represents both signed and unsigned integers; the
//! Core node's `ty` distinguishes width and signedness.

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Literal {
    Int(i64),
    Float(f64),
}

/// A static string literal — `Crash`'s message is one of these.
/// Stored separately from `Literal` because crashes never compose
/// recursively; the message is a leaf.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StrLit(pub Vec<u8>);

impl StrLit {
    #[must_use]
    pub fn new(s: impl Into<String>) -> Self {
        Self(s.into().into_bytes())
    }

    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}
