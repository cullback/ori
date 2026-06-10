//! Scalar literals.
//!
//! No `Str` variant — string literals desugar to `BufLit` of byte
//! `Lit::Int`s at AST→Core (`Str ≡ List(U8)`).

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Literal {
    /// Integer literal. The Core node's `ty` distinguishes width
    /// and signedness (`Type::Con("I64")`, `Type::Con("U8")`, …).
    ///
    /// **Open question:** `i64` covers all integer types Ori has,
    /// since the type tells us how to interpret the bits. But the
    /// existing implementation also uses this for `U64` values
    /// which can overflow when cast through `i64`. Should this be
    /// `u64` instead, or do we need separate `IntSigned(i64)` /
    /// `IntUnsigned(u64)` variants? For now: `i64`, with the
    /// understanding that we interpret via the node's `ty`.
    Int(i64),

    /// Floating-point literal.
    Float(f64),
}
