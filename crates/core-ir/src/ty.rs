//! Core's type representation.
//!
//! `CoreType` is **distinct from inference's `Type`** — by
//! construction unable to express type variables. The polymorphic-
//! `Con.ty` trap from the previous design is structurally
//! impossible here.

use crate::sym::TypeId;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CoreType {
    Prim(Scalar),
    /// Monomorphic constructed type — `Result(I64, Str)` is
    /// `Adt(Result, [Prim(I64), Adt(List, [Prim(U8)])])`.
    Adt(TypeId, Vec<CoreType>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Scalar {
    Bool,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
}

/// Every `Scalar` is a valid `CoreType` — the conversion lets us
/// write `Scalar::I64` (or just `I64` with `use Scalar::*`) wherever
/// a type is expected.
impl From<Scalar> for CoreType {
    fn from(s: Scalar) -> Self {
        Self::Prim(s)
    }
}
