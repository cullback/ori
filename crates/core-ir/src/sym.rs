//! Identifiers — distinct types for distinct concepts.
//!
//! The spec calls out that `Var.sym` (a local binding) and
//! `App.target` (a top-level callable) are semantically different;
//! splitting them at the type level catches "called a local
//! variable like a function" at compile time.

/// A local binding: function parameter, `Let` binder, or pattern
/// binder. The integer is just an allocation tag — we don't reuse
/// the main `ori` crate's `SymbolTable` here, the test harness
/// allocates fresh `LocalId`s.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalId(pub u32);

/// A top-level callable: user function, lifted lambda, builtin,
/// or stdlib. Resolved through a function table at lowering.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FnId(pub u32);

/// A user-declared tag-union constructor (`Cons`, `Nil`, `Ok`,
/// `Err`, ...).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DeclTagId(pub u32);

/// A synthesized closure constructor (`__lambda_K`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ClosureTagId(pub u32);

/// Tag-union tag. Kinded so closure tags and declared tags can't
/// be conflated structurally.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TagId {
    Declared(DeclTagId),
    Closure(ClosureTagId),
}

/// A user-declared type constructor (`List`, `Result`, `MyUnion`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeId(pub u32);
