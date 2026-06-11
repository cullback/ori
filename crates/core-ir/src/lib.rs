//! Ori Core IR — v1 prototype.
//!
//! Implements the spec from `notes/core-ir.md`. The crate is a
//! sandbox for testing IR design choices in isolation: no AST→Core,
//! no main-crate front-end machinery, just the IR types + a
//! builder + a validator + hand-built tests.
//!
//! See `RATIONALE.md` for the variant-selection argument.

pub mod builder;
pub mod expr;
pub mod literal;
pub mod pattern;
pub mod sym;
pub mod ty;
pub mod validate;

pub use builder::Builder;
pub use expr::{Expr, FoldKind, FoldShape, MatchArm};
pub use literal::{Literal, StrLit};
pub use pattern::{Binder, Pattern};
pub use sym::{ClosureTagId, DeclTagId, FnId, LocalId, TagId, TypeId};
pub use ty::{CoreType, Scalar};
pub use validate::{validate_call_graph, validate_scope, ValidationError};
