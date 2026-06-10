//! Ori Core IR — v1 prototype.
//!
//! This crate is a clean-room implementation of the Core IR specified
//! in `notes/core-ir.md`. It exists to:
//!
//! 1. **Validate the spec.** Either the spec describes a buildable,
//!    internally-consistent IR or it doesn't — implementing from
//!    scratch surfaces inconsistencies the existing `src/passes/core/`
//!    can't (it has consumers depending on its current shape).
//! 2. **Test the IR in isolation.** Hand-built Core programs go
//!    through validators and lowering without the full AST→Core
//!    front-end machinery. Today every Core test is end-to-end.
//! 3. **Explore the open design questions** without legacy friction
//!    — polymorphic `Con.ty`, scrutinee as Vec vs. Expr, derived
//!    vs. stored `field_slot_counts`, etc.
//!
//! Scope today: just the IR types. No builder, no display, no
//! validator, no lowering. We need to look at the shape before
//! committing to consumers.

pub mod expr;
pub mod literal;
pub mod pattern;
pub mod sym;
pub mod ty;

pub use expr::{Expr, MatchArm};
pub use literal::Literal;
pub use pattern::Pattern;
pub use sym::{SymbolId, TagId};
pub use ty::Type;
