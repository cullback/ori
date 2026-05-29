//! Lambda compilation: four sub-passes that together defunctionalize
//! the program — every `Lambda`/`Closure` AST node is gone after
//! this folder's passes run, and every call has a known first-order
//! target. See `README.md` for the model, rationale, and motivation.

pub mod lift;
pub mod narrow;
pub mod solve;
pub mod specialize;

// `SingletonTarget` is the only cross-folder shared type — re-exported
// here so `crate::passes::lambda::SingletonTarget` works for
// downstream `lower/` and `mono` callers without depending on which
// sub-pass defines it.
pub use specialize::SingletonTarget;
