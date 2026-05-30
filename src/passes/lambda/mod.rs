//! Lambda compilation: four sub-passes that together defunctionalize
//! the program — every `Lambda`/`Closure` AST node is gone after
//! this folder's passes run, and every call has a known first-order
//! target. See `notes/lambda-set-specialization.md` for the
//! language-level model, runtime semantics, and rationale.
//!
//! Sub-pass order:
//!
//! - `lift`       — `Lambda` → top-level `FuncDef` + `Closure` value.
//! - `solve`      — 0-CFA flow analysis. Outputs a `LambdaSolution`.
//! - `specialize` — `Closure` → tag constructor, HO call → `__apply_K`
//!                  dispatcher (or inline singleton match).
//! - `narrow`     — per-call-site clones of user HOFs so each call
//!                  site's lambda set is singleton (Phase E fires).

pub mod lift;
pub mod narrow;
pub mod solve;
pub mod specialize;

// `SingletonTarget` is the only cross-folder shared type — re-exported
// here so `crate::passes::lambda::SingletonTarget` works for
// downstream `lower/` and `mono` callers without depending on which
// sub-pass defines it.
pub use specialize::SingletonTarget;
