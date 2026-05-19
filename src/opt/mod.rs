//! SSA optimization passes.
//!
//! Each pass lives in its own file, identified by the single kind of
//! redundancy it removes. The `optimize` entry point composes them in
//! a deliberate sequence. Per the architecture: every pass is
//! optional — disabling all of `opt::*` produces a correct, leak-free,
//! slow program.

pub mod branch_fold;
pub mod const_eval;
pub mod const_fold;
pub mod dce;
pub mod inline;
pub mod jump_threading;
pub mod merge_blocks;
pub mod nop_elim;
pub mod operands;
pub mod ownership;
pub mod rc;
pub mod sig_borrow;
pub mod sig_layouts;
pub mod static_promote;

use crate::ssa::Module;

// Re-exports for backward compatibility with passes that imported
// these from `crate::opt::*` directly.
pub use operands::{rewrite_operands, rewrite_terminator_operands};

/// Run the standard local-optimization sequence over every function
/// in `module`. Each sub-pass is self-sufficient — no fixpoint
/// looping; the order is deliberately chosen.
pub fn optimize(module: &mut Module) {
    for func in module.functions.values_mut() {
        const_fold::run(func);
        nop_elim::run(func);
        jump_threading::run(func);
        branch_fold::run(func);
        jump_threading::run(func);
        branch_fold::run(func);
        merge_blocks::run(func);
        dce::run(func);
    }
    dce::dead_functions(module);
}
