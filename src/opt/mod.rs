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
pub mod rc_fuse;
pub mod retype_statics;
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

/// Full SSA optimization pipeline. Single canonical entry point so
/// the binary and the test harness can't drift apart. Validation
/// between passes is the caller's responsibility.
pub fn run_full_pipeline(module: &mut Module) {
    static_promote::promote(module);
    optimize(module);
    inline::inline(module);
    // inline may leave cross-block refs; re-run ssa_form to repair.
    crate::lower::ssa_form::run(module);
    optimize(module);
    const_eval::evaluate(module);
    optimize(module);
    // const_eval may produce more StaticRefs; retype them and any
    // values that flow from them. rc_emit's needs_rc_emit then skips
    // these Ptr-typed values automatically — no rc_elide_static needed.
    retype_statics::run(module);
    rc_fuse::run(module);
    optimize(module);
}
