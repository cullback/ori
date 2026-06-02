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
pub mod const_term_fold;
pub mod dce;
pub mod inline;
pub mod jump_threading;
pub mod merge_blocks;
pub mod nop_elim;
pub mod operands;
pub mod rc_fuse;
pub mod retype_statics;
pub mod static_promote;
pub mod stream_fuse;

use crate::ssa::Module;
use crate::ssa::validate::check;

// Re-exports for backward compatibility with passes that imported
// these from `crate::opt::*` directly.
pub use operands::{rewrite_operands, rewrite_terminator_operands};

/// Run the standard local-optimization sequence over every function
/// in `module`. Each sub-pass is self-sufficient — no fixpoint
/// looping; the order is deliberately chosen.
pub fn optimize(module: &mut Module) {
    for func in module.functions.values_mut() {
        const_fold::run(func);
        const_term_fold::run(func);
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
/// the binary and the test harness can't drift apart. `check` runs
/// after every pass to surface invariant violations at the boundary
/// they were introduced.
pub fn run_full_pipeline(module: &mut Module) {
    static_promote::promote(module);
    check(module, "static_promote");
    optimize(module);
    check(module, "optimize (post static_promote)");
    // inline() re-runs ssa_form internally so it leaves the
    // explicit-block-params invariant intact.
    inline::inline(module);
    check(module, "inline");
    optimize(module);
    check(module, "optimize (post inline)");
    const_eval::evaluate(module);
    check(module, "const_eval");
    optimize(module);
    check(module, "optimize (post const_eval)");
    // const_eval may produce more StaticRefs; retype them and drop
    // the rc ops that rc_emit had emitted while their operand was
    // still RcPtr. retype_statics does both as a single step so the
    // "no rc op on a Ptr-typed Value" invariant holds atomically
    // and the validator can enforce it from this boundary on.
    retype_statics::run(module);
    check(module, "retype_statics");
    rc_fuse::run(module);
    check(module, "rc_fuse");
    optimize(module);
    check(module, "optimize (final)");
}
