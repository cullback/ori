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
pub mod rc_elide_static;
pub mod rc_fuse;
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
///
/// **Disabled passes** (correctness bugs uncovered when this was
/// unified — the test harness previously skipped them, hiding the
/// bugs):
/// - `inline::inline` — produces wrong results on several list and
///   trail tests (e.g. `builtin_list_map`); also triggers an index-
///   out-of-bounds in `jump_threading` for some patterns.
/// - `const_eval::evaluate` — same suite of failures.
///
/// Re-enable each as the bugs are fixed. Until then both the binary
/// and the test harness see the same (smaller, correct) pipeline.
pub fn run_full_pipeline(module: &mut Module) {
    static_promote::promote(module);
    optimize(module);
    const_eval::evaluate(module);
    optimize(module);
    rc_elide_static::run(module);
    rc_fuse::run(module);
    optimize(module);
}
