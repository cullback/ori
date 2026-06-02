//! Drop `RcInc`/`RcDec` instructions whose operand is `Ptr`-typed.
//!
//! `Ptr`-typed Values are statics in the current model — they carry
//! the sentinel-rc convention in eval (`heap.rc_inc`/`rc_dec` short-
//! circuit on `RC_STATIC`) and they shouldn't participate in any
//! runtime refcounting in codegen.
//!
//! This pass deletes the rc ops outright so no downstream consumer
//! needs to special-case them: eval becomes faster (one fewer
//! dispatch per static reference), and codegen doesn't need to
//! track which Values came from `StaticRef` to skip rc-emit.
//!
//! Must run **after** `retype_statics` — which is what reclassifies
//! static-derived Values from `RcPtr` to `Ptr` in the first place.
//!
//! Pre-conditions: `retype_statics` has run; any Value definitely
//! flowing from a `StaticRef` is `Ptr`-typed.
//! Post-conditions: no `Inst::RcInc(v)` or `Inst::RcDec(v)` where
//! `v.ty == ScalarType::Ptr`.

use crate::ssa::Module;
use crate::ssa::instruction::{Inst, ScalarType};

pub fn run(module: &mut Module) {
    for func in module.functions.values_mut() {
        for block in func.blocks.values_mut() {
            block.insts.retain(|inst| match inst {
                Inst::RcInc(v) | Inst::RcDec(v) => v.ty != ScalarType::Ptr,
                _ => true,
            });
        }
    }
}
