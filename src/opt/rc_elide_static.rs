//! Strip `RcInc` / `RcDec` instructions on values defined by
//! `StaticRef`. Static heap objects carry a sentinel refcount that
//! the runtime ignores, so the rc traffic is a no-op — removing it
//! shrinks code with no behavioral change.

use std::collections::HashSet;

use crate::ssa::Module;
use crate::ssa::instruction::{Inst, Value};

pub fn run(module: &mut Module) {
    for func in module.functions.values_mut() {
        let statics: HashSet<Value> = func
            .blocks
            .values()
            .flat_map(|b| &b.insts)
            .filter_map(|inst| {
                if let Inst::StaticRef(dest, _) = inst {
                    Some(*dest)
                } else {
                    None
                }
            })
            .collect();
        if statics.is_empty() {
            continue;
        }
        for (_, block) in &mut func.blocks {
            block.insts.retain(|inst| {
                !matches!(
                    inst,
                    Inst::RcInc(v) | Inst::RcDec(v) if statics.contains(v)
                )
            });
        }
    }
}
