//! Shared utilities for rewriting Value operands across the SSA. Used
//! by inline and any pass that does a global value substitution.

use std::collections::HashMap;

use crate::ssa::instruction::{Inst, Terminator, Value};

pub fn rewrite_operands(inst: &mut Inst, map: &HashMap<Value, Value>) {
    inst.map_operands_mut(|v| {
        if let Some(&r) = map.get(v) {
            *v = r;
        }
    });
}

pub fn rewrite_terminator_operands(term: &mut Terminator, map: &HashMap<Value, Value>) {
    term.map_operands_mut(|v| {
        if let Some(&r) = map.get(v) {
            *v = r;
        }
    });
}
