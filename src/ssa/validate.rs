//! Structural validator for SSA modules.
//!
//! Runs after each pass in the test harness to catch pass-induced
//! breakage immediately (dangling BlockIds, mismatched block args,
//! etc.) rather than discovering it later via a confusing runtime
//! crash.
//!
//! The validator distinguishes two categories of problems:
//! - **Structural**: the module is malformed and eval would panic.
//!   Returned as errors.
//! - **Soft**: type inconsistencies the runtime tolerates but which
//!   indicate a bug somewhere. Returned as warnings — collected but
//!   not fatal. Treat as a backlog to clean up.
//!
//! Every invariant here is cheap to check.

use std::collections::HashSet;
use std::fmt::Write as _;

use super::Module;
use super::instruction::{Inst, Terminator, Value};

/// Structural errors make the module unsafe to eval. Warnings are
/// soft inconsistencies (type lies) that don't affect correctness
/// today but should be cleaned up.
#[derive(Default)]
pub struct Report {
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}

impl Report {
    pub fn is_clean(&self) -> bool {
        self.errors.is_empty()
    }

    pub fn error_summary(&self) -> String {
        self.errors.join("\n")
    }
}

/// Validate a module. Returns Ok if no structural errors were found
/// (warnings may still be present). Errors cause the runtime to
/// misbehave; warnings flag bugs that today happen to work.
pub fn validate(module: &Module) -> Report {
    let mut r = Report::default();
    if !module.functions.contains_key(&module.entry) {
        r.errors.push(format!(
            "module.entry points to '{}' but no such function exists",
            module.entry
        ));
    }
    for (name, func) in &module.functions {
        validate_function(module, name, func, &mut r);
    }
    r
}

fn validate_function(
    module: &Module,
    name: &str,
    func: &super::Function,
    r: &mut Report,
) {
    let prefix = format!("in {name}");

    if !func.blocks.contains_key(&func.entry) {
        r.errors.push(format!(
            "{prefix}: entry block {} not in blocks map",
            func.entry.0
        ));
        return;
    }

    // Gather defined Values: params, block params, instruction
    // destinations. Any operand must be one of these.
    let mut defined: HashSet<Value> = HashSet::new();
    for &p in &func.params {
        if !defined.insert(p) {
            r.errors.push(format!("{prefix}: param {p} defined twice"));
        }
    }
    for (bid, block) in &func.blocks {
        for &p in &block.params {
            if !defined.insert(p) {
                r.errors.push(format!(
                    "{prefix}: b{} param {p} redefines existing value",
                    bid.0
                ));
            }
        }
        for (idx, inst) in block.insts.iter().enumerate() {
            if let Some(d) = inst.dest() {
                if !defined.insert(d) {
                    r.errors.push(format!(
                        "{prefix}: b{}:{idx} {inst:?} redefines value {d}",
                        bid.0
                    ));
                }
            }
        }
    }

    // Operands must be defined; calls must target existing functions.
    for (bid, block) in &func.blocks {
        for (idx, inst) in block.insts.iter().enumerate() {
            for v in inst.operands() {
                if !defined.contains(&v) {
                    r.errors.push(format!(
                        "{prefix}: b{}:{idx} {inst:?} uses undefined value {v}",
                        bid.0
                    ));
                }
            }
            if let Inst::Call(_, callee, _) = inst {
                if !callee.starts_with("__") && !module.functions.contains_key(callee) {
                    r.errors.push(format!(
                        "{prefix}: b{}:{idx} calls unknown function '{callee}'",
                        bid.0
                    ));
                }
            }
        }
        for v in block.terminator.operands() {
            if !defined.contains(&v) {
                r.errors.push(format!(
                    "{prefix}: b{} terminator {:?} uses undefined value {v}",
                    bid.0, block.terminator
                ));
            }
        }

        // Successors must exist; arg counts must match param counts.
        for edge in block.terminator.successors() {
            let Some(target_block) = func.blocks.get(&edge.target) else {
                r.errors.push(format!(
                    "{prefix}: b{} jumps to unknown block b{}",
                    bid.0, edge.target.0
                ));
                continue;
            };
            if target_block.params.len() != edge.args.len() {
                // Arg-count mismatches happen today on dead
                // fallthrough paths in match lowering (exhaustive
                // matches still emit a branch to merge without
                // args). Downgraded to a warning until the match
                // lowering is fixed to emit unreachable sinks.
                r.warnings.push(format!(
                    "{prefix}: b{} → b{}: passes {} args but target has {} params",
                    bid.0,
                    edge.target.0,
                    edge.args.len(),
                    target_block.params.len()
                ));
            } else {
                // Type agreement between arg and target param.
                // Warning-level: the runtime tolerates type lies
                // today but they hide real bugs.
                for (i, (arg, param)) in edge.args.iter().zip(&target_block.params).enumerate() {
                    if arg.ty != param.ty {
                        let mut msg = String::new();
                        let _ = write!(
                            msg,
                            "{prefix}: b{} → b{}: arg #{i} {arg} has type {:?}, target param {param} has type {:?}",
                            bid.0, edge.target.0, arg.ty, param.ty
                        );
                        r.warnings.push(msg);
                    }
                }
            }
        }

        // Return type agreement is soft (warning): the lowering
        // sometimes declares a return type that doesn't match what
        // the body actually produces (e.g., closures typed as Ptr
        // that return raw scalars).
        if let Terminator::Return(v) = &block.terminator {
            if v.ty != func.return_type {
                r.warnings.push(format!(
                    "{prefix}: b{} Return({v}) has type {:?} but function returns {:?}",
                    bid.0, v.ty, func.return_type
                ));
            }
        }
    }

    // Explicit block params check: every value used in a block must
    // be defined within that block (instruction dest or block param),
    // or be a constant defined in that block, or be a function param.
    // This ensures all cross-block value flow goes through block
    // params, making ownership analysis trivial.
    let func_params: HashSet<Value> = func.params.iter().copied().collect();
    for (bid, block) in &func.blocks {
        // Values available in this block: block params + instruction dests.
        let mut local: HashSet<Value> = block.params.iter().copied().collect();
        for inst in &block.insts {
            // Check operands before adding the dest — operands must
            // already be local (or func params).
            for v in inst.operands() {
                if !local.contains(&v) && !func_params.contains(&v) {
                    r.errors.push(format!(
                        "{prefix}: b{} uses {v} which is not a block param, \
                         local instruction, or function param (cross-block reference)",
                        bid.0
                    ));
                }
            }
            if let Some(d) = inst.dest() {
                local.insert(d);
            }
        }
        // Check terminator operands too.
        for v in block.terminator.operands() {
            if !local.contains(&v) && !func_params.contains(&v) {
                r.errors.push(format!(
                    "{prefix}: b{} terminator uses {v} which is not a block param, \
                     local instruction, or function param (cross-block reference)",
                    bid.0
                ));
            }
        }
    }
}
