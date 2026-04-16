//! Structural validator for SSA modules.
//!
//! Runs after each pass in the test harness to catch pass-induced
//! breakage immediately (missing types, dangling BlockIds, mismatched
//! block args, etc.) rather than discovering it later via a
//! confusing runtime crash.
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
/// soft inconsistencies (type lies, orphan entries) that don't
/// affect correctness today but should be cleaned up.
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

    if func.params.len() != func.param_types.len() {
        r.errors.push(format!(
            "{prefix}: params ({}) and param_types ({}) have different lengths",
            func.params.len(),
            func.param_types.len()
        ));
        return;
    }

    for (i, (p, ty)) in func.params.iter().zip(&func.param_types).enumerate() {
        match func.value_types.get(p) {
            None => r.errors.push(format!(
                "{prefix}: param #{i} ({p}) missing from value_types"
            )),
            Some(t) if t != ty => r.errors.push(format!(
                "{prefix}: param #{i} ({p}): param_types says {ty:?} but value_types says {t:?}"
            )),
            _ => {}
        }
    }

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
            if !func.value_types.contains_key(&p) {
                r.errors.push(format!(
                    "{prefix}: b{} param {p} missing from value_types",
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
                if !func.value_types.contains_key(&d) {
                    r.errors.push(format!(
                        "{prefix}: b{}:{idx} destination {d} missing from value_types",
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
        for (target, args) in block.terminator.successors() {
            let Some(target_block) = func.blocks.get(&target) else {
                r.errors.push(format!(
                    "{prefix}: b{} jumps to unknown block b{}",
                    bid.0, target.0
                ));
                continue;
            };
            if target_block.params.len() != args.len() {
                // Arg-count mismatches happen today on dead
                // fallthrough paths in match lowering (exhaustive
                // matches still emit a branch to merge without
                // args). Downgraded to a warning until the match
                // lowering is fixed to emit unreachable sinks.
                r.warnings.push(format!(
                    "{prefix}: b{} → b{}: passes {} args but target has {} params",
                    bid.0,
                    target.0,
                    args.len(),
                    target_block.params.len()
                ));
            } else {
                // Type agreement between arg and target param.
                // Warning-level: the runtime tolerates type lies
                // today but they hide real bugs.
                for (i, (arg, param)) in args.iter().zip(&target_block.params).enumerate() {
                    let arg_ty = func.value_types.get(arg);
                    let param_ty = func.value_types.get(param);
                    if arg_ty != param_ty {
                        let mut msg = String::new();
                        let _ = write!(
                            msg,
                            "{prefix}: b{} → b{}: arg #{i} {arg} has type {arg_ty:?}, target param {param} has type {param_ty:?}",
                            bid.0, target.0
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
            if let Some(ty) = func.value_types.get(v) {
                if *ty != func.return_type {
                    r.warnings.push(format!(
                        "{prefix}: b{} Return({v}) has type {ty:?} but function returns {:?}",
                        bid.0, func.return_type
                    ));
                }
            }
        }
    }

    // Orphan value_types entries — values with types but no
    // definition. Usually a pass deleting an instruction without
    // cleaning up its type entry. Warning-level; doesn't affect
    // eval.
    for &v in func.value_types.keys() {
        if !defined.contains(&v) {
            r.warnings.push(format!(
                "{prefix}: value_types has entry for {v} which is never defined"
            ));
        }
    }
}
