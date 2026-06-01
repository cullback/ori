//! SSA → MIR instruction selection.
//!
//! Phase 3-lite scope:
//! - Trivial value → VReg mapping (`Value{id}` → `VReg(id)`), no
//!   regalloc. Caller is responsible for keeping the function's value
//!   IDs under 32 (one per physical register).
//! - Supported `Inst`s: `Const`, `StaticRef`, `Call` (when target is
//!   a recognized syscall intrinsic).
//! - Supported `Terminator`s: `Return` (unreachable after intrinsic
//!   exit, lowered as `brk #0` for fail-fast).
//!
//! Not yet supported (Phase 4+):
//! - General-purpose `Call` to other Ori functions (needs full ABI
//!   lowering, `bl`/`ret`, callee-saved spills).
//! - `Alloc` / `AllocDyn` / `RcInc` / `RcDec` (needs bump-on-mmap
//!   allocator wired in).
//! - `Load` / `Store` / `LoadDyn` / `StoreDyn` (need `ldr`/`str`
//!   encoders).
//! - `BinOp` (need `add`/`sub`/etc. encoders).
//! - `Jump` / `Branch` / `SwitchInt` (need branch encoders +
//!   displacement layout pass).
//! - Cow* family (FBIP runtime intrinsics).
//!
//! The intrinsic syscall recognition is the escape hatch that lets
//! us drive native codegen end-to-end without those bigger pieces.

#![allow(
    clippy::cast_possible_truncation,
    clippy::checked_conversions,
    clippy::doc_markdown,
    clippy::pub_with_shorthand,
    dead_code
)]

use crate::ssa::{Function, Inst, Module, StaticSlot, Terminator, Value};

use super::mir::{DataItem, Label, MInst, VReg};

/// Recognized syscall intrinsics. Each maps to an aarch64-linux
/// syscall number; args are taken from `Call.args` in order and must
/// already be in vregs that match the syscall arg-register convention.
fn syscall_number(target: &str) -> Option<u16> {
    match target {
        "__syscall_write" => Some(64),
        "__syscall_exit" => Some(94), // exit_group
        _ => None,
    }
}

fn value_to_vreg(v: Value) -> VReg {
    debug_assert!(v.id < 32, "Value id {} exceeds trivial vreg=phys map; need regalloc", v.id);
    #[expect(clippy::cast_possible_truncation, reason = "checked above")]
    VReg(v.id as u8)
}

fn lower_inst(inst: &Inst, out: &mut Vec<MInst>) {
    match inst {
        Inst::Const(dest, bits) => {
            // Phase 3-lite: only 16-bit unsigned immediates fit in a
            // single MOVZ. Larger constants need MOVZ+MOVK sequences.
            debug_assert!(*bits <= u64::from(u16::MAX), "Const {bits} exceeds movz_imm16 range");
            #[expect(clippy::cast_possible_truncation, reason = "checked above")]
            out.push(MInst::MovImm { rd: value_to_vreg(*dest), imm: *bits as u16 });
        }
        Inst::StaticRef(dest, idx) => {
            #[expect(clippy::cast_possible_truncation, reason = "static index bounded by module")]
            let label = Label::Data(*idx as u32);
            out.push(MInst::AdrLabel { rd: value_to_vreg(*dest), label });
        }
        Inst::Call { results, target, args } => {
            let syscall = syscall_number(target)
                .unwrap_or_else(|| panic!("Phase 3-lite only supports syscall intrinsics; got Call to {target}"));

            // Shuffle args into x0..x7 if not already there. With the
            // trivial vreg=phys mapping a Value already lives in its
            // numbered register, so the move is a no-op when arg N is
            // VReg(N).
            for (arg_idx, arg) in args.iter().enumerate() {
                let arg_vreg = value_to_vreg(*arg);
                #[expect(clippy::cast_possible_truncation, reason = "arg count bounded by syscall ABI (≤8)")]
                let target_vreg = VReg(arg_idx as u8);
                if arg_vreg != target_vreg {
                    out.push(MInst::MovReg { rd: target_vreg, rs: arg_vreg });
                }
            }

            // Syscall number → x8.
            out.push(MInst::MovImm { rd: VReg(8), imm: syscall });
            out.push(MInst::Svc { imm: 0 });

            // If the caller captures the result, mov x0 into the
            // result vreg. Phase 3-lite ignores return values when
            // `results` is empty — useful for write/exit which we
            // don't need to inspect.
            for r in results {
                let r_vreg = value_to_vreg(*r);
                if r_vreg != VReg(0) {
                    out.push(MInst::MovReg { rd: r_vreg, rs: VReg(0) });
                }
            }
        }
        _ => panic!(
            "Phase 3-lite: unsupported SSA instruction in selector: {inst:?}\n\
             see select.rs module docstring for what's wired up"
        ),
    }
}

fn lower_terminator(term: &Terminator, out: &mut Vec<MInst>) {
    match term {
        Terminator::Return(_) => {
            // For Phase 3-lite, programs are expected to reach exit
            // via a syscall intrinsic before the Return terminator.
            // If control somehow flows here, brk crashes fast rather
            // than executing a stale `ret` into nowhere.
            out.push(MInst::Brk { imm: 0 });
        }
        _ => panic!(
            "Phase 3-lite: unsupported terminator: {term:?}; only Return is wired up"
        ),
    }
}

/// Serialize a `StaticObject` into the byte form `AdrLabel` resolves
/// to. Phase 3-lite supports only `U8`-slot-only statics (raw byte
/// buffers). Wider slots and `StaticPtr` need byte-order + relocation
/// work that's premature for now.
fn static_to_bytes(slots: &[StaticSlot]) -> Vec<u8> {
    slots
        .iter()
        .map(|slot| match slot {
            StaticSlot::U8(b) => *b,
            other => panic!(
                "Phase 3-lite: unsupported static slot kind {other:?}; only U8 is wired up"
            ),
        })
        .collect()
}

/// Lower a single SSA `Function` to MIR.
#[must_use]
fn lower_function(func: &Function) -> Vec<MInst> {
    let mut out = Vec::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            lower_inst(inst, &mut out);
        }
        lower_terminator(&block.terminator, &mut out);
    }
    out
}

/// Lower an SSA `Module` to `(MIR, DataItems)`. The module's `entry`
/// function is the only one emitted in Phase 3-lite; multi-function
/// programs need `bl`/`ret` support that's not here yet.
#[must_use]
pub fn lower_module(module: &Module) -> (Vec<MInst>, Vec<DataItem>) {
    let entry = module
        .functions
        .get(&module.entry)
        .unwrap_or_else(|| panic!("module entry function {} not found", module.entry));
    let mir = lower_function(entry);

    #[expect(clippy::cast_possible_truncation, reason = "static count bounded by module")]
    let data: Vec<DataItem> = module
        .statics
        .iter()
        .enumerate()
        .map(|(idx, obj)| DataItem {
            label: Label::Data(idx as u32),
            bytes: static_to_bytes(&obj.slots),
            label_offset: 0,
        })
        .collect();

    (mir, data)
}
