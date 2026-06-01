//! MIR → bytes for aarch64.
//!
//! Two-pass over the instruction list:
//!   1. Compute the byte offset of each instruction (trivial since
//!      every aarch64 instruction is 4 bytes) and lay out data items
//!      after the code.
//!   2. Walk the instructions a second time, resolving each `Label`
//!      operand to a PC-relative byte offset, and call the matching
//!      encoder.
//!
//! Output is the concatenated `(code, data)` byte vectors — the
//! container (ELF/Mach-O) handles segment placement.

#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::little_endian_bytes,
    clippy::missing_const_for_fn,
    clippy::pub_with_shorthand,
    dead_code
)]

use std::collections::HashMap;

use super::encode::{self, Reg};
use super::mir::{DataItem, Label, MInst, VReg};

/// Mapping from `Label` → byte offset relative to the start of the
/// emitted code+data blob (code first, data after).
type LabelMap = HashMap<Label, u64>;

/// True for pseudo-ops that emit no bytes.
fn is_pseudo(inst: &MInst) -> bool {
    matches!(inst, MInst::BlockStart { .. } | MInst::FuncStart { .. })
}

fn build_label_map(insts: &[MInst], data: &[DataItem]) -> LabelMap {
    let mut map = LabelMap::new();
    let mut byte = 0_u64;
    for inst in insts {
        match inst {
            MInst::BlockStart { idx } => {
                map.insert(Label::Block(*idx), byte);
            }
            MInst::FuncStart { idx } => {
                map.insert(Label::Func(*idx), byte);
            }
            _ => byte += 4,
        }
    }
    let code_size = byte;
    let mut cursor = code_size;
    for item in data {
        map.insert(item.label, cursor + u64::from(item.label_offset));
        cursor += item.bytes.len() as u64;
    }
    map
}

fn vreg_to_phys(v: VReg) -> Reg {
    Reg(v.0)
}

/// Resolve `label` to a signed byte displacement from the instruction
/// at `inst_offset` (which is the byte offset of the instruction within
/// the combined code+data blob).
fn pc_relative(inst_offset: u64, label: Label, labels: &LabelMap) -> i32 {
    let target = *labels.get(&label).expect("undefined label");
    (target as i64 - inst_offset as i64) as i32
}

/// Encode a single MIR instruction into its 32-bit machine word.
/// Caller must NOT pass pseudo-ops (they emit nothing).
fn encode_inst(inst: &MInst, inst_offset: u64, labels: &LabelMap) -> u32 {
    let v = vreg_to_phys;
    match inst {
        MInst::MovImm { rd, imm } => encode::movz_imm16(v(*rd), *imm),
        MInst::MovInv { rd, imm } => encode::movn_imm16(v(*rd), *imm),
        MInst::MovkImm { rd, imm, shift } => encode::movk_imm16(v(*rd), *imm, *shift),
        MInst::MovReg { rd, rs } => encode::mov_reg(v(*rd), v(*rs)),
        MInst::AdrLabel { rd, label } => {
            let off = pc_relative(inst_offset, *label, labels);
            encode::adr(v(*rd), off)
        }
        MInst::LdrImm64 { rt, rn, byte_offset } => encode::ldr_imm64(v(*rt), v(*rn), *byte_offset),
        MInst::StrImm64 { rt, rn, byte_offset } => encode::str_imm64(v(*rt), v(*rn), *byte_offset),
        MInst::AddImm { rd, rn, imm } => encode::add_imm(v(*rd), v(*rn), *imm),
        MInst::SubImm { rd, rn, imm } => encode::sub_imm(v(*rd), v(*rn), *imm),
        MInst::AddReg { rd, rn, rm } => encode::add_reg(v(*rd), v(*rn), v(*rm)),
        MInst::SubReg { rd, rn, rm } => encode::sub_reg(v(*rd), v(*rn), v(*rm)),
        MInst::AndReg { rd, rn, rm } => encode::and_reg(v(*rd), v(*rn), v(*rm)),
        MInst::OrrReg { rd, rn, rm } => encode::orr_reg(v(*rd), v(*rn), v(*rm)),
        MInst::EorReg { rd, rn, rm } => encode::eor_reg(v(*rd), v(*rn), v(*rm)),
        MInst::LslReg { rd, rn, rm } => encode::lsl_reg(v(*rd), v(*rn), v(*rm)),
        MInst::LsrReg { rd, rn, rm } => encode::lsr_reg(v(*rd), v(*rn), v(*rm)),
        MInst::MulReg { rd, rn, rm } => encode::mul_reg(v(*rd), v(*rn), v(*rm)),
        MInst::UdivReg { rd, rn, rm } => encode::udiv_reg(v(*rd), v(*rn), v(*rm)),
        MInst::AddRegLsl3 { rd, rn, rm } => encode::add_reg_lsl3(v(*rd), v(*rn), v(*rm)),
        MInst::LdrbImm { rt, rn, byte_offset } => encode::ldrb_imm(v(*rt), v(*rn), *byte_offset),
        MInst::StrbImm { rt, rn, byte_offset } => encode::strb_imm(v(*rt), v(*rn), *byte_offset),
        MInst::Ret => encode::ret(),
        MInst::Nop => encode::nop(),
        MInst::Svc { imm } => encode::svc(*imm),
        MInst::Brk { imm } => encode::brk(*imm),
        MInst::CmpImm { rn, imm } => encode::cmp_imm(v(*rn), *imm),
        MInst::CmpReg { rn, rm } => encode::cmp_reg(v(*rn), v(*rm)),
        MInst::CSet { rd, cond } => encode::cset(v(*rd), *cond),
        MInst::CSel { rd, rn, rm, cond } => encode::csel(v(*rd), v(*rn), v(*rm), *cond),
        MInst::B { target } => encode::b(pc_relative(inst_offset, *target, labels)),
        MInst::Bl { target } => encode::bl(pc_relative(inst_offset, *target, labels)),
        MInst::BCond { cond, target } => {
            encode::b_cond(*cond, pc_relative(inst_offset, *target, labels))
        }
        MInst::BlockStart { .. } | MInst::FuncStart { .. } => {
            unreachable!("pseudo-op should not reach encoder")
        }
    }
}

/// Emit code + data to a contiguous byte vector. Code starts at offset
/// 0; data follows immediately. Returns `(combined_bytes, code_size)`.
#[must_use]
pub fn emit(insts: &[MInst], data: &[DataItem]) -> (Vec<u8>, u64) {
    let labels = build_label_map(insts, data);
    let mut out = Vec::new();
    for inst in insts {
        if is_pseudo(inst) {
            continue;
        }
        let pc = out.len() as u64;
        let word = encode_inst(inst, pc, &labels);
        out.extend_from_slice(&word.to_le_bytes());
    }
    let code_size = out.len() as u64;
    for item in data {
        out.extend_from_slice(&item.bytes);
    }
    (out, code_size)
}

#[cfg(test)]
mod tests {
    use super::*;

    const MSG: Label = Label::Data(0);

    /// Hand-written MIR for hello world. The list mirrors hello.rs's
    /// CODE table but uses MIR's symbolic Label instead of a baked-in
    /// +28 offset. Emit must resolve MSG correctly.
    fn hello_world_mir() -> Vec<MInst> {
        vec![
            MInst::MovImm { rd: VReg(0), imm: 1 },
            MInst::AdrLabel { rd: VReg(1), label: MSG },
            MInst::MovImm { rd: VReg(2), imm: 6 },
            MInst::MovImm { rd: VReg(8), imm: 64 },
            MInst::Svc { imm: 0 },
            MInst::MovImm { rd: VReg(0), imm: 0 },
            MInst::MovImm { rd: VReg(8), imm: 94 },
            MInst::Svc { imm: 0 },
        ]
    }

    fn hello_world_data() -> Vec<DataItem> {
        vec![DataItem { label: MSG, bytes: b"hello\n".to_vec(), label_offset: 0 }]
    }

    #[test]
    fn emit_resolves_msg_label_to_plus_28() {
        let (bytes, code_size) = emit(&hello_world_mir(), &hello_world_data());
        assert_eq!(code_size, 32, "code size mismatch");
        assert_eq!(bytes.len(), 38, "code + data size mismatch");
        // adr x1, msg is the second instruction (offset 4). msg is at
        // code+data offset 32. Displacement = 32 - 4 = 28. The encoded
        // u32 for `adr x1, +28` is 0x100000E1; little-endian: E1 00 00 10.
        assert_eq!(&bytes[4..8], &[0xE1, 0x00, 0x00, 0x10]);
    }

    /// Watermark: emit → ElfBuilder must reproduce the 158-byte Phase 0
    /// output byte-identically. This is the high-confidence moment for
    /// the whole MIR → bytes → container pipeline.
    #[test]
    fn hello_world_mir_round_trips_to_phase_0_watermark() {
        let (combined, code_size) = emit(&hello_world_mir(), &hello_world_data());
        let code = &combined[..code_size as usize];
        let data = &combined[code_size as usize..];
        let elf = crate::codegen::elf::build(0, code, data);
        assert_eq!(
            elf.as_slice(),
            crate::codegen::hello::HELLO_BYTES.as_slice(),
            "MIR-driven ELF diverged from Phase 0 watermark"
        );
    }
}
