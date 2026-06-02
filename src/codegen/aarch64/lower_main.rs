//! Phase 4 path: lower a real Ori SSA module produced by the existing
//! frontend (parse → resolve → type → mono → lambda-lift → lower → opt)
//! into a runnable aarch64-linux binary.
//!
//! Scope is deliberately narrow — what's needed for `main = |a,i| Ok("hi")`
//! end-to-end:
//!
//! - Only the `__main` function is emitted; no inter-function `bl`.
//!   The body must be flat (no `Jump`/`Branch` / `SwitchInt`).
//! - Function params are ignored (the simplest programs don't use
//!   `args` or `stdin`).
//! - Supported `Inst`s: `StaticRef`, `RcInc`/`RcDec` (no-ops on
//!   sentinel-rc statics), `Const` (≤16-bit), and `Return` (mov
//!   result → x0).
//! - Supported `StaticSlot`s: `U8`, `U64`, `StaticPtr`. Slot bytes are
//!   packed without alignment padding (matches eval's heap layout).
//! - After `__main` returns, an inline runtime shim chases the `Result`
//!   tag-union shell to its `Str` payload and `write(2)`s it to stdout,
//!   exiting with code 0 for `Ok`, 1 for `Err`. The shim is hard-coded
//!   for the `Result(Str, Str)` shape `main`'s type fixes.
//!
//! Out of scope for now (Phase 5):
//! - `BinOp`, `Alloc`/`AllocDyn`, `Load`/`Store` (need real regalloc
//!   + bump-on-mmap allocator), control flow, inter-function calls.

#![allow(
    clippy::arithmetic_side_effects,
    clippy::cast_possible_truncation,
    clippy::checked_conversions,
    clippy::doc_markdown,
    clippy::get_unwrap,
    clippy::little_endian_bytes,
    clippy::missing_assert_message,
    clippy::missing_const_for_fn,
    clippy::needless_pass_by_value,
    clippy::pub_with_shorthand,
    dead_code
)]

use std::collections::HashMap;

use crate::ssa::instruction::BlockEdge;
use crate::ssa::{BinaryOp, BlockId, Function, Inst, Module, StaticSlot, Terminator, Value};

use super::encode::Cond;
use super::mir::{DataItem, Label, MInst, VReg};

/// Register policy for Phase 5e (stack-everything):
///   x0..x7     — function-call ABI (args + first ≤2 return values)
///   x8         — syscall number
///   x9         — scratch operand A (first load target)
///   x10        — scratch operand B (second load target)
///   x11        — scratch result (where the op writes before store)
///   x19..x21   — entry-shim scratch (mmap base, str header, bytes_read)
///   x28        — heap bump pointer (callee-saved by ABI; we own it)
///   x30        — link register; saved to frame for non-entry calls
///   sp         — stack pointer; frame allocated in function prologue
///
/// Every SSA Value gets a stack slot at `[sp, #(slot_offset)]`. Each
/// Inst loads its operands into x9/x10, computes into x11, stores the
/// result. Frame size is rounded up so `sub sp, sp, #FRAME` and
/// `add sp, sp, #FRAME` both encode in one instruction (either 12-bit
/// imm or LSL #12 form via our `add_imm`/`sub_imm` dispatch).
const HEAP_BUMP_REG: VReg = VReg(28);
const SP_REG: VReg = VReg(31);
const LR_REG: VReg = VReg(30);
const SCRATCH_A: VReg = VReg(9);
const SCRATCH_B: VReg = VReg(10);
const SCRATCH_C: VReg = VReg(11);

/// Per-function slot map: SSA value id → byte offset within the stack
/// frame. Slot 0 is at [sp+0], slot 1 at [sp+8], etc.
type SlotMap = HashMap<usize, u32>;

/// Frame layout for one function.
#[derive(Debug, Clone)]
struct Frame {
    /// SSA value id → byte offset within the frame.
    slots: SlotMap,
    /// Total bytes allocated by `sub sp` in the prologue. Always a
    /// multiple of 16 for SP alignment, and chosen so it fits in one
    /// `sub_imm` encoding.
    size: u32,
    /// Byte offset of the LR save slot (relative to sp). Only valid
    /// when the function is non-leaf (calls another function).
    lr_offset: u32,
    /// True iff the function contains any `Inst::Call` — needs to
    /// save/restore LR around its body.
    non_leaf: bool,
}

/// Round `n` up so it's a valid `add_imm` / `sub_imm` immediate AND a
/// multiple of 16 (SP alignment).
fn round_frame_size(raw: u32) -> u32 {
    let aligned = (raw + 15) & !15;
    if aligned < 4096 {
        aligned
    } else {
        // Round up to next multiple of 4096 so the LSL #12 form encodes it.
        (aligned + 4095) & !4095
    }
}

fn function_is_non_leaf(func: &Function) -> bool {
    func.blocks
        .values()
        .any(|b| b.insts.iter().any(|i| matches!(i, Inst::Call { .. })))
}

fn build_frame_for(func: &Function) -> Frame {
    let mut slots: SlotMap = HashMap::new();
    let mut next_offset: u32 = 0;
    let mut alloc = |id: usize, slots: &mut SlotMap, off: &mut u32| {
        slots.entry(id).or_insert_with(|| {
            let s = *off;
            *off += 8;
            s
        });
    };
    for p in &func.params {
        alloc(p.id, &mut slots, &mut next_offset);
    }
    for block in func.blocks.values() {
        for p in &block.params {
            alloc(p.id, &mut slots, &mut next_offset);
        }
        for inst in &block.insts {
            for d in inst.dests() {
                alloc(d.id, &mut slots, &mut next_offset);
            }
        }
    }
    let non_leaf = function_is_non_leaf(func);
    let raw = next_offset + if non_leaf { 8 } else { 0 };
    let size = round_frame_size(raw);
    let lr_offset = size - 8;
    Frame { slots, size, lr_offset, non_leaf }
}

/// Function-name → label-index lookup. Built once for the whole
/// module. Names are sorted so indices are stable across runs
/// (otherwise `HashMap` iteration order randomness leaks into our
/// codegen and the binary's behavior changes per invocation).
fn function_index_map(module: &Module) -> HashMap<String, u32> {
    let mut names: Vec<&String> = module.functions.keys().collect();
    names.sort();
    let mut map = HashMap::new();
    for (idx, name) in names.into_iter().enumerate() {
        #[expect(clippy::cast_possible_truncation, reason = "<= u32::MAX functions")]
        map.insert(name.clone(), idx as u32);
    }
    map
}

/// Iterate functions in a deterministic order (sorted by name).
fn functions_sorted(module: &Module) -> Vec<(&String, &Function)> {
    let mut pairs: Vec<_> = module.functions.iter().collect();
    pairs.sort_by(|a, b| a.0.cmp(b.0));
    pairs
}

fn slot_of(v: Value, frame: &Frame) -> u32 {
    *frame.slots.get(&v.id).unwrap_or_else(|| {
        panic!("SSA value v{} has no stack slot in this function", v.id)
    })
}

/// Emit `ldr Xreg, [sp, #slot]` for the value `v`.
fn emit_load(v: Value, reg: VReg, frame: &Frame, out: &mut Vec<MInst>) {
    out.push(MInst::LdrImm64 {
        rt: reg,
        rn: SP_REG,
        byte_offset: slot_of(v, frame),
    });
}

/// Emit `str Xreg, [sp, #slot]` for the value `v`. If `v.ty` is
/// narrower than 64 bits and the Facts lattice can't already prove
/// the value fits, prepend a narrowing op (`mov Wreg,Wreg` for U32 or
/// `and reg, reg, #mask` for U8/U16).
fn emit_store(
    v: Value,
    reg: VReg,
    frame: &Frame,
    facts: &HashMap<usize, super::facts::Facts>,
    out: &mut Vec<MInst>,
) {
    use crate::ssa::ScalarType;
    let needed_zh = match v.ty {
        ScalarType::U8 | ScalarType::I8 => 56_u8,
        ScalarType::U16 | ScalarType::I16 => 48,
        ScalarType::U32 | ScalarType::I32 => 32,
        _ => 0,
    };
    let already_narrow = facts
        .get(&v.id)
        .copied()
        .map_or(0, super::facts::Facts::known_zero_high_bits)
        >= needed_zh;
    if needed_zh > 0 && !already_narrow {
        match v.ty {
            ScalarType::U32 | ScalarType::I32 => {
                out.push(MInst::MovWReg { rd: reg, rs: reg });
            }
            ScalarType::U8 | ScalarType::I8 | ScalarType::U16 | ScalarType::I16 => {
                let mask = if matches!(v.ty, ScalarType::U16 | ScalarType::I16) {
                    0xFFFF_u16
                } else {
                    0xFF_u16
                };
                let tmp = if reg == VReg(12) { VReg(13) } else { VReg(12) };
                out.push(MInst::MovImm { rd: tmp, imm: mask });
                out.push(MInst::AndReg { rd: reg, rn: reg, rm: tmp });
            }
            _ => {}
        }
    }
    out.push(MInst::StrImm64 {
        rt: reg,
        rn: SP_REG,
        byte_offset: slot_of(v, frame),
    });
}

/// Lower one SSA instruction with stack-everything regalloc. Each
/// SSA Value reads through `[sp, #slot]` and writes the same way.
fn lower_inst(
    inst: &Inst,
    frame: &Frame,
    func_idx: &HashMap<String, u32>,
    facts: &HashMap<usize, super::facts::Facts>,
    out: &mut Vec<MInst>,
) {
    use super::facts::Facts;
    let fact_of = |v: Value| facts.get(&v.id).copied().unwrap_or(Facts::Top);
    match inst {
        Inst::StaticRef(dest, idx) => {
            out.push(MInst::AdrLabel { rd: SCRATCH_C, label: Label::Data(*idx as u32) });
            emit_store(*dest, SCRATCH_C, frame, facts, out);
        }
        Inst::RcInc(_) | Inst::RcDec(_) => {
            // No-op for the bump allocator. Statics' rc ops are dropped
            // at the SSA layer (opt/retype_statics drops them as part
            // of the RcPtr→Ptr retype, and the validator enforces "no
            // rc op on Ptr"), so anything reaching here is RcPtr-typed
            // — real heap, will need real rc emission once Phase 5h's
            // RC runtime lands.
        }
        Inst::Const(dest, bits) => {
            // Load via MOVZ + (optional MOVKs) for values wider than 16 bits.
            let low = (*bits & 0xFFFF) as u16;
            out.push(MInst::MovImm { rd: SCRATCH_C, imm: low });
            for shift in [16_u8, 32, 48] {
                let chunk = ((*bits >> shift) & 0xFFFF) as u16;
                if chunk != 0 {
                    out.push(MInst::MovkImm { rd: SCRATCH_C, imm: chunk, shift });
                }
            }
            emit_store(*dest, SCRATCH_C, frame, facts, out);
        }
        Inst::Alloc(dest, size) => {
            // Size-tracked: alloc 8 bytes of header + size bytes of payload.
            // Header at [user_ptr - 8] stores the payload size. This lets
            // cow_resize_dyn copy the right number of bytes.
            let aligned_payload = ((*size + 7) & !7) as u32;
            // header_ptr = bump_ptr; user_ptr = header_ptr + 8; bump += 8 + size
            out.push(MInst::MovReg { rd: SCRATCH_A, rs: HEAP_BUMP_REG });          // header_ptr
            out.push(MInst::MovImm { rd: SCRATCH_B, imm: aligned_payload.try_into().unwrap_or(0xFFFF) });
            // For sizes that fit in 16 bits we use MovImm; larger should not
            // appear for static Alloc (Ori SSA produces small literal sizes).
            assert!(aligned_payload <= u32::from(u16::MAX), "Alloc size too big: {aligned_payload}");
            out.push(MInst::StrImm64 { rt: SCRATCH_B, rn: SCRATCH_A, byte_offset: 0 }); // store size header
            out.push(MInst::AddImm { rd: SCRATCH_C, rn: SCRATCH_A, imm: 8 });       // user_ptr
            out.push(MInst::AddImm { rd: HEAP_BUMP_REG, rn: HEAP_BUMP_REG, imm: aligned_payload + 8 });
            emit_store(*dest, SCRATCH_C, frame, facts, out);
        }
        Inst::AllocDyn(dest, size_val) => {
            // Same as Alloc but size is a runtime value. Caller is
            // responsible for the size being 8-aligned.
            emit_load(*size_val, SCRATCH_B, frame, out);                                 // size
            out.push(MInst::MovReg { rd: SCRATCH_A, rs: HEAP_BUMP_REG });                // header_ptr
            out.push(MInst::StrImm64 { rt: SCRATCH_B, rn: SCRATCH_A, byte_offset: 0 });  // store size
            out.push(MInst::AddImm { rd: SCRATCH_C, rn: SCRATCH_A, imm: 8 });            // user_ptr
            out.push(MInst::AddReg { rd: HEAP_BUMP_REG, rn: HEAP_BUMP_REG, rm: SCRATCH_B });
            out.push(MInst::AddImm { rd: HEAP_BUMP_REG, rn: HEAP_BUMP_REG, imm: 8 });
            emit_store(*dest, SCRATCH_C, frame, facts, out);
        }
        Inst::CowResizeDyn(dest, ptr, new_size) => {
            // Allocate a new buffer of `new_size` bytes, copy
            // min(old_size, new_size) bytes from old → new, return
            // new user ptr.
            let old_ptr = VReg(12);
            let new_size_r = VReg(13);
            let old_size = VReg(14);
            let new_header = VReg(15);
            let new_user = VReg(16);
            let copy_size = VReg(17);
            let i = VReg(18);
            let byte = VReg(19);
            let addr_in = VReg(20);
            let addr_out = VReg(21);

            emit_load(*ptr, old_ptr, frame, out);
            emit_load(*new_size, new_size_r, frame, out);

            // old_size = [old_ptr - 8]; compute as (old_ptr - 8) + ldr [+0]
            out.push(MInst::SubImm { rd: addr_in, rn: old_ptr, imm: 8 });
            out.push(MInst::LdrImm64 { rt: old_size, rn: addr_in, byte_offset: 0 });

            // Allocate new (size-tracked).
            out.push(MInst::MovReg { rd: new_header, rs: HEAP_BUMP_REG });
            out.push(MInst::StrImm64 { rt: new_size_r, rn: new_header, byte_offset: 0 });
            out.push(MInst::AddImm { rd: new_user, rn: new_header, imm: 8 });
            out.push(MInst::AddReg { rd: HEAP_BUMP_REG, rn: HEAP_BUMP_REG, rm: new_size_r });
            out.push(MInst::AddImm { rd: HEAP_BUMP_REG, rn: HEAP_BUMP_REG, imm: 8 });

            // copy_size = min(old_size, new_size_r)
            out.push(MInst::CmpReg { rn: old_size, rm: new_size_r });
            out.push(MInst::CSel { rd: copy_size, rn: old_size, rm: new_size_r, cond: Cond::Lt });

            // Byte copy loop.
            let loop_id = 0x6000_0000 | (dest.id as u32 & 0x7FFF);
            let done_id = loop_id | 0x8000;
            out.push(MInst::MovImm { rd: i, imm: 0 });
            out.push(MInst::BlockStart { idx: loop_id });
            out.push(MInst::CmpReg { rn: i, rm: copy_size });
            out.push(MInst::BCond { cond: Cond::Ge, target: Label::Block(done_id) });
            out.push(MInst::AddReg { rd: addr_in, rn: old_ptr, rm: i });
            out.push(MInst::LdrbImm { rt: byte, rn: addr_in, byte_offset: 0 });
            out.push(MInst::AddReg { rd: addr_out, rn: new_user, rm: i });
            out.push(MInst::StrbImm { rt: byte, rn: addr_out, byte_offset: 0 });
            out.push(MInst::AddImm { rd: i, rn: i, imm: 1 });
            out.push(MInst::B { target: Label::Block(loop_id) });
            out.push(MInst::BlockStart { idx: done_id });

            emit_store(*dest, new_user, frame, facts, out);
        }
        Inst::Store(ptr, offset, val) => {
            assert!(*offset <= 0x7FF8, "Store offset {offset} out of range");
            assert!(offset.is_multiple_of(8), "Store offset must be 8-aligned");
            emit_load(*ptr, SCRATCH_A, frame, out);
            emit_load(*val, SCRATCH_B, frame, out);
            out.push(MInst::StrImm64 { rt: SCRATCH_B, rn: SCRATCH_A, byte_offset: *offset as u32 });
        }
        Inst::Load(dest, ptr, offset) => {
            assert!(*offset <= 0x7FF8, "Load offset {offset} out of range");
            assert!(offset.is_multiple_of(8), "Load offset must be 8-aligned");
            emit_load(*ptr, SCRATCH_A, frame, out);
            out.push(MInst::LdrImm64 { rt: SCRATCH_C, rn: SCRATCH_A, byte_offset: *offset as u32 });
            emit_store(*dest, SCRATCH_C, frame, facts, out);
        }
        Inst::LoadDyn(dest, ptr, idx_val) => {
            // Stride 8 uniformly (eval semantics). addr = ptr + idx*8.
            emit_load(*ptr, SCRATCH_A, frame, out);
            emit_load(*idx_val, SCRATCH_B, frame, out);
            out.push(MInst::AddRegLsl3 { rd: SCRATCH_C, rn: SCRATCH_A, rm: SCRATCH_B });
            out.push(MInst::LdrImm64 { rt: SCRATCH_C, rn: SCRATCH_C, byte_offset: 0 });
            emit_store(*dest, SCRATCH_C, frame, facts, out);
        }
        Inst::StoreDyn(ptr, idx_val, val) => {
            emit_load(*ptr, SCRATCH_A, frame, out);
            emit_load(*idx_val, SCRATCH_B, frame, out);
            out.push(MInst::AddRegLsl3 { rd: SCRATCH_A, rn: SCRATCH_A, rm: SCRATCH_B });
            emit_load(*val, SCRATCH_C, frame, out);
            out.push(MInst::StrImm64 { rt: SCRATCH_C, rn: SCRATCH_A, byte_offset: 0 });
        }
        Inst::BinOp(dest, op, lhs, rhs) => {
            // BinOp(Const, Const) is folded at the SSA layer by
            // opt/const_fold — by the time we get here both operands
            // are runtime values.
            emit_load(*lhs, SCRATCH_A, frame, out);
            emit_load(*rhs, SCRATCH_B, frame, out);
            let cmp_then = |cond: Cond, out: &mut Vec<MInst>| {
                out.push(MInst::CmpReg { rn: SCRATCH_A, rm: SCRATCH_B });
                out.push(MInst::CSet { rd: SCRATCH_C, cond });
            };
            match op {
                BinaryOp::Eq => cmp_then(Cond::Eq, out),
                BinaryOp::Neq => cmp_then(Cond::Ne, out),
                BinaryOp::Lt => cmp_then(Cond::Lt, out),
                BinaryOp::Le => cmp_then(Cond::Le, out),
                BinaryOp::Gt => cmp_then(Cond::Gt, out),
                BinaryOp::Ge => cmp_then(Cond::Ge, out),
                BinaryOp::Add => out.push(MInst::AddReg { rd: SCRATCH_C, rn: SCRATCH_A, rm: SCRATCH_B }),
                BinaryOp::Sub => out.push(MInst::SubReg { rd: SCRATCH_C, rn: SCRATCH_A, rm: SCRATCH_B }),
                BinaryOp::Mul => out.push(MInst::MulReg { rd: SCRATCH_C, rn: SCRATCH_A, rm: SCRATCH_B }),
                BinaryOp::And => out.push(MInst::AndReg { rd: SCRATCH_C, rn: SCRATCH_A, rm: SCRATCH_B }),
                BinaryOp::Or => out.push(MInst::OrrReg { rd: SCRATCH_C, rn: SCRATCH_A, rm: SCRATCH_B }),
                BinaryOp::Xor => out.push(MInst::EorReg { rd: SCRATCH_C, rn: SCRATCH_A, rm: SCRATCH_B }),
                BinaryOp::Shl => out.push(MInst::LslReg { rd: SCRATCH_C, rn: SCRATCH_A, rm: SCRATCH_B }),
                BinaryOp::Shr => out.push(MInst::LsrReg { rd: SCRATCH_C, rn: SCRATCH_A, rm: SCRATCH_B }),
                BinaryOp::Div => out.push(MInst::UdivReg { rd: SCRATCH_C, rn: SCRATCH_A, rm: SCRATCH_B }),
                BinaryOp::Rem => {
                    // rem = a - (a/b)*b. Uses x12 as a scratch outside our
                    // standard scratch trio to avoid clobbering.
                    let q = VReg(12);
                    out.push(MInst::UdivReg { rd: q, rn: SCRATCH_A, rm: SCRATCH_B });
                    out.push(MInst::MulReg { rd: q, rn: q, rm: SCRATCH_B });
                    out.push(MInst::SubReg { rd: SCRATCH_C, rn: SCRATCH_A, rm: q });
                }
                other => panic!("Phase 5e: unsupported BinOp {other:?}"),
            }
            emit_store(*dest, SCRATCH_C, frame, facts, out);
        }
        Inst::Call { results, target, args } => {
            // Builtin: `__crash` is the runtime panic helper called from
            // unwrap-on-None / unwrap-on-Err patterns. It never returns.
            // Phase 5f minimum: drop the error message and just `exit(1)`.
            // (Printing the message would mean inlining a third byte-pack
            // loop; doable later.)
            if target == "__crash" {
                out.push(MInst::MovImm { rd: VReg(0), imm: 1 });
                out.push(MInst::MovImm { rd: VReg(8), imm: 94 });
                out.push(MInst::Svc { imm: 0 });
                out.push(MInst::Brk { imm: 0 });
                return;
            }

            assert!(args.len() <= 8, "Phase 5e: >8 args needs stack-passed args");
            assert!(results.len() <= 8, "Phase 5e: >8 return values needs stack-passed returns");
            for (i, arg) in args.iter().enumerate() {
                #[expect(clippy::cast_possible_truncation, reason = "≤ 8 args")]
                let target_reg = VReg(i as u8);
                emit_load(*arg, target_reg, frame, out);
            }
            let idx = *func_idx.get(target).unwrap_or_else(|| {
                panic!("Phase 5e: Call to unknown function {target}")
            });
            out.push(MInst::Bl { target: Label::Func(idx) });
            for (i, r) in results.iter().enumerate() {
                #[expect(clippy::cast_possible_truncation, reason = "≤ 8 returns")]
                let src_reg = VReg(i as u8);
                emit_store(*r, src_reg, frame, facts, out);
            }
        }
        Inst::Cast(dest, src) | Inst::BitCast(dest, src) => {
            // Phase 5f: rely on 8-byte slots being zero-padded for
            // smaller types — widening is just a slot copy. Narrowing
            // is also a slot copy (high bits get carried but Ori
            // semantics check the narrowed width at use sites).
            emit_load(*src, SCRATCH_C, frame, out);
            emit_store(*dest, SCRATCH_C, frame, facts, out);
        }
        other => panic!("Phase 5e: unsupported SSA inst: {other:?}"),
    }
}

/// Sentinel block index used for the runtime-shim "exit" landing pad.
/// Every `Return` lowers to a jump to this label, where the post-main
/// shim begins. Real block ids start at 0; we pick a high one out of
/// the way.
const EXIT_BLOCK_LABEL: u32 = 0xFFFF_FFFE;

/// Emit slot-to-slot copies for an edge's block-param plumbing.
/// For each (edge arg, dest param) pair, load from arg's slot into a
/// scratch register and store into the dest param's slot.
///
/// Order doesn't matter because we always go through a scratch — no
/// two pairs interfere (no shared destination since SSA gives every
/// param a unique slot).
fn emit_edge_moves(
    edge: &BlockEdge,
    dest_block: BlockId,
    func: &Function,
    frame: &Frame,
    facts: &HashMap<usize, super::facts::Facts>,
    out: &mut Vec<MInst>,
) {
    let dest = func.blocks.get(&dest_block).expect("edge to nonexistent block");
    assert_eq!(edge.args.len(), dest.params.len(), "edge arity mismatch");
    for (arg, param) in edge.args.iter().zip(&dest.params) {
        if slot_of(*arg, frame) == slot_of(*param, frame) {
            continue;
        }
        emit_load(*arg, SCRATCH_A, frame, out);
        emit_store(*param, SCRATCH_A, frame, facts, out);
    }
}

/// Pack a per-function block id into a globally-unique label.
/// Layout: bits 30:16 = func_idx, bits 15:0 = local block id.
/// Synthetic thunk ids set bits 31 or 30, keeping them disjoint.
#[expect(clippy::cast_possible_truncation, reason = "block ids fit in 16 bits, func ids in 15")]
fn block_label(func_idx: u32, bid: BlockId) -> Label {
    Label::Block(((func_idx & 0x7FFF) << 16) | (bid.0 as u32 & 0xFFFF))
}

/// Lower a terminator. For non-entry functions, Return moves values to
/// x0..xN and does `ret`. For the entry (`__main`), it jumps to the
/// shared `EXIT_BLOCK_LABEL` where the runtime shim takes over.
fn lower_terminator(
    term: &Terminator,
    func: &Function,
    func_idx: u32,
    is_entry: bool,
    frame: &Frame,
    facts: &HashMap<usize, super::facts::Facts>,
    out: &mut Vec<MInst>,
) {
    use super::facts::Facts;
    let fact_of = |v: Value| facts.get(&v.id).copied().unwrap_or(Facts::Top);
    match term {
        Terminator::Return(vs) => {
            assert!(vs.len() <= 8, "Phase 5e: >8 return values needs stack-passed returns");
            // Load return values from slots into x0..xN.
            for (i, v) in vs.iter().enumerate() {
                #[expect(clippy::cast_possible_truncation, reason = "≤ 8 returns")]
                let dst = VReg(i as u8);
                emit_load(*v, dst, frame, out);
            }
            if is_entry {
                // No epilogue — entry never returns; runtime shim exits.
                out.push(MInst::B { target: Label::Block(EXIT_BLOCK_LABEL) });
            } else {
                emit_epilogue(frame, out);
                out.push(MInst::Ret);
            }
        }
        Terminator::Jump(edge) => {
            emit_edge_moves(edge, edge.target, func, frame, facts, out);
            out.push(MInst::B { target: block_label(func_idx, edge.target) });
        }
        Terminator::Branch { cond, then_edge, else_edge } => {
            // Branch with Const cond is folded to Jump at SSA layer
            // by opt/const_term_fold — by here cond is runtime.
            emit_load(*cond, SCRATCH_A, frame, out);
            out.push(MInst::CmpImm { rn: SCRATCH_A, imm: 0 });
            let thunk_id = synth_branch_thunk_id(func_idx, then_edge.target);
            out.push(MInst::BCond { cond: Cond::Ne, target: Label::Block(thunk_id) });
            emit_edge_moves(else_edge, else_edge.target, func, frame, facts, out);
            out.push(MInst::B { target: block_label(func_idx, else_edge.target) });
            out.push(MInst::BlockStart { idx: thunk_id });
            emit_edge_moves(then_edge, then_edge.target, func, frame, facts, out);
            out.push(MInst::B { target: block_label(func_idx, then_edge.target) });
        }
        Terminator::SwitchInt { scrutinee, arms, default } => {
            // SwitchInt with Const scrutinee is folded to Jump at SSA
            // layer by opt/const_term_fold — by here scrutinee is runtime.
            emit_load(*scrutinee, SCRATCH_A, frame, out);
            for (i, (val, edge)) in arms.iter().enumerate() {
                let val_u32 = u32::try_from(*val).expect("Phase 5e: switch arm value > u32");
                out.push(MInst::CmpImm { rn: SCRATCH_A, imm: val_u32 });
                #[expect(clippy::cast_possible_truncation, reason = "≤ 8 arms in practice")]
                let thunk_id = synth_switch_thunk_id(func_idx, edge.target, i as u32);
                out.push(MInst::BCond { cond: Cond::Eq, target: Label::Block(thunk_id) });
            }
            match default {
                Some(edge) => {
                    emit_edge_moves(edge, edge.target, func, frame, facts, out);
                    out.push(MInst::B { target: block_label(func_idx, edge.target) });
                }
                None => out.push(MInst::Brk { imm: 0 }),
            }
            for (i, (_, edge)) in arms.iter().enumerate() {
                #[expect(clippy::cast_possible_truncation, reason = "≤ 8 arms in practice")]
                let thunk_id = synth_switch_thunk_id(func_idx, edge.target, i as u32);
                out.push(MInst::BlockStart { idx: thunk_id });
                emit_edge_moves(edge, edge.target, func, frame, facts, out);
                out.push(MInst::B { target: block_label(func_idx, edge.target) });
            }
        }
    }
}

/// Emit `sub sp, sp, #FRAME`; if non-leaf, save x30 at `lr_offset`.
/// Then spill each function parameter from x0..xN into its slot.
fn emit_prologue(
    func: &Function,
    frame: &Frame,
    facts: &HashMap<usize, super::facts::Facts>,
    out: &mut Vec<MInst>,
) {
    if frame.size > 0 {
        out.push(MInst::SubImm { rd: SP_REG, rn: SP_REG, imm: frame.size });
    }
    if frame.non_leaf {
        out.push(MInst::StrImm64 { rt: LR_REG, rn: SP_REG, byte_offset: frame.lr_offset });
    }
    // Spill the function's incoming params from x0..xN to their slots.
    for (i, p) in func.params.iter().enumerate() {
        #[expect(clippy::cast_possible_truncation, reason = "≤ 8 params")]
        let src = VReg(i as u8);
        emit_store(*p, src, frame, facts, out);
    }
}

/// Emit `ldr x30, [sp, #lr_offset]` (if non-leaf) and `add sp, sp, #FRAME`.
/// The caller is responsible for the trailing `ret`.
fn emit_epilogue(frame: &Frame, out: &mut Vec<MInst>) {
    if frame.non_leaf {
        out.push(MInst::LdrImm64 { rt: LR_REG, rn: SP_REG, byte_offset: frame.lr_offset });
    }
    if frame.size > 0 {
        out.push(MInst::AddImm { rd: SP_REG, rn: SP_REG, imm: frame.size });
    }
}

/// Synthesize a unique block-label id for a Branch's then-thunk.
/// Sets bit 31 to keep it disjoint from real block labels.
fn synth_branch_thunk_id(func_idx: u32, target: BlockId) -> u32 {
    #[expect(clippy::cast_possible_truncation, reason = "block / func ids fit in 15 bits each")]
    let base = ((func_idx & 0x7FFF) << 16) | (target.0 as u32 & 0xFFFF);
    0x8000_0000 | base
}

/// Synthesize a unique block-label id for a Switch arm's thunk.
/// Bits 31:30 = 11; encodes arm index in the low bits below func_idx.
fn synth_switch_thunk_id(func_idx: u32, target: BlockId, arm_idx: u32) -> u32 {
    #[expect(clippy::cast_possible_truncation, reason = "block / func ids fit in 15 bits each")]
    let local = ((func_idx & 0x7F) << 16) | ((arm_idx & 0xFF) << 8) | (target.0 as u32 & 0xFF);
    0xC000_0000 | local
}

/// Wrap the runtime shim with a `BlockStart { EXIT_BLOCK_LABEL }` so
/// every `Return` lowering can `B` here.
fn runtime_shim_with_label() -> Vec<MInst> {
    let mut v = vec![MInst::BlockStart { idx: EXIT_BLOCK_LABEL }];
    v.extend(runtime_shim());
    v
}

/// Inline `_start` shim that runs AFTER __main's body has placed the
/// Result pointer in x0. Decodes `Result(Str, Str)` and writes the
/// payload Str's bytes to stdout (Ok) or stderr (Err).
///
/// Because the Str's data buffer is 8-byte-slotted (each byte in its
/// own slot), we first byte-pack it into a contiguous buffer using
/// the bump heap, then write that.
///
///   result_ptr in x0
///   ldr x19, [x0, #0]   ; tag (saved for fd/exit_code decision)
///   ldr x0,  [x0, #8]   ; payload_ptr
///   ldr x0,  [x0, #0]   ; str_ptr
///   ldr x2,  [x0, #0]   ; len
///   ldr x3,  [x0, #16]  ; data_ptr (8-byte-spread)
///
///   mov x4, x28         ; out_buf = bump pointer (fresh region)
///   add x28, x28, x2    ; advance bump past out_buf
///
///   mov x5, #0          ; i = 0
/// pack_loop:
///   cmp x5, x2
///   b.ge pack_done
///   add x6, x3, x5, lsl #3   ; addr = data_ptr + i*8
///   ldrb w7, [x6]            ; byte = data_ptr[i*8]
///   strb w7, [x4, x5]        ; out_buf[i] = byte (uses STRB Wt, [Xn, #imm]
///                            ; but our encoder takes a reg-imm; here imm
///                            ; is variable so we use add+strb#0)
///   add x5, x5, #1
///   b pack_loop
/// pack_done:
///
///   ; write(fd, out_buf, len)
///   cmp x19, #0
///   b.eq ok_path
///   mov x0, #2          ; stderr
///   b after_fd
/// ok_path:
///   mov x0, #1          ; stdout
/// after_fd:
///   mov x1, x4
///   mov x8, #64
///   svc #0
///
///   ; exit(tag)  (0 for Ok, 1 for Err)
///   mov x0, x19
///   mov x8, #94
///   svc #0
///   brk #0
fn runtime_shim() -> Vec<MInst> {
    let result_ptr = VReg(0);
    let tag = VReg(19);
    let str_ptr = VReg(0);   // reused after walking
    let len = VReg(2);
    let data_ptr = VReg(3);
    let out_buf = VReg(4);
    let i = VReg(5);
    let addr_in = VReg(6);
    let byte = VReg(7);
    let addr_out = VReg(20);

    vec![
        // Decode Result → Str → (len, data_ptr).
        MInst::LdrImm64 { rt: tag, rn: result_ptr, byte_offset: 0 },     // tag
        MInst::LdrImm64 { rt: VReg(0), rn: result_ptr, byte_offset: 8 }, // payload_ptr
        MInst::LdrImm64 { rt: VReg(0), rn: VReg(0), byte_offset: 0 },    // str_ptr
        MInst::LdrImm64 { rt: len, rn: str_ptr, byte_offset: 0 },        // len
        MInst::LdrImm64 { rt: data_ptr, rn: str_ptr, byte_offset: 16 },  // data ptr

        // Allocate packed-output buffer from the bump heap.
        MInst::MovReg { rd: out_buf, rs: HEAP_BUMP_REG },
        // bump += len (round up so x28 stays aligned doesn't matter at exit).
        MInst::AddReg { rd: HEAP_BUMP_REG, rn: HEAP_BUMP_REG, rm: len },

        // Pack loop: for i in 0..len: out_buf[i] = data_ptr[i*8] (low byte).
        MInst::MovImm { rd: i, imm: 0 },
        MInst::BlockStart { idx: SHIM_PACK_LOOP },
        MInst::CmpReg { rn: i, rm: len },
        MInst::BCond { cond: Cond::Ge, target: Label::Block(SHIM_PACK_DONE) },
        MInst::AddRegLsl3 { rd: addr_in, rn: data_ptr, rm: i },
        MInst::LdrbImm { rt: byte, rn: addr_in, byte_offset: 0 },
        MInst::AddReg { rd: addr_out, rn: out_buf, rm: i },
        MInst::StrbImm { rt: byte, rn: addr_out, byte_offset: 0 },
        MInst::AddImm { rd: i, rn: i, imm: 1 },
        MInst::B { target: Label::Block(SHIM_PACK_LOOP) },
        MInst::BlockStart { idx: SHIM_PACK_DONE },

        // write(fd, out_buf, len). fd = 1 (Ok=stdout) or 2 (Err=stderr).
        // Branchless: cset gives 0/1, then +1 → 1/2.
        MInst::CmpImm { rn: tag, imm: 0 },
        MInst::CSet { rd: VReg(0), cond: Cond::Ne },
        MInst::AddImm { rd: VReg(0), rn: VReg(0), imm: 1 },
        MInst::MovReg { rd: VReg(1), rs: out_buf },
        MInst::MovImm { rd: VReg(8), imm: 64 }, // write syscall
        MInst::Svc { imm: 0 },

        // exit(tag): 0 for Ok, 1 for Err.
        MInst::MovReg { rd: VReg(0), rs: tag },
        MInst::MovImm { rd: VReg(8), imm: 94 }, // exit_group
        MInst::Svc { imm: 0 },
        MInst::Brk { imm: 0 }, // unreachable
    ]
}

/// Heap arena layout (mmap'd at startup):
///   [0 .. STDIN_RAW_SIZE)               : raw stdin buffer
///   [STDIN_RAW_SIZE .. SPREAD)          : 8-byte-spread input data (data_ptr)
///   [SPREAD .. STRH)                     : input Str header (24 bytes)
///   [STRH .. ARGS)                       : empty args List header (24 bytes)
///   [ARGS .. ARENA_SIZE)                 : bump heap
const STDIN_RAW_SIZE: u16 = 0x800;       // 2 KiB raw bytes from read
const STDIN_SPREAD_SIZE: u16 = 0x4000;   // 16 KiB (2 KiB * 8)
/// Total arena size, in units of 16 (so the value fits a 16-bit movz
/// with LSL #16: `imm << 16 = bytes`). Without real RC, allocations
/// leak monotonically — the bench at N=5000 needs ~80 MiB; we leave
/// generous headroom. mmap of anonymous pages is lazy, so this only
/// costs address space, not committed memory.
const ARENA_SIZE_HIGH16: u16 = 0x4000;   // 1 GiB (anonymous pages are lazy)

/// Block labels reserved for shim-internal loops. Range 0x4000_0000
/// is free of real block labels (`(func<<16)|bid`) and synth thunks
/// (`0x8000_0000+`).
const SHIM_PACK_LOOP: u32 = 0x4000_0003;
const SHIM_PACK_DONE: u32 = 0x4000_0004;
const SHIM_SPREAD_LOOP: u32 = 0x4000_0005;
const SHIM_SPREAD_DONE: u32 = 0x4000_0006;

/// Generate the `_start` entry shim that runs before `__main`'s body:
///   1. mmap the arena.
///   2. read(0, arena, STDIN_BUF_SIZE).
///   3. Build the input Str header inside the arena.
///   4. Place args (= 0, unused), input ptr, and bump pointer into
///      x0, x1, x28 respectively.
/// Entry shim:
///   1. mmap a 60 KiB arena.
///   2. Read up to STDIN_RAW_SIZE bytes of stdin into the raw buffer.
///   3. Spread each byte into an 8-byte slot in the spread buffer
///      (so SSA's LoadDyn(idx) at `idx*8` returns the right byte).
///   4. Build the input Str header pointing at the spread buffer.
///   5. Build an empty args List header (3 zero u64 slots).
///   6. Set x0 = args ptr, x1 = input Str ptr, x28 = bump heap base.
fn entry_shim() -> Vec<MInst> {
    let arena = VReg(19);
    let strh = VReg(20);
    let bytes_read = VReg(21);
    let raw_buf = arena;                 // alias for clarity
    let spread_buf = VReg(22);
    let i = VReg(5);
    let byte = VReg(6);
    let addr_in = VReg(7);
    let addr_out = VReg(23);

    vec![
        // mmap(addr=0, len=ARENA_SIZE_HIGH16<<16, prot=R|W, flags=PRIVATE|ANON, fd=-1, off=0)
        MInst::MovImm { rd: VReg(0), imm: 0 },
        MInst::MovImmShl { rd: VReg(1), imm: ARENA_SIZE_HIGH16, shift: 16 },
        MInst::MovImm { rd: VReg(2), imm: 3 },         // prot = R|W
        MInst::MovImm { rd: VReg(3), imm: 0x22 },      // PRIVATE | ANON
        MInst::MovInv { rd: VReg(4), imm: 0 },         // fd = -1
        MInst::MovImm { rd: VReg(5), imm: 0 },         // offset
        MInst::MovImm { rd: VReg(8), imm: 222 },       // mmap
        MInst::Svc { imm: 0 },
        MInst::MovReg { rd: arena, rs: VReg(0) },

        // read(fd=0, buf=raw_buf, count=STDIN_RAW_SIZE)
        MInst::MovImm { rd: VReg(0), imm: 0 },
        MInst::MovReg { rd: VReg(1), rs: raw_buf },
        MInst::MovImm { rd: VReg(2), imm: STDIN_RAW_SIZE },
        MInst::MovImm { rd: VReg(8), imm: 63 },        // read
        MInst::Svc { imm: 0 },
        MInst::MovReg { rd: bytes_read, rs: VReg(0) },

        // spread_buf = arena + STDIN_RAW_SIZE + 8 (8-byte size header
        // precedes the user pointer, so cow_resize_dyn can find the size).
        MInst::AddImm { rd: spread_buf, rn: arena, imm: u32::from(STDIN_RAW_SIZE) + 8 },

        // Spread loop: for i in 0..bytes_read:
        //   byte    = raw_buf[i]              (1-byte stride)
        //   spread_buf[i*8] = byte            (8-byte slot, low byte)
        MInst::MovImm { rd: i, imm: 0 },
        MInst::BlockStart { idx: SHIM_SPREAD_LOOP },
        MInst::CmpReg { rn: i, rm: bytes_read },
        MInst::BCond { cond: Cond::Ge, target: Label::Block(SHIM_SPREAD_DONE) },
        MInst::AddReg { rd: addr_in, rn: raw_buf, rm: i },
        MInst::LdrbImm { rt: byte, rn: addr_in, byte_offset: 0 },
        MInst::AddRegLsl3 { rd: addr_out, rn: spread_buf, rm: i },
        MInst::StrImm64 { rt: byte, rn: addr_out, byte_offset: 0 },
        MInst::AddImm { rd: i, rn: i, imm: 1 },
        MInst::B { target: Label::Block(SHIM_SPREAD_LOOP) },
        MInst::BlockStart { idx: SHIM_SPREAD_DONE },

        // Write the spread_buf's size header: [spread_buf - 8] = bytes_read * 8.
        // VReg(2) = bytes_read * 8 via add_reg_lsl3 with xzr base.
        MInst::AddRegLsl3 { rd: VReg(2), rn: VReg(31), rm: bytes_read },
        MInst::SubImm { rd: VReg(3), rn: spread_buf, imm: 8 },  // header addr
        MInst::StrImm64 { rt: VReg(2), rn: VReg(3), byte_offset: 0 },

        // strh = spread_buf + STDIN_SPREAD_SIZE
        MInst::AddImm { rd: strh, rn: spread_buf, imm: u32::from(STDIN_SPREAD_SIZE) },
        // Str header: (len, cap, data_ptr)
        MInst::StrImm64 { rt: bytes_read, rn: strh, byte_offset: 0 },
        MInst::MovImm { rd: VReg(2), imm: STDIN_RAW_SIZE },
        MInst::StrImm64 { rt: VReg(2), rn: strh, byte_offset: 8 },
        MInst::StrImm64 { rt: spread_buf, rn: strh, byte_offset: 16 },

        // Empty args List header at strh + 24.
        MInst::AddImm { rd: VReg(2), rn: strh, imm: 24 },
        MInst::StrImm64 { rt: VReg(31), rn: VReg(2), byte_offset: 0 },
        MInst::StrImm64 { rt: VReg(31), rn: VReg(2), byte_offset: 8 },
        MInst::StrImm64 { rt: VReg(31), rn: VReg(2), byte_offset: 16 },

        // Bump pointer past args header.
        MInst::AddImm { rd: HEAP_BUMP_REG, rn: strh, imm: 48 },

        // Set up __main params.
        MInst::MovReg { rd: VReg(0), rs: VReg(2) },  // args
        MInst::MovReg { rd: VReg(1), rs: strh },     // input
    ]
}

/// Emit one function with stack-everything regalloc. Prologue
/// allocates the frame and spills params; body uses [sp, #slot]
/// for every Value access; epilogue at each Return restores LR
/// and deallocates the frame (or, for the entry, jumps to EXIT).
fn lower_function(
    func: &Function,
    func_idx_map: &HashMap<String, u32>,
    is_entry: bool,
    out: &mut Vec<MInst>,
) {
    let frame = build_frame_for(func);
    let func_idx = *func_idx_map.get(&func.name).expect("function not in idx map");
    // Compute facts once per function; both lower_inst and
    // lower_terminator consult the same map.
    let facts = super::facts::analyze(func);

    if !is_entry {
        out.push(MInst::FuncStart { idx: func_idx });
    }

    emit_prologue(func, &frame, &facts, out);

    for (bid, block) in &func.blocks {
        let combined = match block_label(func_idx, *bid) {
            Label::Block(c) => c,
            _ => unreachable!(),
        };
        out.push(MInst::BlockStart { idx: combined });
        for inst in &block.insts {
            lower_inst(inst, &frame, func_idx_map, &facts, out);
        }
        lower_terminator(&block.terminator, func, func_idx, is_entry, &frame, &facts, out);
    }
}

/// Lower module → MIR. Emits in order:
///   1. entry shim (mmap, stdin read, params setup)
///   2. entry function (__main) body
///   3. runtime shim at EXIT label
///   4. each non-entry function (so __main can `bl` them)
///   5. 8-byte alignment pad before data
#[must_use]
pub fn lower_to_mir(module: &Module) -> Vec<MInst> {
    let func_idx_map = function_index_map(module);

    let mut out = entry_shim();

    let entry = module.functions.get(&module.entry).expect("entry function not found");
    lower_function(entry, &func_idx_map, /*is_entry*/ true, &mut out);

    out.extend(runtime_shim_with_label());

    for (name, func) in functions_sorted(module) {
        if name == &module.entry {
            continue;
        }
        lower_function(func, &func_idx_map, /*is_entry*/ false, &mut out);
    }

    // Pad the code stream to an 8-byte boundary so the data section
    // that follows (with U64 / pointer slots) is naturally aligned.
    let code_bytes: usize = out
        .iter()
        .filter(|i| !matches!(i, MInst::BlockStart { .. } | MInst::FuncStart { .. }))
        .count()
        * 4;
    if !code_bytes.is_multiple_of(8) {
        out.push(MInst::Nop);
    }

    out
}

// ---------- Const-return specialization ----------

/// What we can extract at compile time when `main` returns a fully
/// static-resolved `Result(Str, Str)`.
#[derive(Clone, Debug)]
pub struct ConstReturn {
    /// 0 = Ok, 1 = Err.
    pub tag: u64,
    /// Length of the inner Str in bytes.
    pub len: u64,
    /// Index into `module.statics` of the raw byte buffer.
    pub data_static_idx: usize,
}

/// Walk the function body to find the `StaticRef` that defines `v`.
/// Returns the static index, or None if `v` isn't directly a static.
fn static_idx_of(func: &Function, v: Value) -> Option<usize> {
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::StaticRef(d, idx) = inst {
                if *d == v {
                    return Some(*idx);
                }
            }
        }
    }
    None
}

/// Recognize the "main returns a fully-static Ok/Err(string)" shape.
///
/// SSA pattern (post-opt):
///   __main returns v_result
///   v_result = StaticRef @result_idx
///   @result_idx = [U64(tag), StaticPtr(@payload_idx)]
///   @payload_idx = [StaticPtr(@str_idx)]
///   @str_idx = [U64(len), U64(_cap), StaticPtr(@data_idx)]
///   @data_idx = [U8, U8, ...] (raw bytes)
#[must_use]
pub fn analyze_const_return(module: &Module) -> Option<ConstReturn> {
    let func = module.functions.get(&module.entry)?;
    if func.blocks.len() != 1 {
        return None;
    }
    let block = func.blocks.values().next()?;
    let Terminator::Return(vs) = &block.terminator else {
        return None;
    };
    if vs.len() != 1 {
        return None;
    }

    let result_idx = static_idx_of(func, vs[0])?;
    let result_obj = module.statics.get(result_idx)?;
    let [StaticSlot::U64(tag), StaticSlot::StaticPtr(payload_idx)] = result_obj.slots.as_slice()
    else {
        return None;
    };

    let payload_obj = module.statics.get(*payload_idx)?;
    let [StaticSlot::StaticPtr(str_idx)] = payload_obj.slots.as_slice() else {
        return None;
    };

    let str_obj = module.statics.get(*str_idx)?;
    let [StaticSlot::U64(len), StaticSlot::U64(_cap), StaticSlot::StaticPtr(data_idx)] =
        str_obj.slots.as_slice()
    else {
        return None;
    };

    // Verify the bytes static is pure-U8.
    let data_obj = module.statics.get(*data_idx)?;
    if !data_obj.slots.iter().all(|s| matches!(s, StaticSlot::U8(_))) {
        return None;
    }

    Some(ConstReturn { tag: *tag, len: *len, data_static_idx: *data_idx })
}

/// MIR + data for the specialized const-return path. Drops the
/// runtime Result decoder, drops the unreferenced statics, and picks
/// the right fd (1=stdout / 2=stderr) and exit code (0/1) for the
/// tag.
#[must_use]
pub fn lower_const_return(info: &ConstReturn, module: &Module) -> (Vec<MInst>, Vec<DataItem>) {
    let data_obj = &module.statics[info.data_static_idx];
    let data_bytes: Vec<u8> = data_obj
        .slots
        .iter()
        .map(|s| {
            if let StaticSlot::U8(b) = s { *b } else { unreachable!() }
        })
        .collect();

    let fd: u16 = if info.tag == 0 { 1 } else { 2 };
    let exit_code: u16 = if info.tag == 0 { 0 } else { 1 };
    let len_u16: u16 = u16::try_from(info.len).expect("len exceeds u16 in const-return path");

    // Data label 0 → the bytes blob. We only emit one data item.
    let label = Label::Data(0);

    let mir = vec![
        MInst::MovImm { rd: VReg(0), imm: fd },
        MInst::AdrLabel { rd: VReg(1), label },
        MInst::MovImm { rd: VReg(2), imm: len_u16 },
        MInst::MovImm { rd: VReg(8), imm: 64 },
        MInst::Svc { imm: 0 },
        MInst::MovImm { rd: VReg(0), imm: exit_code },
        MInst::MovImm { rd: VReg(8), imm: 94 },
        MInst::Svc { imm: 0 },
    ];

    // Const-return path emits raw bytes (no size header) since it
    // calls write() directly with len.
    let data = vec![DataItem { label, bytes: data_bytes, label_offset: 0 }];
    (mir, data)
}

// ---------- Static data emission ----------

const LOAD_VADDR: u64 = 0x0040_0000;
const PAYLOAD_FILE_OFFSET: u64 = 64 + 56; // ELF header + program header

/// Per eval's `init_statics`: every slot occupies 8 bytes regardless
/// of payload type. U8 slots have the byte in the low position and 7
/// zero pad bytes; U32 has 4 payload + 4 pad. This uniform layout is
/// what `LoadDyn` / `StoreDyn` assume (slot index → offset = idx*8).
const SLOT_BYTES: usize = 8;

/// Each allocation (static and dynamic) is prefixed by an 8-byte
/// size header (the byte size of the user data). `cow_resize_dyn`
/// reads this header to know how many bytes to copy.
const SIZE_HEADER_BYTES: usize = 8;

fn static_payload_bytes(slots: &[StaticSlot]) -> usize {
    slots.len() * SLOT_BYTES
}

fn static_total_bytes(slots: &[StaticSlot]) -> usize {
    SIZE_HEADER_BYTES + static_payload_bytes(slots)
}

/// Round `n` up to the next multiple of 8.
fn round_up_8(n: u64) -> u64 {
    (n + 7) & !7
}

/// Compute the file offset of each static's HEADER, relative to the
/// start of the data section. Each static is `8 + N*8` bytes
/// (size header + N 8-byte slots), already 8-byte aligned.
fn static_offsets(module: &Module) -> Vec<u64> {
    let mut offsets = Vec::with_capacity(module.statics.len());
    let mut cumulative = 0_u64;
    for obj in &module.statics {
        offsets.push(cumulative);
        cumulative += static_total_bytes(&obj.slots) as u64;
    }
    offsets
}

/// Absolute virtual address of the static's USER pointer (skipping the
/// 8-byte size header). `static_ref` and `StaticPtr` slots both
/// resolve to this address.
fn static_vaddr(idx: usize, code_size: u64, offsets: &[u64]) -> u64 {
    LOAD_VADDR + PAYLOAD_FILE_OFFSET + code_size + offsets[idx] + SIZE_HEADER_BYTES as u64
}

/// Serialize one static object: 8-byte size header (payload bytes),
/// then each slot in an 8-byte cell.
fn serialize_one_static(slots: &[StaticSlot], code_size: u64, offsets: &[u64]) -> Vec<u8> {
    let payload_bytes = static_payload_bytes(slots);
    let mut out = vec![0_u8; SIZE_HEADER_BYTES + payload_bytes];
    // Header at offset 0: u64 with payload size.
    out[0..8].copy_from_slice(&(payload_bytes as u64).to_le_bytes());
    // Slots follow.
    for (i, slot) in slots.iter().enumerate() {
        let s = SIZE_HEADER_BYTES + i * SLOT_BYTES;
        match slot {
            StaticSlot::U8(b) => out[s] = *b,
            StaticSlot::U32(w) => out[s..s + 4].copy_from_slice(&w.to_le_bytes()),
            StaticSlot::U64(w) => out[s..s + 8].copy_from_slice(&w.to_le_bytes()),
            StaticSlot::I64(w) => out[s..s + 8].copy_from_slice(&w.to_le_bytes()),
            StaticSlot::StaticPtr(target_idx) => {
                let va = static_vaddr(*target_idx, code_size, offsets);
                out[s..s + 8].copy_from_slice(&va.to_le_bytes());
            }
        }
    }
    out
}

/// Build the `DataItem` list for the emit pass. Each static becomes
/// one labelled blob; trailing zero-pad bytes are appended to the
/// preceding item to bring the *next* item to 8-byte alignment.
/// (Putting the pad on the previous item keeps each `Label::Data(idx)`
/// pointing at the static's true start.)
#[must_use]
pub fn data_items(module: &Module, code_size: u64) -> Vec<super::mir::DataItem> {
    let offsets = static_offsets(module);
    let mut items = Vec::with_capacity(module.statics.len());
    for (idx, obj) in module.statics.iter().enumerate() {
        let bytes = serialize_one_static(&obj.slots, code_size, &offsets);
        items.push(super::mir::DataItem {
            label: Label::Data(idx as u32),
            bytes,
            // Skip the 8-byte size header so `Label::Data(idx)` points
            // at the user pointer. `cow_resize_dyn` reads the size by
            // computing user_ptr - 8.
            label_offset: SIZE_HEADER_BYTES as u32,
        });
    }
    items
}
