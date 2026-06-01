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

/// Function-name → label-index lookup. Built once for the whole module.
fn function_index_map(module: &Module) -> HashMap<String, u32> {
    let mut map = HashMap::new();
    for (idx, name) in module.functions.keys().enumerate() {
        #[expect(clippy::cast_possible_truncation, reason = "<= u32::MAX functions")]
        map.insert(name.clone(), idx as u32);
    }
    map
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

/// Emit `str Xreg, [sp, #slot]` for the value `v`.
fn emit_store(v: Value, reg: VReg, frame: &Frame, out: &mut Vec<MInst>) {
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
    out: &mut Vec<MInst>,
) {
    match inst {
        Inst::StaticRef(dest, idx) => {
            out.push(MInst::AdrLabel { rd: SCRATCH_C, label: Label::Data(*idx as u32) });
            emit_store(*dest, SCRATCH_C, frame, out);
        }
        Inst::RcInc(_) | Inst::RcDec(_) => {
            // No-op until a real refcount runtime exists.
        }
        Inst::Const(dest, bits) => {
            assert!(*bits <= u64::from(u16::MAX), "Const {bits} exceeds 16-bit movz");
            out.push(MInst::MovImm { rd: SCRATCH_C, imm: *bits as u16 });
            emit_store(*dest, SCRATCH_C, frame, out);
        }
        Inst::Alloc(dest, size) => {
            // result = bump_ptr; bump_ptr += aligned_size
            out.push(MInst::MovReg { rd: SCRATCH_C, rs: HEAP_BUMP_REG });
            let aligned = ((*size + 7) & !7) as u32;
            out.push(MInst::AddImm { rd: HEAP_BUMP_REG, rn: HEAP_BUMP_REG, imm: aligned });
            emit_store(*dest, SCRATCH_C, frame, out);
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
            emit_store(*dest, SCRATCH_C, frame, out);
        }
        Inst::BinOp(dest, op, lhs, rhs) => {
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
                other => panic!("Phase 5e: unsupported BinOp {other:?}"),
            }
            emit_store(*dest, SCRATCH_C, frame, out);
        }
        Inst::Call { results, target, args } => {
            assert!(args.len() <= 8, "Phase 5e: >8 args needs stack-passed args");
            assert!(results.len() <= 8, "Phase 5e: >8 return values needs stack-passed returns");
            // Load args directly into x0..xN (calling-convention regs).
            for (i, arg) in args.iter().enumerate() {
                #[expect(clippy::cast_possible_truncation, reason = "≤ 8 args")]
                let target_reg = VReg(i as u8);
                emit_load(*arg, target_reg, frame, out);
            }
            let idx = *func_idx.get(target).unwrap_or_else(|| {
                panic!("Phase 5e: Call to unknown function {target}")
            });
            out.push(MInst::Bl { target: Label::Func(idx) });
            // Store return values from x0..xM into their slots.
            for (i, r) in results.iter().enumerate() {
                #[expect(clippy::cast_possible_truncation, reason = "≤ 8 returns")]
                let src_reg = VReg(i as u8);
                emit_store(*r, src_reg, frame, out);
            }
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
    out: &mut Vec<MInst>,
) {
    let dest = func.blocks.get(&dest_block).expect("edge to nonexistent block");
    assert_eq!(edge.args.len(), dest.params.len(), "edge arity mismatch");
    for (arg, param) in edge.args.iter().zip(&dest.params) {
        if slot_of(*arg, frame) == slot_of(*param, frame) {
            continue;
        }
        emit_load(*arg, SCRATCH_A, frame, out);
        emit_store(*param, SCRATCH_A, frame, out);
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
    out: &mut Vec<MInst>,
) {
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
            emit_edge_moves(edge, edge.target, func, frame, out);
            out.push(MInst::B { target: block_label(func_idx, edge.target) });
        }
        Terminator::Branch { cond, then_edge, else_edge } => {
            emit_load(*cond, SCRATCH_A, frame, out);
            out.push(MInst::CmpImm { rn: SCRATCH_A, imm: 0 });
            let thunk_id = synth_branch_thunk_id(func_idx, then_edge.target);
            out.push(MInst::BCond { cond: Cond::Ne, target: Label::Block(thunk_id) });
            emit_edge_moves(else_edge, else_edge.target, func, frame, out);
            out.push(MInst::B { target: block_label(func_idx, else_edge.target) });
            out.push(MInst::BlockStart { idx: thunk_id });
            emit_edge_moves(then_edge, then_edge.target, func, frame, out);
            out.push(MInst::B { target: block_label(func_idx, then_edge.target) });
        }
        Terminator::SwitchInt { scrutinee, arms, default } => {
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
                    emit_edge_moves(edge, edge.target, func, frame, out);
                    out.push(MInst::B { target: block_label(func_idx, edge.target) });
                }
                None => out.push(MInst::Brk { imm: 0 }),
            }
            for (i, (_, edge)) in arms.iter().enumerate() {
                #[expect(clippy::cast_possible_truncation, reason = "≤ 8 arms in practice")]
                let thunk_id = synth_switch_thunk_id(func_idx, edge.target, i as u32);
                out.push(MInst::BlockStart { idx: thunk_id });
                emit_edge_moves(edge, edge.target, func, frame, out);
                out.push(MInst::B { target: block_label(func_idx, edge.target) });
            }
        }
    }
}

/// Emit `sub sp, sp, #FRAME`; if non-leaf, save x30 at `lr_offset`.
/// Then spill each function parameter from x0..xN into its slot.
fn emit_prologue(func: &Function, frame: &Frame, out: &mut Vec<MInst>) {
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
        emit_store(*p, src, frame, out);
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
/// Result pointer in x0. Hardcoded for `Result(Str, Str)`:
///   x0 = result_ptr
///   ldr x1, [x0, #0]    ; tag (0=Ok, 1=Err)
///   ldr x0, [x0, #8]    ; payload_ptr (heap obj containing the Str ptr)
///   ldr x0, [x0, #0]    ; str_ptr (the List(U8) header)
///   ldr x2, [x0, #0]    ; len
///   ldr x1, [x0, #16]   ; data ptr (raw bytes)
///   mov x0, #1          ; fd = stdout
///   mov x8, #64         ; write syscall
///   svc #0
///   mov x0, #0          ; exit 0 (always; Err handling deferred)
///   mov x8, #94         ; exit_group
///   svc #0
fn runtime_shim() -> Vec<MInst> {
    vec![
        // Save the str_ptr in x3 while we walk through; we need both
        // len and data from it.
        MInst::LdrImm64 { rt: VReg(1), rn: VReg(0), byte_offset: 0 },  // tag (ignored, kept for Phase 5)
        MInst::LdrImm64 { rt: VReg(0), rn: VReg(0), byte_offset: 8 },  // x0 = payload_ptr
        MInst::LdrImm64 { rt: VReg(0), rn: VReg(0), byte_offset: 0 },  // x0 = str_ptr
        MInst::LdrImm64 { rt: VReg(2), rn: VReg(0), byte_offset: 0 },  // x2 = len
        MInst::LdrImm64 { rt: VReg(1), rn: VReg(0), byte_offset: 16 }, // x1 = data ptr
        MInst::MovImm { rd: VReg(0), imm: 1 },                          // fd = stdout
        MInst::MovImm { rd: VReg(8), imm: 64 },                         // write syscall
        MInst::Svc { imm: 0 },
        MInst::MovImm { rd: VReg(0), imm: 0 },                          // exit code
        MInst::MovImm { rd: VReg(8), imm: 94 },                         // exit_group
        MInst::Svc { imm: 0 },
        MInst::Brk { imm: 0 },                                          // unreachable
    ]
}

/// Heap arena size (mmap'd at startup). Layout within the arena:
///   [0 .. STDIN_BUF_SIZE)               : stdin buffer
///   [STDIN_BUF_SIZE .. +24)              : input Str header (len, cap, data)
///   [STDIN_BUF_SIZE+24 .. ARENA_SIZE)    : bump-allocated heap
///
/// Both sizes must fit in a 16-bit movz immediate.
const ARENA_SIZE: u16 = 0xF000; // 60 KiB
const STDIN_BUF_SIZE: u16 = 0x1000; // 4 KiB

/// Generate the `_start` entry shim that runs before `__main`'s body:
///   1. mmap the arena.
///   2. read(0, arena, STDIN_BUF_SIZE).
///   3. Build the input Str header inside the arena.
///   4. Place args (= 0, unused), input ptr, and bump pointer into
///      x0, x1, x28 respectively.
fn entry_shim() -> Vec<MInst> {
    // Pick callee-saved scratch regs the shim alone uses.
    let arena = VReg(19); // base of the mmap region
    let strh = VReg(20); // address of the input Str header
    let bytes_read = VReg(21); // result of read(2)

    vec![
        // mmap(addr=0, len=ARENA_SIZE, prot=R|W, flags=PRIVATE|ANON, fd=-1, off=0)
        MInst::MovImm { rd: VReg(0), imm: 0 },        // addr
        MInst::MovImm { rd: VReg(1), imm: ARENA_SIZE }, // len
        MInst::MovImm { rd: VReg(2), imm: 3 },        // prot = PROT_READ | PROT_WRITE
        MInst::MovImm { rd: VReg(3), imm: 0x22 },     // flags = MAP_PRIVATE | MAP_ANONYMOUS
        MInst::MovInv { rd: VReg(4), imm: 0 },        // fd = -1
        MInst::MovImm { rd: VReg(5), imm: 0 },        // offset
        MInst::MovImm { rd: VReg(8), imm: 222 },      // mmap syscall
        MInst::Svc { imm: 0 },
        // x0 now holds the arena base; save into `arena`.
        MInst::MovReg { rd: arena, rs: VReg(0) },

        // read(fd=0, buf=arena, count=STDIN_BUF_SIZE)
        MInst::MovImm { rd: VReg(0), imm: 0 },                  // stdin
        MInst::MovReg { rd: VReg(1), rs: arena },               // buf
        MInst::MovImm { rd: VReg(2), imm: STDIN_BUF_SIZE },     // count
        MInst::MovImm { rd: VReg(8), imm: 63 },                 // read syscall
        MInst::Svc { imm: 0 },
        // x0 = bytes read; stash into `bytes_read`.
        MInst::MovReg { rd: bytes_read, rs: VReg(0) },

        // strh = arena + STDIN_BUF_SIZE
        MInst::AddImm { rd: strh, rn: arena, imm: u32::from(STDIN_BUF_SIZE) },

        // Store the Str header fields: [len, cap, data_ptr].
        MInst::StrImm64 { rt: bytes_read, rn: strh, byte_offset: 0 },  // len
        MInst::MovImm { rd: VReg(2), imm: STDIN_BUF_SIZE },             // tmp = cap value
        MInst::StrImm64 { rt: VReg(2), rn: strh, byte_offset: 8 },     // cap
        MInst::StrImm64 { rt: arena, rn: strh, byte_offset: 16 },      // data

        // Empty args List header at strh + 24 — 3 zero u64 slots
        // (len=0, cap=0, data=null). We write via XZR (= VReg(31)).
        MInst::AddImm { rd: VReg(2), rn: strh, imm: 24 },         // tmp = args ptr
        MInst::StrImm64 { rt: VReg(31), rn: VReg(2), byte_offset: 0 },
        MInst::StrImm64 { rt: VReg(31), rn: VReg(2), byte_offset: 8 },
        MInst::StrImm64 { rt: VReg(31), rn: VReg(2), byte_offset: 16 },

        // Bump pointer (X28) = strh + 24 + 24. Heap starts after the
        // args header.
        MInst::AddImm { rd: HEAP_BUMP_REG, rn: strh, imm: 48 },

        // Set up __main's params: x0 = args ptr, x1 = input ptr.
        MInst::MovReg { rd: VReg(0), rs: VReg(2) },
        MInst::MovReg { rd: VReg(1), rs: strh },
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

    if !is_entry {
        out.push(MInst::FuncStart { idx: func_idx });
    }

    emit_prologue(func, &frame, out);

    for (bid, block) in &func.blocks {
        let combined = match block_label(func_idx, *bid) {
            Label::Block(c) => c,
            _ => unreachable!(),
        };
        out.push(MInst::BlockStart { idx: combined });
        for inst in &block.insts {
            lower_inst(inst, &frame, func_idx_map, out);
        }
        lower_terminator(&block.terminator, func, func_idx, is_entry, &frame, out);
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

    for (name, func) in &module.functions {
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

    let data = vec![DataItem { label, bytes: data_bytes }];
    (mir, data)
}

// ---------- Static data emission ----------

const LOAD_VADDR: u64 = 0x0040_0000;
const PAYLOAD_FILE_OFFSET: u64 = 64 + 56; // ELF header + program header

fn slot_byte_size(slot: &StaticSlot) -> usize {
    match slot {
        StaticSlot::U8(_) => 1,
        StaticSlot::U32(_) => 4,
        StaticSlot::U64(_) | StaticSlot::I64(_) | StaticSlot::StaticPtr(_) => 8,
    }
}

fn static_byte_size(slots: &[StaticSlot]) -> usize {
    slots.iter().map(slot_byte_size).sum()
}

/// Round `n` up to the next multiple of 8.
fn round_up_8(n: u64) -> u64 {
    (n + 7) & !7
}

/// Compute the file offset of each static, relative to the start of
/// the data section. Each static is padded to 8-byte alignment so its
/// `U64` and `StaticPtr` slots load correctly via `ldr` (which traps
/// on misaligned addresses by default on aarch64-linux).
fn static_offsets(module: &Module) -> Vec<u64> {
    let mut offsets = Vec::with_capacity(module.statics.len());
    let mut cumulative = 0_u64;
    for obj in &module.statics {
        offsets.push(cumulative);
        cumulative += static_byte_size(&obj.slots) as u64;
        cumulative = round_up_8(cumulative);
    }
    offsets
}

/// Absolute virtual address of static at `idx`, given the code size
/// (so we can place data after the code in the segment).
fn static_vaddr(idx: usize, code_size: u64, offsets: &[u64]) -> u64 {
    LOAD_VADDR + PAYLOAD_FILE_OFFSET + code_size + offsets[idx]
}

/// Serialize one static object's slots to bytes (no inter-object padding).
fn serialize_one_static(slots: &[StaticSlot], code_size: u64, offsets: &[u64]) -> Vec<u8> {
    let mut out = Vec::with_capacity(static_byte_size(slots));
    for slot in slots {
        match slot {
            StaticSlot::U8(b) => out.push(*b),
            StaticSlot::U32(w) => out.extend_from_slice(&w.to_le_bytes()),
            StaticSlot::U64(w) => out.extend_from_slice(&w.to_le_bytes()),
            StaticSlot::I64(w) => out.extend_from_slice(&w.to_le_bytes()),
            StaticSlot::StaticPtr(target_idx) => {
                let va = static_vaddr(*target_idx, code_size, offsets);
                out.extend_from_slice(&va.to_le_bytes());
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
        let mut bytes = serialize_one_static(&obj.slots, code_size, &offsets);
        // Determine pad to next 8-byte boundary based on the offset
        // table delta.
        let this_start = offsets[idx];
        let next_start = offsets
            .get(idx + 1)
            .copied()
            .unwrap_or_else(|| round_up_8(this_start + static_byte_size(&obj.slots) as u64));
        let want_len = (next_start - this_start) as usize;
        while bytes.len() < want_len {
            bytes.push(0);
        }
        items.push(super::mir::DataItem {
            label: Label::Data(idx as u32),
            bytes,
        });
    }
    items
}
