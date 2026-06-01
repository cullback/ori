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

/// Register policy for Phase 5a:
///   x0          — first param (args), syscall arg 0, return reg
///   x1          — second param (input), syscall arg 1
///   x2..x7      — syscall args (transient)
///   x8          — syscall number
///   x9..x14     — SSA value vregs (dense from FIRST_FREE_VREG)
///   x19..x21    — scratch held by the entry shim
///   x28         — reserved: bump pointer for the heap arena
///   x29, x30    — frame pointer / link register, untouched
///   sp          — stack pointer, untouched
///
/// With this layout, functions with ≤ ~6 simultaneous live SSA values
/// fit; anything bigger needs real regalloc.
const FIRST_FREE_VREG: u8 = 9;
const HEAP_BUMP_REG: VReg = VReg(28);

/// Map each SSA Value to a virtual register. Function params get
/// pinned to x0, x1, ... per the calling convention; the rest are
/// dense from FIRST_FREE_VREG.
fn assign_vregs(module: &Module) -> HashMap<usize, VReg> {
    let func = module
        .functions
        .get(&module.entry)
        .unwrap_or_else(|| panic!("entry function {} not found", module.entry));

    let mut map = HashMap::new();
    let mut next = FIRST_FREE_VREG;

    // Pin function params to their incoming registers (x0, x1, ...).
    for (i, p) in func.params.iter().enumerate() {
        assert!(i < 8, "Phase 5a: ≤8 function params (would need stack-passed args)");
        #[expect(clippy::cast_possible_truncation, reason = "i < 8")]
        let phys = VReg(i as u8);
        map.insert(p.id, phys);
    }

    let assign = |id: usize, map: &mut HashMap<usize, VReg>, next: &mut u8| {
        map.entry(id).or_insert_with(|| {
            assert!(*next < HEAP_BUMP_REG.0, "Phase 5a: too many live SSA values; needs stack regalloc");
            let v = VReg(*next);
            *next += 1;
            v
        });
    };

    for block in func.blocks.values() {
        for p in &block.params {
            assign(p.id, &mut map, &mut next);
        }
        for inst in &block.insts {
            for d in inst.dests() {
                assign(d.id, &mut map, &mut next);
            }
        }
    }
    map
}

fn vreg_of(v: Value, vmap: &HashMap<usize, VReg>) -> VReg {
    *vmap
        .get(&v.id)
        .unwrap_or_else(|| panic!("SSA value v{} has no vreg assignment", v.id))
}

/// Lower one SSA instruction. Pushes zero or more MIR ops.
fn lower_inst(inst: &Inst, vmap: &HashMap<usize, VReg>, out: &mut Vec<MInst>) {
    match inst {
        Inst::StaticRef(dest, idx) => {
            out.push(MInst::AdrLabel {
                rd: vreg_of(*dest, vmap),
                label: Label::Data(*idx as u32),
            });
        }
        Inst::RcInc(_) | Inst::RcDec(_) => {
            // No-op until Phase 5e introduces a real refcount runtime.
            // The bump allocator never frees, so leaks are correct-but-leaky.
        }
        Inst::Const(dest, bits) => {
            // 16-bit immediate fast path; widening with MOVK comes later.
            assert!(*bits <= u64::from(u16::MAX), "Phase 5a: Const {bits} exceeds 16-bit movz");
            out.push(MInst::MovImm {
                rd: vreg_of(*dest, vmap),
                imm: *bits as u16,
            });
        }
        Inst::Alloc(dest, size) => {
            // result = bump_ptr; bump_ptr += size_8aligned
            let dest_v = vreg_of(*dest, vmap);
            out.push(MInst::MovReg { rd: dest_v, rs: HEAP_BUMP_REG });
            let aligned = ((*size + 7) & !7) as u32;
            out.push(MInst::AddImm { rd: HEAP_BUMP_REG, rn: HEAP_BUMP_REG, imm: aligned });
        }
        Inst::Store(ptr, offset, val) => {
            assert!(*offset <= 0x7FF8, "Phase 5a: Store offset {offset} out of range");
            assert!(offset.is_multiple_of(8), "Phase 5a: Store offset must be 8-aligned");
            out.push(MInst::StrImm64 {
                rt: vreg_of(*val, vmap),
                rn: vreg_of(*ptr, vmap),
                byte_offset: *offset as u32,
            });
        }
        Inst::Load(dest, ptr, offset) => {
            assert!(*offset <= 0x7FF8, "Phase 5a: Load offset {offset} out of range");
            assert!(offset.is_multiple_of(8), "Phase 5a: Load offset must be 8-aligned");
            out.push(MInst::LdrImm64 {
                rt: vreg_of(*dest, vmap),
                rn: vreg_of(*ptr, vmap),
                byte_offset: *offset as u32,
            });
        }
        Inst::BinOp(dest, op, lhs, rhs) => {
            // Phase 5b: only equality (used by Switch on a bool) is wired
            // up via cmp + cset. Other ops land in Phase 5d.
            match op {
                BinaryOp::Eq => {
                    out.push(MInst::CmpReg { rn: vreg_of(*lhs, vmap), rm: vreg_of(*rhs, vmap) });
                    out.push(MInst::CSet { rd: vreg_of(*dest, vmap), cond: Cond::Eq });
                }
                other => panic!("Phase 5b: unsupported BinOp {other:?}"),
            }
        }
        other => panic!("Phase 5b: unsupported SSA inst: {other:?}"),
    }
}

/// Sentinel block index used for the runtime-shim "exit" landing pad.
/// Every `Return` lowers to a jump to this label, where the post-main
/// shim begins. Real block ids start at 0; we pick a high one out of
/// the way.
const EXIT_BLOCK_LABEL: u32 = 0xFFFF_FFFE;

/// Emit moves to set up a destination block's params from an edge's args.
/// Naive: emit one MovReg per pair, in order. This is correct when no
/// destination vreg appears as a source in another pair (otherwise we'd
/// need a swap chain). For our hello-world-class programs this trivially
/// holds since block params get distinct vregs.
fn emit_edge_moves(
    edge: &BlockEdge,
    dest_block: BlockId,
    func: &Function,
    vmap: &HashMap<usize, VReg>,
    out: &mut Vec<MInst>,
) {
    let dest = func.blocks.get(&dest_block).expect("edge to nonexistent block");
    assert_eq!(edge.args.len(), dest.params.len(), "edge arity mismatch");
    for (arg, param) in edge.args.iter().zip(&dest.params) {
        let src = vreg_of(*arg, vmap);
        let dst = vreg_of(*param, vmap);
        if src != dst {
            out.push(MInst::MovReg { rd: dst, rs: src });
        }
    }
}

fn block_label(bid: BlockId) -> Label {
    Label::Block(bid.0 as u32)
}

/// Lower a terminator. Adds moves for outgoing edge block-params and
/// then a B / B.cond / chain-of-comparisons depending on the kind.
fn lower_terminator(
    term: &Terminator,
    func: &Function,
    vmap: &HashMap<usize, VReg>,
    out: &mut Vec<MInst>,
) {
    match term {
        Terminator::Return(vs) => {
            assert_eq!(vs.len(), 1, "Phase 5b: only single-value Return supported");
            let src = vreg_of(vs[0], vmap);
            if src != VReg(0) {
                out.push(MInst::MovReg { rd: VReg(0), rs: src });
            }
            out.push(MInst::B { target: Label::Block(EXIT_BLOCK_LABEL) });
        }
        Terminator::Jump(edge) => {
            emit_edge_moves(edge, edge.target, func, vmap, out);
            out.push(MInst::B { target: block_label(edge.target) });
        }
        Terminator::Branch { cond, then_edge, else_edge } => {
            // cmp cond, #0; b.ne <then>; (fallthrough to else)
            let cond_v = vreg_of(*cond, vmap);
            out.push(MInst::CmpImm { rn: cond_v, imm: 0 });
            // Plan: emit a fresh synthetic block id for the then-thunk
            // (param moves + b target). For now keep it linear:
            // b.ne to the THEN moves, fall through to ELSE moves.
            // We can't easily emit anonymous synthetic blocks without
            // an id scheme. The simplest correct shape is:
            //
            //   cmp cond, #0
            //   b.ne taken_thunk
            //   <else moves>
            //   b else_target
            //   taken_thunk: <then moves> ; b then_target
            //
            // We synthesize a unique block id by combining the source
            // block id (encoded as the high bits) with the sense bit.
            let thunk_id = synth_branch_thunk_id(then_edge.target, /*then_sense*/ true);
            out.push(MInst::BCond { cond: Cond::Ne, target: Label::Block(thunk_id) });
            emit_edge_moves(else_edge, else_edge.target, func, vmap, out);
            out.push(MInst::B { target: block_label(else_edge.target) });
            out.push(MInst::BlockStart { idx: thunk_id });
            emit_edge_moves(then_edge, then_edge.target, func, vmap, out);
            out.push(MInst::B { target: block_label(then_edge.target) });
        }
        Terminator::SwitchInt { scrutinee, arms, default } => {
            let s_v = vreg_of(*scrutinee, vmap);
            for (i, (val, edge)) in arms.iter().enumerate() {
                let val_u32 = u32::try_from(*val).expect("Phase 5b: switch arm value > u32");
                out.push(MInst::CmpImm { rn: s_v, imm: val_u32 });
                let thunk_id = synth_switch_thunk_id(edge.target, i as u32);
                out.push(MInst::BCond { cond: Cond::Eq, target: Label::Block(thunk_id) });
            }
            match default {
                Some(edge) => {
                    emit_edge_moves(edge, edge.target, func, vmap, out);
                    out.push(MInst::B { target: block_label(edge.target) });
                }
                None => {
                    // No default in our test programs — but the SSA
                    // always provides exhaustive coverage. Insert a
                    // crash-fast trap as defensive measure.
                    out.push(MInst::Brk { imm: 0 });
                }
            }
            // Emit each arm's thunk
            for (i, (_, edge)) in arms.iter().enumerate() {
                let thunk_id = synth_switch_thunk_id(edge.target, i as u32);
                out.push(MInst::BlockStart { idx: thunk_id });
                emit_edge_moves(edge, edge.target, func, vmap, out);
                out.push(MInst::B { target: block_label(edge.target) });
            }
        }
    }
}

/// Synthesize a unique block-label id for a Branch's "then-thunk".
/// Reserves the high bit so it can't collide with real block ids
/// (which are small `usize`s).
fn synth_branch_thunk_id(target: BlockId, then_sense: bool) -> u32 {
    let base = (target.0 as u32) & 0x0000_FFFF;
    let sense = u32::from(then_sense);
    0x8000_0000 | (sense << 16) | base
}

/// Synthesize a unique block-label id for a Switch arm's thunk.
fn synth_switch_thunk_id(target: BlockId, arm_idx: u32) -> u32 {
    let base = (target.0 as u32) & 0x0000_FFFF;
    0xC000_0000 | (arm_idx << 16) | base
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

/// Lower module → MIR. Returns the MIR stream; the caller pairs it
/// with `serialize_statics` for the data section.
#[must_use]
pub fn lower_to_mir(module: &Module) -> Vec<MInst> {
    let vmap = assign_vregs(module);
    let func = module.functions.get(&module.entry).unwrap();

    let mut out = entry_shim();
    // Emit each block with a BlockStart label so terminators can target it.
    for (bid, block) in &func.blocks {
        out.push(MInst::BlockStart { idx: bid.0 as u32 });
        for inst in &block.insts {
            lower_inst(inst, &vmap, &mut out);
        }
        lower_terminator(&block.terminator, func, &vmap, &mut out);
    }

    out.extend(runtime_shim_with_label());

    // Pad the code stream to an 8-byte boundary so the data section
    // that immediately follows (with U64 / pointer slots) is naturally
    // aligned for `ldr Xt, [Xn]` which traps on misaligned addresses.
    let code_bytes: usize = out
        .iter()
        .filter(|i| !matches!(i, MInst::BlockStart { .. }))
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
