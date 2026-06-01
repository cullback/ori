//! Machine IR for aarch64.
//!
//! One `MInst` per native instruction, with virtual registers and
//! symbolic labels for things the encoder needs resolved addresses
//! for. Layout/displacement happens in `emit`; selection from SSA
//! happens in `select` (Phase 3).
//!
//! Today only the three opcodes hello-world needs are wired up; grow
//! lazily with the encoder library.

#![allow(clippy::pub_with_shorthand, dead_code)]

/// Virtual register. Trivial mapping for now: `VReg(n)` → physical
/// `X(n)`. Real regalloc lands in Phase 3+; until then there is no
/// register pressure (hello world uses x0/x1/x2/x8 only).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct VReg(pub u8);

/// A symbolic location resolved at emit time.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Label {
    /// Index into the function's data table.
    Data(u32),
    /// Block identifier — resolved by the layout pass to the byte
    /// offset of the matching `BlockStart` pseudo-instruction.
    Block(u32),
    /// Function identifier (index into the module's function table) —
    /// resolved by the layout pass to the byte offset of the function's
    /// `FuncStart` pseudo-instruction.
    Func(u32),
}

#[derive(Clone, Debug)]
pub enum MInst {
    /// `MOVZ Xd, #imm16, LSL #0` — load a 16-bit unsigned immediate.
    MovImm { rd: VReg, imm: u16 },
    /// `MOVN Xd, #imm16, LSL #0` — load NOT(imm); `MOVN ..., #0` = -1.
    MovInv { rd: VReg, imm: u16 },
    /// `MOVK Xd, #imm16, LSL #(shift)` — keep other bits, patch a 16-bit chunk.
    MovkImm { rd: VReg, imm: u16, shift: u8 },
    /// `MOV Xd, Xs` — register-to-register move. Used by the selector
    /// to shuffle SSA values into calling-convention slots.
    MovReg { rd: VReg, rs: VReg },
    /// `ADR Xd, label` — load PC-relative address of the label.
    AdrLabel { rd: VReg, label: Label },
    /// `LDR Xt, [Xn, #imm]` — load 64 bits from `Xn + imm`. `imm`
    /// must be 8-byte aligned and ≤ 32760.
    LdrImm64 { rt: VReg, rn: VReg, byte_offset: u32 },
    /// `STR Xt, [Xn, #imm]` — store 64 bits.
    StrImm64 { rt: VReg, rn: VReg, byte_offset: u32 },
    /// `ADD Xd, Xn, #imm` — 12-bit imm (auto-shifts to LSL #12 for
    /// 4096-multiples up to ~16 MiB).
    AddImm { rd: VReg, rn: VReg, imm: u32 },
    /// `SUB Xd, Xn, #imm` — same dispatch policy as `AddImm`.
    SubImm { rd: VReg, rn: VReg, imm: u32 },
    /// `ADD Xd, Xn, Xm` — register-register add.
    AddReg { rd: VReg, rn: VReg, rm: VReg },
    /// `SUB Xd, Xn, Xm`.
    SubReg { rd: VReg, rn: VReg, rm: VReg },
    /// `AND Xd, Xn, Xm`.
    AndReg { rd: VReg, rn: VReg, rm: VReg },
    /// `ORR Xd, Xn, Xm`.
    OrrReg { rd: VReg, rn: VReg, rm: VReg },
    /// `EOR Xd, Xn, Xm` — bitwise XOR.
    EorReg { rd: VReg, rn: VReg, rm: VReg },
    /// `LSL Xd, Xn, Xm` — variable shift left.
    LslReg { rd: VReg, rn: VReg, rm: VReg },
    /// `LSR Xd, Xn, Xm` — variable shift right.
    LsrReg { rd: VReg, rn: VReg, rm: VReg },
    /// `MUL Xd, Xn, Xm`.
    MulReg { rd: VReg, rn: VReg, rm: VReg },
    /// `UDIV Xd, Xn, Xm` — unsigned division.
    UdivReg { rd: VReg, rn: VReg, rm: VReg },
    /// `ADD Xd, Xn, Xm, LSL #3` — indexed addressing for 8-byte slots.
    AddRegLsl3 { rd: VReg, rn: VReg, rm: VReg },
    /// `LDRB Wt, [Xn, #imm]` — zero-extending byte load.
    LdrbImm { rt: VReg, rn: VReg, byte_offset: u16 },
    /// `STRB Wt, [Xn, #imm]` — store low byte.
    StrbImm { rt: VReg, rn: VReg, byte_offset: u16 },
    /// `RET` — return via X30/LR.
    Ret,
    /// `NOP` — filler for code-section alignment padding.
    Nop,
    /// `SVC #imm` — supervisor call.
    Svc { imm: u16 },
    /// `BRK #imm` — trap. Placed after non-returning syscalls as a
    /// crash-fast landing pad in case control somehow flows past.
    Brk { imm: u16 },
    /// `CMP Xn, #imm` — sets flags.
    CmpImm { rn: VReg, imm: u32 },
    /// `CMP Xn, Xm` — sets flags.
    CmpReg { rn: VReg, rm: VReg },
    /// `CSET Xd, cond` — write 1/0 based on flags + condition.
    CSet { rd: VReg, cond: super::encode::Cond },
    /// `CSEL Xd, Xn, Xm, cond` — `Xd = if cond { Xn } else { Xm }`.
    CSel { rd: VReg, rn: VReg, rm: VReg, cond: super::encode::Cond },
    /// `B label` — unconditional branch.
    B { target: Label },
    /// `BL label` — branch + link (function call).
    Bl { target: Label },
    /// `B.cond label` — conditional branch.
    BCond { cond: super::encode::Cond, target: Label },
    /// Pseudo-op: marks where a basic block starts. Emits no bytes;
    /// the layout pass records the byte offset for `Label::Block(idx)`.
    BlockStart { idx: u32 },
    /// Pseudo-op: marks where a function's code starts. Emits no bytes;
    /// records the offset for `Label::Func(idx)`.
    FuncStart { idx: u32 },
}

/// A blob of bytes addressable by `Label::Data(idx)`.
///
/// `label` resolves to `start_of_bytes + label_offset`. For Phase 5f
/// runtime-friendly statics this is 8 so the label points past the
/// 8-byte size header; older code paths (Phase 0/3 hello-worlds) use 0.
#[derive(Clone, Debug)]
pub struct DataItem {
    pub label: Label,
    pub bytes: Vec<u8>,
    pub label_offset: u32,
}
