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
}

#[derive(Clone, Debug)]
pub enum MInst {
    /// `MOVZ Xd, #imm16, LSL #0` — load a 16-bit unsigned immediate.
    MovImm { rd: VReg, imm: u16 },
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
    /// `ADD Xd, Xn, #imm` — unshifted 12-bit immediate add.
    AddImm { rd: VReg, rn: VReg, imm: u16 },
    /// `SUB Xd, Xn, #imm` — unshifted 12-bit immediate subtract.
    SubImm { rd: VReg, rn: VReg, imm: u16 },
    /// `ADD Xd, Xn, Xm` — register-register add.
    AddReg { rd: VReg, rn: VReg, rm: VReg },
    /// `RET` — return via X30/LR.
    Ret,
    /// `SVC #imm` — supervisor call.
    Svc { imm: u16 },
    /// `BRK #imm` — trap. Placed after non-returning syscalls as a
    /// crash-fast landing pad in case control somehow flows past.
    Brk { imm: u16 },
}

/// A blob of bytes addressable by `Label::Data(idx)`.
#[derive(Clone, Debug)]
pub struct DataItem {
    pub label: Label,
    pub bytes: Vec<u8>,
}
