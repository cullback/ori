//! Pure-fn aarch64 instruction encoders.
//!
//! Each public fn takes operands and returns the 32-bit little-endian
//! word the CPU executes. No allocation, no I/O, no awareness of ELF
//! or Mach-O. Every encoder has a unit test below that locks in the
//! expected bits against values verified with GNU `as` + `objdump`.
//!
//! Grow this file lazily: only encode the instructions the higher
//! layers actually emit. We start with the three hello-world needs.

// Tests below contain many `assert without message` instances; relaxing
// the restriction lint at file scope keeps signal-to-noise readable.
// `dead_code` is allowed because higher phases (1b, 2, 3) will be the
// consumers — these encoders are deliberately built ahead of demand.
#![allow(
    clippy::integer_division,
    clippy::integer_division_remainder_used,
    clippy::arithmetic_side_effects,
    clippy::missing_assert_message,
    clippy::missing_const_for_fn,
    clippy::modulo_arithmetic,
    clippy::separated_literal_suffix,
    clippy::unreadable_literal,
    dead_code
)]

/// A general-purpose aarch64 register, 0..=31.
///
/// 31 means SP in `add`/`sub` contexts and the zero register XZR in
/// most others. Callers track that distinction; the encoder just
/// emits the 5-bit field.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Reg(pub u8);

#[expect(clippy::allow_attributes, reason = "constants are write-rare, read-many")]
#[allow(clippy::doc_markdown, dead_code)]
pub mod regs {
    use super::Reg;
    pub const X0: Reg = Reg(0);
    pub const X1: Reg = Reg(1);
    pub const X2: Reg = Reg(2);
    pub const X3: Reg = Reg(3);
    pub const X4: Reg = Reg(4);
    pub const X5: Reg = Reg(5);
    pub const X6: Reg = Reg(6);
    pub const X7: Reg = Reg(7);
    pub const X8: Reg = Reg(8);
    pub const X16: Reg = Reg(16);
    pub const X17: Reg = Reg(17);
    pub const X29: Reg = Reg(29); // FP
    pub const X30: Reg = Reg(30); // LR
    pub const SP: Reg = Reg(31);
    pub const XZR: Reg = Reg(31);
}

/// Encode `MOVZ Xd, #imm16, LSL #0` — load a 16-bit unsigned immediate
/// into a 64-bit register, clearing the upper bits.
///
/// Bit layout (64-bit MOVZ):
/// ```text
///   31 30 29 28..23 22 21 20.....5 4..0
///    1 1  0 100101  0  0  imm16    Rd
/// ```
#[must_use]
pub fn movz_imm16(rd: Reg, imm: u16) -> u32 {
    debug_assert!(rd.0 < 32, "Rd out of range");
    0xD280_0000 | (u32::from(imm) << 5) | u32::from(rd.0)
}

/// Encode `MOVN Xd, #imm16, LSL #0` — load the bitwise NOT of a 16-bit
/// immediate into a 64-bit register. `MOVN Xd, #0` is the canonical
/// way to load `-1` (= `0xFFFF_FFFF_FFFF_FFFF`).
#[must_use]
pub fn movn_imm16(rd: Reg, imm: u16) -> u32 {
    debug_assert!(rd.0 < 32, "Rd out of range");
    0x9280_0000 | (u32::from(imm) << 5) | u32::from(rd.0)
}

/// Encode `ADR Xd, label` — load `PC + offset` into a 64-bit register.
///
/// `offset` is in bytes from the address of this instruction; the
/// signed 21-bit range is ±1 MiB. Out-of-range values trip a debug
/// assert — callers must split into `ADRP` + `ADD` for longer reach.
///
/// Bit layout:
/// ```text
///   31 30 29 28..24 23.........5 4..0
///    0 immlo 10000  immhi(19)    Rd
/// ```
/// where `imm21 = immhi:immlo` (signed, in bytes).
#[must_use]
#[expect(clippy::cast_sign_loss, reason = "wrapping into 21-bit field is intentional")]
pub fn adr(rd: Reg, offset: i32) -> u32 {
    debug_assert!(rd.0 < 32, "Rd out of range");
    debug_assert!(
        (-(1_i32 << 20_i32)..(1_i32 << 20_i32)).contains(&offset),
        "ADR offset {offset} out of +/-1MiB range"
    );
    let imm21 = (offset as u32) & 0x001F_FFFF;
    let immlo = imm21 & 0x3;
    let immhi = (imm21 >> 2_u32) & 0x0007_FFFF;
    0x1000_0000 | (immlo << 29_u32) | (immhi << 5_u32) | u32::from(rd.0)
}

/// Encode `SVC #imm16` — supervisor call (syscall trap on Linux/macOS).
///
/// Bit layout:
/// ```text
///   31..24   23..21 20.....5 4..0
///   11010100  000   imm16    00001
/// ```
#[must_use]
pub fn svc(imm: u16) -> u32 {
    0xD400_0001 | (u32::from(imm) << 5)
}

/// Encode `MOV Xd, Xs` — register-to-register move.
///
/// Architecturally an alias for `ORR Xd, XZR, Xs`. Used by the
/// selector to shuffle SSA values into the calling-convention
/// argument registers before a `Call`.
#[must_use]
pub fn mov_reg(rd: Reg, rs: Reg) -> u32 {
    debug_assert!(rd.0 < 32 && rs.0 < 32, "register out of range");
    0xAA00_03E0 | (u32::from(rs.0) << 16) | u32::from(rd.0)
}

/// Encode `BRK #imm16` — software breakpoint, terminates the process
/// with SIGTRAP. Used as a "trap-on-unreachable" landing pad after
/// syscalls that shouldn't return (e.g. exit).
#[must_use]
pub fn brk(imm: u16) -> u32 {
    0xD420_0000 | (u32::from(imm) << 5)
}

/// Encode `LDR Xt, [Xn, #imm]` — load 64 bits from `Xn + imm`.
///
/// `byte_offset` must be 8-byte aligned and in `0..=32760`. The
/// encoder asserts both (debug build) and the upper layers should
/// have arranged the layout to fit.
#[must_use]
pub fn ldr_imm64(rt: Reg, rn: Reg, byte_offset: u32) -> u32 {
    debug_assert!(rt.0 < 32 && rn.0 < 32, "register out of range");
    debug_assert!(byte_offset.is_multiple_of(8), "LDR x-reg requires 8-byte aligned offset");
    debug_assert!(byte_offset <= 0x7FF8, "LDR imm offset {byte_offset} out of range");
    let imm12 = byte_offset / 8;
    0xF940_0000 | (imm12 << 10_u32) | (u32::from(rn.0) << 5_u32) | u32::from(rt.0)
}

/// Encode `STR Xt, [Xn, #imm]` — store 64 bits to `Xn + imm`. Same
/// alignment + range constraints as `ldr_imm64`.
#[must_use]
pub fn str_imm64(rt: Reg, rn: Reg, byte_offset: u32) -> u32 {
    debug_assert!(rt.0 < 32 && rn.0 < 32, "register out of range");
    debug_assert!(byte_offset.is_multiple_of(8), "STR x-reg requires 8-byte aligned offset");
    debug_assert!(byte_offset <= 0x7FF8, "STR imm offset {byte_offset} out of range");
    let imm12 = byte_offset / 8;
    0xF900_0000 | (imm12 << 10_u32) | (u32::from(rn.0) << 5_u32) | u32::from(rt.0)
}

/// Encode `ADD Xd, Xn, #imm` — 12-bit immediate add, auto-dispatching
/// between the unshifted and `LSL #12` (4096-multiple) encodings.
///
/// Range: `0..4096` unshifted, or `(N * 4096)` for `N < 4096`. Other
/// values panic — the caller must materialize them in a register and
/// use `add_reg` instead.
#[must_use]
pub fn add_imm(rd: Reg, rn: Reg, imm: u32) -> u32 {
    assert!(rd.0 < 32 && rn.0 < 32, "register out of range");
    let (imm12, sh) = encode_imm12_with_optional_lsl12(imm, "ADD");
    0x9100_0000 | (sh << 22_u32) | (imm12 << 10_u32) | (u32::from(rn.0) << 5_u32) | u32::from(rd.0)
}

/// Encode `SUB Xd, Xn, #imm` — same dispatch policy as `add_imm`.
#[must_use]
pub fn sub_imm(rd: Reg, rn: Reg, imm: u32) -> u32 {
    assert!(rd.0 < 32 && rn.0 < 32, "register out of range");
    let (imm12, sh) = encode_imm12_with_optional_lsl12(imm, "SUB");
    0xD100_0000 | (sh << 22_u32) | (imm12 << 10_u32) | (u32::from(rn.0) << 5_u32) | u32::from(rd.0)
}

/// Shared imm12 / `LSL #12` dispatch for `add_imm`/`sub_imm`.
/// Returns `(imm12_field, sh_field)`.
fn encode_imm12_with_optional_lsl12(imm: u32, op: &str) -> (u32, u32) {
    if imm < 4096 {
        (imm, 0)
    } else if imm < (4096 << 12) && imm.is_multiple_of(4096) {
        (imm >> 12_u32, 1)
    } else {
        panic!("{op} imm {imm} not encodable as imm12 (with optional LSL #12); materialize in a reg instead")
    }
}

/// Encode `ADD Xd, Xn, Xm` — register-register add (no shift).
#[must_use]
pub fn add_reg(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    debug_assert!(rd.0 < 32 && rn.0 < 32 && rm.0 < 32, "register out of range");
    0x8B00_0000 | (u32::from(rm.0) << 16_u32) | (u32::from(rn.0) << 5_u32) | u32::from(rd.0)
}

/// Encode `RET` (defaults to returning via X30/LR).
#[must_use]
pub fn ret() -> u32 {
    0xD65F_03C0
}

#[cfg(test)]
mod tests {
    use super::regs::*;
    use super::*;

    // The expected values below were cross-checked with `as` +
    // `objdump`. See src/codegen/hello.rs for the original assembly
    // listing the hello-world bytes came from.

    #[test]
    fn movz_hello_world_constants() {
        assert_eq!(movz_imm16(X0, 1), 0xD280_0020);
        assert_eq!(movz_imm16(X2, 6), 0xD280_00C2);
        assert_eq!(movz_imm16(X8, 64), 0xD280_0808);
        assert_eq!(movz_imm16(X8, 94), 0xD280_0BC8);
        assert_eq!(movz_imm16(X0, 0), 0xD280_0000);
    }

    #[test]
    fn movz_boundary_imm() {
        assert_eq!(movz_imm16(X0, 0xFFFF), 0xD29F_FFE0);
        assert_eq!(movz_imm16(Reg(31), 0xFFFF), 0xD29F_FFFF);
    }

    #[test]
    fn adr_positive_offset_28() {
        // The exact `adr x1, msg` from hello.rs at offset 4 with
        // msg at offset 32 → +28 byte displacement.
        assert_eq!(adr(X1, 28), 0x1000_00E1);
    }

    #[test]
    fn adr_zero_offset() {
        // adr x0, . → encodes 0 displacement.
        assert_eq!(adr(X0, 0), 0x1000_0000);
    }

    #[test]
    fn adr_negative_offset() {
        // adr x1, -4 → encodes -4 displacement as 21-bit signed.
        // imm21 = -4 as u32 (mod 2^21) = 0x1FFFFC
        // immlo = 0x3 << 29 = 0x6000_0000? No — immlo = bits 1:0 = 0
        // (since -4 = ...11111100). Recompute:
        // -4 & 0x1FFFFF = 0x1FFFFC; immlo = 0, immhi = 0x7FFFF.
        let v = adr(X1, -4);
        assert_eq!(v, 0x10FF_FFE1);
    }

    #[test]
    fn adr_max_positive() {
        // Just inside the +range: (1 << 20) - 4 = 0xFFFFC.
        let off = (1_i32 << 20) - 4;
        // immhi = 0xFFFFC >> 2 & 0x7FFFF = 0x3FFFF
        // immlo = 0xFFFFC & 0x3 = 0
        // encoding = 0x1000_0000 | (0 << 29) | (0x3FFFF << 5) | 0
        //          = 0x1000_0000 | 0x007F_FFE0
        //          = 0x107F_FFE0
        assert_eq!(adr(X0, off), 0x107F_FFE0);
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "ADR offset")]
    fn adr_out_of_range_panics_in_debug() {
        let _ = adr(X0, 1 << 20);
    }

    #[test]
    fn svc_hello_world() {
        assert_eq!(svc(0), 0xD400_0001);
    }

    #[test]
    fn svc_nonzero_imm() {
        // SVC #0x80 — macOS syscall trap. Tested ahead of when we
        // need it because the encoder is target-independent.
        assert_eq!(svc(0x80), 0xD400_1001);
    }

    #[test]
    fn mov_reg_encoding() {
        // Cross-verified with `as`:
        //   mov x0, x1 -> 0xAA0103E0
        //   mov x3, x8 -> 0xAA0803E3
        //   mov x7, xzr -> 0xAA1F03E7
        assert_eq!(mov_reg(X0, X1), 0xAA01_03E0);
        assert_eq!(mov_reg(Reg(3), X8), 0xAA08_03E3);
        assert_eq!(mov_reg(Reg(7), XZR), 0xAA1F_03E7);
    }

    #[test]
    fn brk_encoding() {
        // Cross-verified: brk #0 -> 0xD4200000.
        assert_eq!(brk(0), 0xD420_0000);
    }

    #[test]
    fn ldr_imm64_encoding() {
        // Cross-verified against `as`:
        //   ldr x0, [x1]       -> 0xF9400020
        //   ldr x2, [x3, #8]   -> 0xF9400462
        //   ldr x4, [x5, #16]  -> 0xF94008A4
        //   ldr x16, [x0, #4088] -> 0xF947FC10
        assert_eq!(ldr_imm64(X0, X1, 0), 0xF940_0020);
        assert_eq!(ldr_imm64(Reg(2), Reg(3), 8), 0xF940_0462);
        assert_eq!(ldr_imm64(Reg(4), Reg(5), 16), 0xF940_08A4);
        assert_eq!(ldr_imm64(X16, X0, 4088), 0xF947_FC10);
    }

    #[test]
    fn str_imm64_encoding() {
        // STR uses the same layout as LDR with the top bit flipped:
        // LDR top byte is 0xF9 and bit 22 indicates load (=1).
        // STR has bit 22 = 0 → 0xF9 → 0xF9 → opcode delta moves
        // base from 0xF940 to 0xF900.
        assert_eq!(str_imm64(X0, X1, 0), 0xF900_0020);
        assert_eq!(str_imm64(Reg(2), Reg(3), 8), 0xF900_0462);
    }

    #[test]
    fn add_imm_encoding() {
        // Cross-verified: add x0, x1, #16 -> 0x91004020.
        assert_eq!(add_imm(X0, X1, 16), 0x9100_4020);
        // add sp, sp, #32 (sp == reg 31).
        assert_eq!(add_imm(SP, SP, 32), 0x9100_83FF);
    }

    #[test]
    fn add_imm_lsl12_encoding() {
        // imm = 4096 fits as `add Xd, Xn, #1, LSL #12`. The encoder
        // must take the shifted path, not silently overflow into the
        // sh bit. Cross-verified with `as`:
        //   add x20, x19, #4096 -> 0x91400674
        //   add x0,  x1,  #8192 -> 0x91400820
        assert_eq!(add_imm(Reg(20), Reg(19), 4096), 0x9140_0674);
        assert_eq!(add_imm(X0, X1, 8192), 0x9140_0820);
    }

    #[test]
    #[should_panic(expected = "not encodable")]
    fn add_imm_panics_on_non_encodable() {
        let _ = add_imm(X0, X1, 4097);
    }

    #[test]
    fn sub_imm_encoding() {
        // Cross-verified: sub sp, sp, #32 -> 0xD10083FF.
        assert_eq!(sub_imm(SP, SP, 32), 0xD100_83FF);
    }

    #[test]
    fn add_reg_encoding() {
        // Cross-verified: add x0, x1, x2 -> 0x8B020020.
        assert_eq!(add_reg(X0, X1, Reg(2)), 0x8B02_0020);
    }

    #[test]
    fn ret_encoding() {
        // Cross-verified: ret -> 0xD65F03C0 (Xn defaults to X30 / LR).
        assert_eq!(ret(), 0xD65F_03C0);
    }

    #[test]
    fn movn_encoding() {
        // Cross-verified: movn x4, #0 -> 0x92800004 (loads -1).
        assert_eq!(movn_imm16(Reg(4), 0), 0x9280_0004);
        assert_eq!(movn_imm16(X0, 0), 0x9280_0000);
    }

    // Watermark integration: emitting the hello-world code via these
    // encoders must produce the same 32 bytes as hello.rs's CODE table.
    #[test]
    fn hello_world_code_via_encoders() {
        let code: [u32; 8] = [
            movz_imm16(X0, 1),
            adr(X1, 28),
            movz_imm16(X2, 6),
            movz_imm16(X8, 64),
            svc(0),
            movz_imm16(X0, 0),
            movz_imm16(X8, 94),
            svc(0),
        ];
        // Compare against the canonical hand-written table.
        let expected: [u32; 8] = [
            0xD280_0020, 0x1000_00E1, 0xD280_00C2, 0xD280_0808,
            0xD400_0001, 0xD280_0000, 0xD280_0BC8, 0xD400_0001,
        ];
        assert_eq!(code, expected);
    }
}
