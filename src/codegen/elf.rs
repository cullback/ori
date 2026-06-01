//! ELF64 container builder for Linux aarch64.
//!
//! Phase 1b: factor the literal bytes from `hello.rs` into a single
//! function that takes `(entry_offset, code, data)` and returns the
//! complete binary. The watermark test below asserts byte-identical
//! reproduction of `hello.rs`'s output when fed the hello-world payload.
//!
//! Layout assumptions for the minimal binary:
//!   - One PT_LOAD segment, R+X, covering the whole file from offset 0.
//!   - Code immediately follows the program header (file offset 120).
//!   - Data immediately follows code.
//!   - Entry point virtual address = LOAD_VADDR + 120 + entry_offset.
//!
//! Section headers are deliberately omitted (e_shoff = 0). The kernel
//! doesn't need them; only the linker would.

#![allow(
    clippy::cast_possible_truncation,
    clippy::doc_markdown,
    clippy::little_endian_bytes,
    clippy::pub_with_shorthand,
    clippy::separated_literal_suffix
)]

const ELF_HDR_SIZE: u64 = 64;
const PHDR_SIZE: u64 = 56;
const PAYLOAD_FILE_OFFSET: u64 = ELF_HDR_SIZE + PHDR_SIZE;
const LOAD_VADDR: u64 = 0x0040_0000;
const PAGE_ALIGN: u64 = 0x0001_0000; // 64 KiB

/// Build a complete static aarch64-linux ELF64 executable.
///
/// `entry_offset` is the byte offset of the entry instruction within
/// `code`. The kernel will jump to `LOAD_VADDR + 120 + entry_offset`
/// after mapping the segment.
#[must_use]
pub fn build(entry_offset: u64, code: &[u8], data: &[u8]) -> Vec<u8> {
    let code_size = code.len() as u64;
    let data_size = data.len() as u64;
    let file_size = PAYLOAD_FILE_OFFSET + code_size + data_size;
    let entry_vaddr = LOAD_VADDR + PAYLOAD_FILE_OFFSET + entry_offset;

    let mut b: Vec<u8> = Vec::with_capacity(file_size as usize);

    // ELF64 header (64 bytes).
    b.extend_from_slice(&[0x7F, b'E', b'L', b'F']);
    b.push(2); // EI_CLASS    = ELFCLASS64
    b.push(1); // EI_DATA     = ELFDATA2LSB
    b.push(1); // EI_VERSION  = EV_CURRENT
    b.push(0); // EI_OSABI    = SYSV
    b.push(0); // EI_ABIVERSION
    b.extend_from_slice(&[0; 7]); // EI_PAD
    b.extend_from_slice(&2_u16.to_le_bytes()); // e_type      = ET_EXEC
    b.extend_from_slice(&0x00B7_u16.to_le_bytes()); // e_machine   = EM_AARCH64
    b.extend_from_slice(&1_u32.to_le_bytes()); // e_version
    b.extend_from_slice(&entry_vaddr.to_le_bytes()); // e_entry
    b.extend_from_slice(&ELF_HDR_SIZE.to_le_bytes()); // e_phoff
    b.extend_from_slice(&0_u64.to_le_bytes()); // e_shoff
    b.extend_from_slice(&0_u32.to_le_bytes()); // e_flags
    b.extend_from_slice(&(ELF_HDR_SIZE as u16).to_le_bytes()); // e_ehsize
    b.extend_from_slice(&(PHDR_SIZE as u16).to_le_bytes()); // e_phentsize
    b.extend_from_slice(&1_u16.to_le_bytes()); // e_phnum
    b.extend_from_slice(&0_u16.to_le_bytes()); // e_shentsize
    b.extend_from_slice(&0_u16.to_le_bytes()); // e_shnum
    b.extend_from_slice(&0_u16.to_le_bytes()); // e_shstrndx

    // Program header (56 bytes).
    b.extend_from_slice(&1_u32.to_le_bytes()); // p_type   = PT_LOAD
    b.extend_from_slice(&5_u32.to_le_bytes()); // p_flags  = PF_R | PF_X
    b.extend_from_slice(&0_u64.to_le_bytes()); // p_offset
    b.extend_from_slice(&LOAD_VADDR.to_le_bytes()); // p_vaddr
    b.extend_from_slice(&LOAD_VADDR.to_le_bytes()); // p_paddr
    b.extend_from_slice(&file_size.to_le_bytes()); // p_filesz
    b.extend_from_slice(&file_size.to_le_bytes()); // p_memsz
    b.extend_from_slice(&PAGE_ALIGN.to_le_bytes()); // p_align

    b.extend_from_slice(code);
    b.extend_from_slice(data);

    debug_assert_eq!(b.len() as u64, file_size, "elf size accounting drifted");
    b
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen::aarch64::encode::regs::*;
    use crate::codegen::aarch64::encode::{adr, movz_imm16, svc};

    /// Hello-world code stream, built via the Phase 1a encoders. The
    /// adr offset is hard-coded for now (Phase 2 introduces labels).
    /// At code offset 4, the `adr x1, msg` jumps +28 bytes — that's
    /// 32 (code length) minus 4 (adr's own offset).
    fn hello_world_code_bytes() -> Vec<u8> {
        let words: [u32; 8] = [
            movz_imm16(X0, 1),
            adr(X1, 28),
            movz_imm16(X2, 6),
            movz_imm16(X8, 64),
            svc(0),
            movz_imm16(X0, 0),
            movz_imm16(X8, 94),
            svc(0),
        ];
        let mut out = Vec::with_capacity(32);
        for w in words {
            out.extend_from_slice(&w.to_le_bytes());
        }
        out
    }

    /// Watermark: the ElfBuilder fed with the encoder-built hello-world
    /// payload must reproduce the Phase 0 byte-for-byte output. Drift
    /// here means either the encoders or the container are wrong.
    #[test]
    fn hello_world_round_trips_to_phase_0_watermark() {
        let code = hello_world_code_bytes();
        let data = b"hello\n";
        let built = build(0, &code, data);
        assert_eq!(
            built.as_slice(),
            crate::codegen::hello::HELLO_BYTES.as_slice(),
            "ElfBuilder output diverged from Phase 0 watermark"
        );
    }
}
