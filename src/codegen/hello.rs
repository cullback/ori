//! Hand-written aarch64-linux ELF that prints "hello\n" and exits.
//!
//! Phase 0 of native codegen: literal bytes only. No instruction
//! encoders, no ELF builder, no allocator — every value here was
//! cross-checked against `as` / `objdump`. The whole binary is 158
//! bytes:
//!
//! ```text
//!   off  | what                       | size
//!   ---- | -------------------------- | ----
//!   0    | ELF64 header               | 64
//!   64   | one PT_LOAD program header | 56
//!   120  | code (8 instructions)      | 32
//!   152  | "hello\n"                  | 6
//! ```
//!
//! Loaded at virtual address `0x400000`, segment is mapped R+X, entry
//! is at `0x400078` (start of code).
//!
//! Syscall ABI (aarch64-linux): number in `x8`, args in `x0..x7`,
//! trap via `svc #0`. We use `write` (64) and `exit_group` (94).

// File-local allows: the bytewise ELF construction unavoidably uses
// `to_le_bytes` and small integer literals throughout; per-site
// `#[expect]` would drown the actual logic. `pub_with_shorthand` is
// repo-pervasive (see Cargo.toml workspace lints).
#![allow(
    clippy::little_endian_bytes,
    clippy::pub_with_shorthand,
    clippy::separated_literal_suffix,
    dead_code
)]

use std::io::Write as _;
use std::os::unix::fs::PermissionsExt as _;
use std::path::Path;

const LOAD_VADDR: u64 = 0x40_0000;
const ELF_HDR_SIZE: u64 = 64;
const PHDR_SIZE: u64 = 56;
const ENTRY_VADDR: u64 = LOAD_VADDR + ELF_HDR_SIZE + PHDR_SIZE;

const MSG: &[u8] = b"hello\n";

// Eight 32-bit instructions, little-endian. Cross-checked with
// `as` + `objdump -d`. See module docstring for the equivalent
// assembly listing.
const CODE: [u32; 8] = [
    0xD280_0020, // mov  x0, #1                fd = stdout
    0x1000_00E1, // adr  x1, msg               pc-relative +28
    0xD280_00C2, // mov  x2, #6                count = len("hello\n")
    0xD280_0808, // mov  x8, #64               syscall = write
    0xD400_0001, // svc  #0
    0xD280_0000, // mov  x0, #0                status = 0
    0xD280_0BC8, // mov  x8, #94               syscall = exit_group
    0xD400_0001, // svc  #0
];

#[expect(clippy::cast_possible_truncation)]
fn build() -> Vec<u8> {
    let code_size = (CODE.len() * 4) as u64;
    let msg_size = MSG.len() as u64;
    let file_size = ELF_HDR_SIZE + PHDR_SIZE + code_size + msg_size;

    let mut b: Vec<u8> = Vec::with_capacity(file_size as usize);

    // ELF64 header (64 bytes).
    b.extend_from_slice(&[0x7F, b'E', b'L', b'F']); // e_ident magic
    b.push(2); // EI_CLASS    = ELFCLASS64
    b.push(1); // EI_DATA     = ELFDATA2LSB
    b.push(1); // EI_VERSION  = EV_CURRENT
    b.push(0); // EI_OSABI    = SYSV
    b.push(0); // EI_ABIVERSION
    b.extend_from_slice(&[0; 7]); // EI_PAD
    b.extend_from_slice(&2_u16.to_le_bytes()); // e_type      = ET_EXEC
    b.extend_from_slice(&0x00B7_u16.to_le_bytes()); // e_machine   = EM_AARCH64
    b.extend_from_slice(&1_u32.to_le_bytes()); // e_version
    b.extend_from_slice(&ENTRY_VADDR.to_le_bytes()); // e_entry
    b.extend_from_slice(&ELF_HDR_SIZE.to_le_bytes()); // e_phoff
    b.extend_from_slice(&0_u64.to_le_bytes()); // e_shoff = 0 (no sections)
    b.extend_from_slice(&0_u32.to_le_bytes()); // e_flags
    b.extend_from_slice(&(ELF_HDR_SIZE as u16).to_le_bytes()); // e_ehsize
    b.extend_from_slice(&(PHDR_SIZE as u16).to_le_bytes()); // e_phentsize
    b.extend_from_slice(&1_u16.to_le_bytes()); // e_phnum
    b.extend_from_slice(&0_u16.to_le_bytes()); // e_shentsize
    b.extend_from_slice(&0_u16.to_le_bytes()); // e_shnum
    b.extend_from_slice(&0_u16.to_le_bytes()); // e_shstrndx

    // Program header (56 bytes) — one PT_LOAD covering the whole file.
    b.extend_from_slice(&1_u32.to_le_bytes()); // p_type   = PT_LOAD
    b.extend_from_slice(&5_u32.to_le_bytes()); // p_flags  = PF_R | PF_X
    b.extend_from_slice(&0_u64.to_le_bytes()); // p_offset
    b.extend_from_slice(&LOAD_VADDR.to_le_bytes()); // p_vaddr
    b.extend_from_slice(&LOAD_VADDR.to_le_bytes()); // p_paddr
    b.extend_from_slice(&file_size.to_le_bytes()); // p_filesz
    b.extend_from_slice(&file_size.to_le_bytes()); // p_memsz
    b.extend_from_slice(&0x0001_0000_u64.to_le_bytes()); // p_align = 64 KiB

    // Code.
    for insn in CODE {
        b.extend_from_slice(&insn.to_le_bytes());
    }

    // Message.
    b.extend_from_slice(MSG);

    debug_assert_eq!(b.len() as u64, file_size, "elf size accounting drifted");
    b
}

/// Emit the hand-written hello-world binary to `path`, chmod 0o755.
pub fn emit(path: &Path) -> std::io::Result<()> {
    let bytes = build();
    let mut f = std::fs::File::create(path)?;
    f.write_all(&bytes)?;
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755))?;
    Ok(())
}

/// Watermark: every byte. Drift here is either an intentional
/// change (update the constant) or a regression. Phase ≥ 1 paths
/// that go through encoders/builders must reproduce this byte-for-byte.
pub const HELLO_BYTES: &[u8; 158] = &[
    0x7f, 0x45, 0x4c, 0x46, 0x02, 0x01, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x02, 0x00, 0xb7, 0x00, 0x01, 0x00, 0x00, 0x00, 0x78, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x38, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x9e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x9e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x20, 0x00, 0x80, 0xd2, 0xe1, 0x00, 0x00, 0x10,
    0xc2, 0x00, 0x80, 0xd2, 0x08, 0x08, 0x80, 0xd2, 0x01, 0x00, 0x00, 0xd4, 0x00, 0x00, 0x80, 0xd2,
    0xc8, 0x0b, 0x80, 0xd2, 0x01, 0x00, 0x00, 0xd4, 0x68, 0x65, 0x6c, 0x6c, 0x6f, 0x0a,
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bytes_match_watermark() {
        assert_eq!(build().as_slice(), HELLO_BYTES.as_slice(), "elf bytes drifted");
    }

    #[test]
    #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
    fn emitted_binary_prints_hello() {
        let dir = std::env::temp_dir().join(format!("ori-hello-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("hello");
        emit(&path).unwrap();
        let out = std::process::Command::new(&path).output().unwrap();
        assert!(out.status.success(), "binary exited with {:?}", out.status);
        assert_eq!(out.stdout, b"hello\n", "stdout mismatch");
        assert_eq!(out.stderr, b"", "stderr should be empty");
        std::fs::remove_dir_all(&dir).ok();
    }
}
