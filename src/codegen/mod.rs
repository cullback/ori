//! Native code emission.
//!
//! Phase 0 (current): hand-written byte vectors for a specific
//! artifact (`hello`). No encoders, no allocator, no SSA — just bytes
//! we can compare against `as` output. The point is to anchor the
//! whole pipeline to a runnable file on disk before any abstraction.
//!
//! Phase 1 (next): factor literals into instruction encoders
//! (`mov_imm`, `svc`, `adr`, …) and an ELF builder. Same artifact,
//! built compositionally.
//!
//! Phase 2: lower SSA to bytes via Phase 1 helpers, with bump-on-mmap
//! for allocation. Targets aarch64-linux only for now.

pub mod aarch64;
pub mod build;
pub mod elf;
pub mod hello;
