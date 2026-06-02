//! aarch64 target backend.
//!
//! Layering from bottom to top:
//!   `encode`  — pure-fn instruction encoders, target-independent of OS/container.
//!   (`mir`)   — Phase 2: virtual-register IR with symbolic labels.
//!   (`emit`)  — Phase 2: MIR → bytes via `encode`.
//!   (`select`)— Phase 3: SSA → MIR.
//!
//! Only `encode` exists today; later modules will be added as their phases land.

pub mod emit;
pub mod encode;
pub mod facts;
pub mod lower_main;
pub mod mir;
pub mod select;
