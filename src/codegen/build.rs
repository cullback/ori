//! Top-level codegen driver: SSA `Module` → linux-aarch64 ELF bytes.
//!
//! Phase 3-lite glue. Composes `select` (SSA → MIR), `emit` (MIR →
//! code+data bytes), and `elf::build` (container). The output is a
//! ready-to-write `Vec<u8>` that, with execute permission, runs on
//! aarch64-linux.

#![allow(
    clippy::cast_possible_truncation,
    clippy::pub_with_shorthand,
    dead_code
)]

use crate::ssa::Module;

use super::aarch64::{emit, lower_main, select};
use super::elf;

/// Phase 3-lite: hand-constructed SSA with intrinsic syscall calls.
/// Used by the existing intrinsic-only test path.
#[must_use]
pub fn build_linux_aarch64(module: &Module) -> Vec<u8> {
    let (mir, data) = select::lower_module(module);
    let (combined, code_size) = emit::emit(&mir, &data);
    let code = &combined[..code_size as usize];
    let data_bytes = &combined[code_size as usize..];
    elf::build(0, code, data_bytes)
}

/// Phase 4: real Ori SSA module (output of `compile()`) → native
/// aarch64-linux ELF. Tries the const-return specialization first
/// (collapses a known-constant `Result` return into a direct write +
/// exit, dropping the runtime decoder and unused statics); falls
/// back to the general runtime-shim path for non-constant returns.
#[must_use]
pub fn build_ori_program_linux_aarch64(module: &Module) -> Vec<u8> {
    let (mir, data) = if let Some(info) = lower_main::analyze_const_return(module) {
        lower_main::lower_const_return(&info, module)
    } else {
        let mir = lower_main::lower_to_mir(module);
        let code_size = mir_code_size(&mir);
        let data = lower_main::data_items(module, code_size);
        (mir, data)
    };
    let (combined, code_size) = emit::emit(&mir, &data);
    let code = &combined[..code_size as usize];
    let data_bytes = &combined[code_size as usize..];
    elf::build(0, code, data_bytes)
}

/// Byte count of the encoded code section — counts only instructions
/// that emit bytes (skips `BlockStart` pseudo-ops).
fn mir_code_size(mir: &[super::aarch64::mir::MInst]) -> u64 {
    use super::aarch64::mir::MInst;
    let n = mir.iter().filter(|i| !matches!(i, MInst::BlockStart { .. })).count();
    (n as u64) * 4
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap};
    use std::io::Write as _;
    use std::os::unix::fs::PermissionsExt as _;

    use super::*;
    use crate::ssa::{
        Block, BlockId, Function, Inst, Module, ScalarType, StaticObject, StaticSlot, Terminator,
        Value,
    };

    /// Hand-construct an SSA module equivalent to:
    ///   _start():
    ///     write(1, "hello\n", 6)
    ///     exit_group(0)
    ///
    /// Value ids are chosen carefully (0..=3) so the trivial vreg=phys
    /// mapping in `select` puts each value in the right syscall arg
    /// register without needing extra `MovReg` shuffles.
    fn hand_built_hello_module() -> Module {
        let v0 = Value { id: 0, ty: ScalarType::U64 }; // fd = 1, → x0
        let v1 = Value { id: 1, ty: ScalarType::Ptr }; // msg ptr,  → x1
        let v2 = Value { id: 2, ty: ScalarType::U64 }; // len = 6,  → x2
        let v3 = Value { id: 3, ty: ScalarType::U64 }; // exit code, → x3 then MovReg→x0

        let block = Block {
            params: vec![],
            insts: vec![
                Inst::Const(v0, 1),
                Inst::StaticRef(v1, 0),
                Inst::Const(v2, 6),
                Inst::Call {
                    results: vec![],
                    target: "__syscall_write".to_string(),
                    args: vec![v0, v1, v2],
                },
                Inst::Const(v3, 0),
                Inst::Call {
                    results: vec![],
                    target: "__syscall_exit".to_string(),
                    args: vec![v3],
                },
            ],
            terminator: Terminator::Return(vec![v3]),
        };

        let mut blocks = BTreeMap::new();
        blocks.insert(BlockId(0), block);

        let func = Function {
            name: "_start".to_string(),
            params: vec![],
            blocks,
            return_type: vec![ScalarType::U64],
            entry: BlockId(0),
            next_block: 1,
        };

        let mut functions = HashMap::new();
        functions.insert(func.name.clone(), func);

        Module {
            functions,
            statics: vec![StaticObject {
                slots: b"hello\n".iter().copied().map(StaticSlot::U8).collect(),
            }],
            entry: "_start".to_string(),
        }
    }

    fn compile_and_run(src: &str) -> (Vec<u8>, std::process::Output) {
        use crate::source::SourceArena;
        use std::io::Write as _;
        use std::os::unix::fs::PermissionsExt as _;

        let mut arena = SourceArena::new();
        let main_file = arena.add("/tmp/ori_phase4_test.ori".to_string(), src.to_string());
        let resolved = crate::resolve(&mut arena, main_file, None, false)
            .unwrap_or_else(|e| panic!("resolve failed: {}", e.format(&arena)));
        let (ssa_module, _input_vals) = crate::compile(resolved)
            .unwrap_or_else(|e| panic!("compile failed: {}", e.format(&arena)));

        let bytes = build_ori_program_linux_aarch64(&ssa_module);

        let dir = std::env::temp_dir().join(format!("ori-phase4-{}-{}", std::process::id(), rand_suffix()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("prog");
        let mut f = std::fs::File::create(&path).unwrap();
        f.write_all(&bytes).unwrap();
        drop(f);
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();

        let out = std::process::Command::new(&path).output().unwrap();
        std::fs::remove_dir_all(&dir).ok();
        (bytes, out)
    }

    fn rand_suffix() -> u64 {
        use std::time::{SystemTime, UNIX_EPOCH};
        SystemTime::now().duration_since(UNIX_EPOCH).unwrap().subsec_nanos() as u64
    }

    /// Phase 4 const-return specialization: for `main = |a,i| Ok(static_str)`,
    /// the binary must collapse to: 120 (ELF+PHdr) + 32 (8 instructions) + len(str).
    /// That's the same byte budget a hand-written hello world would have.
    #[test]
    #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
    fn ok_static_str_is_byte_tied_with_handwritten() {
        let (bytes, out) = compile_and_run("main : List(Str), Str -> Result(Str, Str)\nmain = |a,i| Ok(\"hi\")\n");
        assert!(out.status.success(), "exit status {:?}; stderr: {}", out.status, String::from_utf8_lossy(&out.stderr));
        assert_eq!(out.stdout, b"hi");
        assert_eq!(bytes.len(), 154, "expected 120+32+2 = 154 bytes for Ok(\"hi\")");
    }

    #[test]
    #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
    fn err_static_str_goes_to_stderr_with_exit_1() {
        let (bytes, out) = compile_and_run("main : List(Str), Str -> Result(Str, Str)\nmain = |a,i| Err(\"oops\\n\")\n");
        assert_eq!(out.status.code(), Some(1), "Err should exit 1");
        assert_eq!(out.stdout, b"", "Err should not write to stdout");
        assert_eq!(out.stderr, b"oops\n");
        assert_eq!(bytes.len(), 157, "expected 120+32+5 = 157 bytes for Err(\"oops\\n\")");
    }

    fn compile_and_run_with_stdin(src: &str, stdin_data: &[u8]) -> (Vec<u8>, std::process::Output) {
        use crate::source::SourceArena;
        use std::io::Write as _;
        use std::os::unix::fs::PermissionsExt as _;
        use std::process::Stdio;

        let mut arena = SourceArena::new();
        let main_file = arena.add("/tmp/ori_phase5_test.ori".to_string(), src.to_string());
        let resolved = crate::resolve(&mut arena, main_file, None, false)
            .unwrap_or_else(|e| panic!("resolve failed: {}", e.format(&arena)));
        let (ssa_module, _input_vals) = crate::compile(resolved)
            .unwrap_or_else(|e| panic!("compile failed: {}", e.format(&arena)));

        let bytes = build_ori_program_linux_aarch64(&ssa_module);

        let dir = std::env::temp_dir().join(format!("ori-phase5-{}-{}", std::process::id(), rand_suffix()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("prog");
        let mut f = std::fs::File::create(&path).unwrap();
        f.write_all(&bytes).unwrap();
        drop(f);
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();

        let mut child = std::process::Command::new(&path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.as_mut().unwrap().write_all(stdin_data).unwrap();
        let out = child.wait_with_output().unwrap();
        std::fs::remove_dir_all(&dir).ok();
        (bytes, out)
    }

    /// Phase 5a: echo program. `main = |a,i| Ok(input)` reads stdin,
    /// allocates Result+Ok shell at runtime via the bump allocator,
    /// returns. The runtime shim writes the Str's bytes back out.
    #[test]
    #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
    fn echo_program_round_trips_stdin() {
        let src = "main : List(Str), Str -> Result(Str, Str)\nmain = |a,i| Ok(i)\n";
        let (_bytes, out) = compile_and_run_with_stdin(src, b"hello from stdin\n");
        assert!(out.status.success(), "exit {:?}; stderr: {}", out.status, String::from_utf8_lossy(&out.stderr));
        assert_eq!(out.stdout, b"hello from stdin\n");
    }

    /// Phase 5b: branches + multi-block functions. The args list is
    /// empty in our entry shim, so this program takes the `args : []`
    /// arm and prints "no args".
    #[test]
    #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
    fn branching_program_takes_correct_arm() {
        let src = "main : List(Str), Str -> Result(Str, Str)\nmain = |a,i| if a : [] then Ok(\"no args\") else Ok(\"got args\")\n";
        let (_bytes, out) = compile_and_run_with_stdin(src, b"");
        assert!(out.status.success(), "exit {:?}; stderr: {}", out.status, String::from_utf8_lossy(&out.stderr));
        assert_eq!(out.stdout, b"no args");
    }

    /// Phase 5c: inter-function calls. Calls a helper that's the
    /// identity function; expected to round-trip stdin like echo.
    #[test]
    #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
    fn identity_helper_passes_input_through() {
        let src = "helper : Str -> Str\nhelper = |s| s\n\nmain : List(Str), Str -> Result(Str, Str)\nmain = |a,i| Ok(helper(i))\n";
        let (_bytes, out) = compile_and_run_with_stdin(src, b"hello via helper\n");
        assert!(out.status.success(), "exit {:?}; stderr: {}", out.status, String::from_utf8_lossy(&out.stderr));
        assert_eq!(out.stdout, b"hello via helper\n");
    }

    /// Phase 5c: nested calls. Three identity calls — exercises the
    /// caller-saved register handling (or its absence; we only use
    /// caller-saved regs for vregs but never reuse them across calls
    /// in this trivial pattern).
    #[test]
    #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
    fn nested_identity_calls_work() {
        let src = "id : Str -> Str\nid = |s| s\n\nmain : List(Str), Str -> Result(Str, Str)\nmain = |a,i| Ok(id(id(id(i))))\n";
        let (_bytes, out) = compile_and_run_with_stdin(src, b"three deep\n");
        assert!(out.status.success(), "exit {:?}; stderr: {}", out.status, String::from_utf8_lossy(&out.stderr));
        assert_eq!(out.stdout, b"three deep\n");
    }

    /// Phase 5a: empty stdin should produce empty stdout, exit 0.
    #[test]
    #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
    fn echo_program_handles_empty_stdin() {
        let src = "main : List(Str), Str -> Result(Str, Str)\nmain = |a,i| Ok(i)\n";
        let (_bytes, out) = compile_and_run_with_stdin(src, b"");
        assert!(out.status.success());
        assert_eq!(out.stdout, b"");
    }

    /// Phase 4 end-to-end: real Ori source through the existing
    /// frontend, lowered to native via `build_ori_program_linux_aarch64`,
    /// executed. The high-confidence test for the whole pipeline.
    #[test]
    #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
    fn ori_source_compiles_and_runs() {
        use crate::source::SourceArena;

        let src = "main : List(Str), Str -> Result(Str, Str)\nmain = |args, input| Ok(\"hi\")\n";

        let mut arena = SourceArena::new();
        let main_file = arena.add("/tmp/ori_phase4_test.ori".to_string(), src.to_string());
        let resolved = crate::resolve(&mut arena, main_file, None, false)
            .unwrap_or_else(|e| panic!("resolve failed: {}", e.format(&arena)));
        let (ssa_module, _input_vals) = crate::compile(resolved)
            .unwrap_or_else(|e| panic!("compile failed: {}", e.format(&arena)));

        let bytes = build_ori_program_linux_aarch64(&ssa_module);

        let dir = std::env::temp_dir().join(format!("ori-phase4-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("prog");
        let mut f = std::fs::File::create(&path).unwrap();
        f.write_all(&bytes).unwrap();
        drop(f);
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();

        let out = std::process::Command::new(&path).output().unwrap();
        assert!(out.status.success(), "binary exited with {:?}; stderr: {}", out.status, String::from_utf8_lossy(&out.stderr));
        assert_eq!(out.stdout, b"hi", "stdout mismatch");

        std::fs::remove_dir_all(&dir).ok();
    }

    /// Phase 3-lite end-to-end: hand-built SSA with intrinsic syscalls.
    #[test]
    #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
    fn hand_built_ssa_runs_and_prints_hello() {
        let module = hand_built_hello_module();
        let bytes = build_linux_aarch64(&module);

        let dir = std::env::temp_dir().join(format!("ori-ssa-native-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("hello_ssa");
        let mut f = std::fs::File::create(&path).unwrap();
        f.write_all(&bytes).unwrap();
        drop(f);
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();

        let out = std::process::Command::new(&path).output().unwrap();
        assert!(out.status.success(), "binary exited with {:?}", out.status);
        assert_eq!(out.stdout, b"hello\n", "stdout mismatch");
        assert_eq!(out.stderr, b"", "stderr should be empty");

        std::fs::remove_dir_all(&dir).ok();
    }
}
