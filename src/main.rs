mod ast;
mod ast_display;
mod codegen;
mod error;
mod lower;
mod numeric;
mod opt;
mod passes;
mod source;
#[allow(
    clippy::pedantic,
    clippy::nursery,
    clippy::restriction,
    clippy::all,
    dead_code
)]
mod ssa;
mod stdlib;
mod symbol;
mod syntax;
#[cfg(test)]
mod test_frontend;
mod types;

use std::io::IsTerminal as _;
use std::io::Read as _;
use std::io::Write as _;
use std::process;

use error::CompileError;
use source::SourceArena;

fn resolve(
    arena: &mut SourceArena,
    main_file: source::FileId,
    source_dir: Option<&std::path::Path>,
    test_mode: bool,
) -> Result<passes::resolve::Resolved<'static>, CompileError> {
    let parsed = if test_mode {
        syntax::parse::parse_test(arena.content(main_file), main_file)?
    } else {
        syntax::parse::parse(arena.content(main_file), main_file)?
    };
    passes::resolve::resolve_imports(parsed, arena, source_dir)
}

fn compile(
    mut resolved: passes::resolve::Resolved<'static>,
) -> Result<(crate::ssa::Module, Vec<crate::ssa::Value>), CompileError> {
    passes::fold_lift::lift(&mut resolved);
    passes::flatten_patterns::flatten(&mut resolved)?;
    passes::topo::compute(&mut resolved)?;
    let infer_result = types::infer::check(&mut resolved)?;
    let mut mono = passes::mono::specialize(resolved.module, infer_result, resolved.symbols);
    passes::lambda::lift::lift(&mut mono);
    let lambda_solution = passes::lambda::solve::solve(&mono);
    passes::lambda::specialize::specialize(&mut mono, &lambda_solution);
    passes::lambda::narrow::narrow(&mut mono);
    let pre_prune_decls = passes::decl_info::build(&mono);
    passes::reachable::prune(&mut mono, &pre_prune_decls);

    // Try the new Core pipeline first. Two failure modes:
    //   (a) lower_module returns Err for any unsupported AST/Core
    //       variant — silent fallback.
    //   (b) lower_module returns Ok but produces SSA the validator
    //       rejects — silent fallback (covers cases where Core's
    //       lowering is unsound for that program shape).
    // Either way we fall through to the established direct AST→SSA
    // path. Core is additive — never regresses programs that worked
    // before, only takes over for ones it handles correctly.
    let decls = passes::decl_info::build(&mono);
    let core_attempt = passes::core::pipeline::lower_module(
        &mut mono, &resolved.fields, &decls,
    );
    if let Err(e) = &core_attempt {
        if std::env::var("ORI_TRACE_CORE").is_ok() {
            eprintln!("[core] fallback: {e}");
        }
    }
    // Run ssa_form + rc_emit + elim_dead_allocs before validating
    // so Core's emission can use implicit cross-block refs (which
    // ssa_form threads into explicit block params). Mirrors the
    // tail of existing-lower's `lower::lower`.
    let core_module = core_attempt.ok().map(|mut m| {
        if std::env::var("ORI_DUMP_CORE_RAW").is_ok() {
            eprintln!("=== raw Core SSA (pre ssa_form) ===\n{m}");
        }
        lower::ssa_form::run(&mut m);
        lower::rc_emit::run(&mut m);
        lower::elim_dead_allocs::run(&mut m);
        m
    }).filter(|m| {
        let r = ssa::validate::validate(m);
        let ok = r.is_clean() && r.warnings.is_empty();
        if !ok && std::env::var("ORI_TRACE_CORE").is_ok() {
            eprintln!("[core] fallback: validation errors={:?} warnings={:?}",
                r.errors, r.warnings);
        }
        ok
    });
    if core_module.is_some() && std::env::var("ORI_TRACE_CORE").is_ok() {
        eprintln!("[core] used Core pipeline");
    }

    let (ssa_module, input_vals) = if let Some(m) = core_module {
        let main_params = m.functions.get("__main")
            .map(|f| f.params.clone())
            .unwrap_or_default();
        (m, main_params)
    } else {
        lower::lower(&mono, &resolved.fields)?
    };
    let mut ssa_module = ssa_module;
    run_ssa_pipeline(&mut ssa_module);
    Ok((ssa_module, input_vals))
}

/// Run the full SSA pipeline on a freshly-lowered module. Single
/// canonical entry — see `opt::run_full_pipeline` for the order.
/// The pipeline itself calls `check` between passes.
fn run_ssa_pipeline(module: &mut ssa::Module) {
    ssa::validate::check(module, "lower");
    opt::run_full_pipeline(module);
}

fn bytes_to_scalar(bytes: &[u8], heap: &mut ssa::eval::Heap) -> ssa::eval::Scalar {
    let scalars: Vec<ssa::eval::Scalar> = bytes.iter().map(|&b| ssa::eval::Scalar::U8(b)).collect();
    heap_alloc_list(heap, &scalars)
}

fn heap_alloc_list(heap: &mut ssa::eval::Heap, elems: &[ssa::eval::Scalar]) -> ssa::eval::Scalar {
    use ssa::eval::Scalar;
    let len = elems.len();
    let data_idx = heap.alloc(len * 8);
    for (i, elem) in elems.iter().enumerate() {
        heap.store(data_idx, i * 8, *elem);
    }
    let header_idx = heap.alloc(24);
    heap.store(header_idx, 0, Scalar::U64(len as u64));
    heap.store(header_idx, 8, Scalar::U64(len as u64));
    heap.store(header_idx, 16, Scalar::Ptr(data_idx));
    Scalar::Ptr(header_idx)
}

fn scalar_str_to_bytes(heap: &ssa::eval::Heap, str_ptr: ssa::eval::Scalar) -> Vec<u8> {
    use ssa::eval::Scalar;
    let Scalar::Ptr(list_idx) = str_ptr else {
        panic!("expected Ptr for string, got {str_ptr:?}");
    };
    let Scalar::U64(len) = heap.load(list_idx, 0, ssa::ScalarType::U64) else {
        panic!("expected U64 for list len");
    };
    let Scalar::Ptr(data_idx) = heap.load(list_idx, 16, ssa::ScalarType::RcPtr) else {
        panic!("expected Ptr for list data");
    };
    #[expect(clippy::cast_possible_truncation)]
    let len_usize = len as usize;
    let mut bytes = Vec::with_capacity(len_usize);
    for i in 0..len_usize {
        let Scalar::U8(b) = heap.load(data_idx, i * 8, ssa::ScalarType::U8) else {
            panic!("expected U8 in string data");
        };
        bytes.push(b);
    }
    bytes
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    // Phase 0 codegen escape hatch: bypass the whole frontend and
    // write the hand-crafted hello-world ELF directly. Removes any
    // dependence on a working Ori source file.
    if let Some(out_path) = args.iter().position(|a| a == "--emit-hello").and_then(|i| args.get(i + 1)) {
        codegen::hello::emit(std::path::Path::new(out_path)).unwrap_or_else(|e| {
            eprintln!("emit-hello: {e}");
            process::exit(1);
        });
        return;
    }

    let dump_ssa = args.iter().any(|a| a == "--dump-ssa");
    let emit_native = args
        .iter()
        .position(|a| a == "--emit-native")
        .and_then(|i| args.get(i + 1))
        .cloned();
    let positional: Vec<&String> = args
        .iter()
        .skip(1)
        .filter(|a| !a.starts_with("--"))
        .filter(|a| Some(*a) != emit_native.as_ref())
        .collect();
    // `ori test <file.ori>` runs all `expect` decls; otherwise the
    // first positional is the source path and the rest are program args.
    let (test_mode, file_args): (bool, Vec<&String>) = match positional.first() {
        Some(first) if first.as_str() == "test" => (true, positional[1..].to_vec()),
        _ => (false, positional),
    };
    if file_args.is_empty() {
        eprintln!("usage: ori [--dump-ssa] [test] <file.ori> [args...]");
        eprintln!("       ori --emit-hello <output_path>");
        eprintln!("       ori --emit-native <output_path> <file.ori>");
        process::exit(1);
    }
    let source_path = file_args[0];
    let mut content = std::fs::read_to_string(source_path).unwrap_or_else(|e| {
        eprintln!("error reading {source_path}: {e}");
        process::exit(1);
    });

    if test_mode {
        let doctests = crate::syntax::parse::extract_doctest_expects(&content);
        let is_lib = content.lines().any(|l| l.trim().starts_with("exports "));
        if is_lib {
            // Lib files can't be tested directly (builtins have no
            // bodies). Generate a wrapper that imports the module and
            // includes its doctests.
            let module_name = std::path::Path::new(source_path)
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("lib");
            let mut wrapper = format!("import {module_name}\n");
            for dt in &doctests {
                wrapper.push_str(dt);
                wrapper.push('\n');
            }
            content = wrapper;
        } else if !doctests.is_empty() {
            content.push('\n');
            content.push_str(&doctests.join("\n"));
        }
    }

    let mut arena = SourceArena::new();
    let main_file = arena.add(source_path.clone(), content);

    let source_dir = std::path::Path::new(source_path).parent();
    let resolved = match resolve(&mut arena, main_file, source_dir, test_mode) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("{}", e.format(&arena));
            process::exit(1);
        }
    };
    let (ssa_module, input_vals) = match compile(resolved) {
        Ok(result) => result,
        Err(e) => {
            eprintln!("{}", e.format(&arena));
            process::exit(1);
        }
    };

    if dump_ssa {
        eprint!("{ssa_module}");
        process::exit(0);
    }

    if let Some(out_path) = emit_native.as_ref() {
        use std::io::Write as _;
        use std::os::unix::fs::PermissionsExt as _;
        let bytes = codegen::build::build_ori_program_linux_aarch64(&ssa_module);
        let path = std::path::Path::new(out_path);
        std::fs::write(path, &bytes).unwrap_or_else(|e| {
            eprintln!("emit-native: {e}");
            process::exit(1);
        });
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755))
            .unwrap_or_else(|e| {
                eprintln!("emit-native chmod: {e}");
                process::exit(1);
            });
        // Flush in case stdout is line-buffered for the calling shell.
        let _ = std::io::stderr().flush();
        return;
    }

    // Build SSA inputs
    let mut heap = ssa::eval::new_heap();
    ssa::eval::load_statics(&ssa_module, &mut heap);
    let program_args: Vec<&String> = file_args[1..].to_vec();

    let cli_args: Vec<ssa::eval::Scalar> = program_args
        .iter()
        .map(|a| bytes_to_scalar(a.as_bytes(), &mut heap))
        .collect();
    let args_list = heap_alloc_list(&mut heap, &cli_args);

    let stdin_val = if std::io::stdin().is_terminal() {
        bytes_to_scalar(b"", &mut heap)
    } else {
        let mut buf = Vec::new();
        std::io::stdin().read_to_end(&mut buf).unwrap();
        bytes_to_scalar(&buf, &mut heap)
    };

    let mut ssa_args = Vec::new();
    for i in 0..input_vals.len() {
        ssa_args.push(match i {
            0 => args_list,
            1 => stdin_val,
            _ => bytes_to_scalar(b"", &mut heap),
        });
    }

    let result = ssa::eval::eval(&ssa_module, &mut heap, &ssa_args);
    if std::env::var("ORI_HEAP_STATS").is_ok() {
        eprintln!(
            "heap stats: alloc={} fresh={} free={} peak_live={}",
            heap.alloc_count, heap.fresh_alloc_count, heap.free_count, heap.peak_live,
        );
    }

    // Handle Result output. With D2 the result is materialized as a
    // 16-byte tag-union shell: `tag@0`, `payload_ptr@8`. The payload
    // heap object holds the Continue/Break-style variant fields — for
    // `Result(Str, Str)` that's the Str pointer at offset 0 of the
    // payload.
    let ssa::eval::Scalar::Ptr(result_idx) = result else {
        eprintln!("unexpected non-Ptr result: {result:?}");
        process::exit(1);
    };
    let ssa::eval::Scalar::U64(tag) = heap.load(result_idx, 0, ssa::ScalarType::U64) else {
        eprintln!("unexpected tag type");
        process::exit(1);
    };
    let payload_ptr = heap.load(result_idx, 8, ssa::ScalarType::RcPtr);
    let ssa::eval::Scalar::Ptr(payload_idx) = payload_ptr else {
        eprintln!("unexpected non-Ptr payload: {payload_ptr:?}");
        process::exit(1);
    };
    let str_ptr = heap.load(payload_idx, 0, ssa::ScalarType::RcPtr);

    // Tag 0 = first constructor (Ok), Tag 1 = second (Err)
    let bytes = scalar_str_to_bytes(&heap, str_ptr);
    if tag == 0 {
        std::io::stdout().write_all(&bytes).unwrap();
        if !bytes.ends_with(b"\n") {
            println!();
        }
    } else {
        std::io::stderr().write_all(&bytes).unwrap();
        process::exit(1);
    }
}
