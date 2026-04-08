mod decl_info;
mod defunc;
mod error;
mod reachable;
mod resolve;
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

fn compile(
    arena: &mut SourceArena,
    main_file: source::FileId,
    source_dir: Option<&std::path::Path>,
) -> Result<(crate::ssa::Module, Vec<crate::ssa::Value>), CompileError> {
    let parsed = syntax::parse::parse(arena.content(main_file), main_file)?;
    let resolved = resolve::resolve_imports(parsed, arena, source_dir)?;
    let infer_result = types::infer::check(arena, &resolved.module, &resolved.scope)?;
    ssa::lower::lower(arena, &resolved.module, &resolved.scope, &infer_result)
}

fn bytes_to_scalar(bytes: &[u8], heap: &mut ssa::eval::Heap) -> ssa::eval::Scalar {
    let scalars: Vec<ssa::eval::Scalar> = bytes.iter().map(|&b| ssa::eval::Scalar::U8(b)).collect();
    heap_alloc_list(heap, &scalars)
}

fn heap_alloc_list(heap: &mut ssa::eval::Heap, elems: &[ssa::eval::Scalar]) -> ssa::eval::Scalar {
    use ssa::eval::Scalar;
    let len = elems.len();
    let data_idx = heap.alloc(len);
    for (i, elem) in elems.iter().enumerate() {
        heap.store(data_idx, i, *elem);
    }
    let header_idx = heap.alloc(3);
    heap.store(header_idx, 0, Scalar::U64(len as u64));
    heap.store(header_idx, 1, Scalar::U64(len as u64));
    heap.store(header_idx, 2, Scalar::Ptr(data_idx));
    Scalar::Ptr(header_idx)
}

fn scalar_str_to_bytes(heap: &ssa::eval::Heap, str_ptr: ssa::eval::Scalar) -> Vec<u8> {
    use ssa::eval::Scalar;
    let Scalar::Ptr(list_idx) = str_ptr else {
        panic!("expected Ptr for string, got {str_ptr:?}");
    };
    let Scalar::U64(len) = heap.load(list_idx, 0) else {
        panic!("expected U64 for list len");
    };
    let Scalar::Ptr(data_idx) = heap.load(list_idx, 2) else {
        panic!("expected Ptr for list data");
    };
    #[expect(clippy::cast_possible_truncation)]
    let len_usize = len as usize;
    let mut bytes = Vec::with_capacity(len_usize);
    for i in 0..len_usize {
        let Scalar::U8(b) = heap.load(data_idx, i) else {
            panic!("expected U8 in string data");
        };
        bytes.push(b);
    }
    bytes
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let dump_ssa = args.iter().any(|a| a == "--dump-ssa");
    let file_args: Vec<&String> = args
        .iter()
        .skip(1)
        .filter(|a| !a.starts_with("--"))
        .collect();
    if file_args.is_empty() {
        eprintln!("usage: ori [--dump-ssa] <file.ori> [args...]");
        process::exit(1);
    }
    let source_path = file_args[0];
    let content = std::fs::read_to_string(source_path).unwrap_or_else(|e| {
        eprintln!("error reading {source_path}: {e}");
        process::exit(1);
    });

    let mut arena = SourceArena::new();
    let main_file = arena.add(source_path.clone(), content);

    let source_dir = std::path::Path::new(source_path).parent();
    let (ssa_module, input_vals) = match compile(&mut arena, main_file, source_dir) {
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

    // Build SSA inputs
    let mut heap = ssa::eval::new_heap();
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

    // Handle Result output — result is a Ptr to a tagged union
    let ssa::eval::Scalar::Ptr(result_idx) = result else {
        eprintln!("unexpected non-Ptr result: {result:?}");
        process::exit(1);
    };
    let ssa::eval::Scalar::U64(tag) = heap.load(result_idx, 0) else {
        eprintln!("unexpected tag type");
        process::exit(1);
    };
    let payload = heap.load(result_idx, 1);

    // Tag 0 = first constructor (Ok), Tag 1 = second (Err)
    let bytes = scalar_str_to_bytes(&heap, payload);
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
