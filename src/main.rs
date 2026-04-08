mod core;
mod error;
mod lower;
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
#[cfg(test)]
mod test_programs;
mod types;

use std::collections::HashMap;
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
) -> Result<(crate::core::Program, Vec<crate::core::VarId>), CompileError> {
    for (name, src) in stdlib::all() {
        arena.add(format!("<stdlib:{name}>"), src.to_owned());
    }

    let parsed = syntax::parse::parse(arena.content(main_file), main_file)?;
    let resolved = resolve::resolve_imports(parsed, arena, source_dir)?;
    let infer_result = types::infer::check(arena, &resolved.module, &resolved.scope)?;
    lower::lower(arena, &resolved.module, &resolved.scope, &infer_result)
}

fn value_to_bytes(val: &core::Value) -> Vec<u8> {
    let core::Value::VList(elems) = val else {
        panic!("expected Str, got {val:?}");
    };
    elems
        .iter()
        .map(|e| {
            let core::Value::VNum(core::NumVal::U8(b)) = e else {
                panic!("expected U8 in Str, got {e:?}");
            };
            *b
        })
        .collect()
}

fn bytes_to_value(bytes: &[u8]) -> core::Value {
    core::Value::VList(
        bytes
            .iter()
            .map(|&b| core::Value::VNum(core::NumVal::U8(b)))
            .collect(),
    )
}

fn print_value(val: &core::Value) {
    match val {
        core::Value::VList(_) => {
            let bytes = value_to_bytes(val);
            std::io::stdout().write_all(&bytes).unwrap();
        }
        core::Value::VNum(core::NumVal::I64(n)) => print!("{n}"),
        core::Value::VNum(core::NumVal::U64(n)) => print!("{n}"),
        core::Value::VNum(core::NumVal::F64(n)) => print!("{n}"),
        core::Value::VNum(core::NumVal::U8(n)) => print!("{n}"),
        core::Value::VNum(core::NumVal::I8(n)) => print!("{n}"),
        other => print!("{other:?}"),
    }
    if let core::Value::VList(elems) = val
        && elems.last() == Some(&core::Value::VNum(core::NumVal::U8(b'\n')))
    {
        return;
    }
    println!();
}

fn eprint_value(val: &core::Value) {
    match val {
        core::Value::VList(_) => {
            let bytes = value_to_bytes(val);
            std::io::stderr().write_all(&bytes).unwrap();
        }
        other => eprint!("{other:?}"),
    }
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
    let (program, input_vars) = match compile(&mut arena, main_file, source_dir) {
        Ok(result) => result,
        Err(e) => {
            eprintln!("{}", e.format(&arena));
            process::exit(1);
        }
    };

    if dump_ssa {
        eprintln!("--dump-ssa: low-level SSA lowering not yet implemented");
        process::exit(1);
    }

    // Build inputs
    let program_args: Vec<&String> = file_args[1..].to_vec();
    let cli_args: Vec<core::Value> = program_args
        .iter()
        .map(|a| bytes_to_value(a.as_bytes()))
        .collect();
    let args_value = core::Value::VList(cli_args);

    let stdin_value = if std::io::stdin().is_terminal() {
        bytes_to_value(b"")
    } else {
        let mut buf = Vec::new();
        std::io::stdin().read_to_end(&mut buf).unwrap();
        bytes_to_value(&buf)
    };

    // Evaluate via Core interpreter
    let mut env = HashMap::new();
    for (i, var) in input_vars.iter().enumerate() {
        let val = match i {
            0 => args_value.clone(),
            1 => stdin_value.clone(),
            _ => core::Value::VList(vec![]),
        };
        env.insert(*var, val);
    }
    let result = core::eval::eval(&env, &program, &program.main);

    // Handle Result output
    match &result {
        core::Value::VConstruct { tag, fields } => {
            let name = program.debug_names.func_name(*tag);
            match name {
                "Ok" => print_value(&fields[0]),
                "Err" => {
                    eprint_value(&fields[0]);
                    process::exit(1);
                }
                _ => println!("{result:?}"),
            }
        }
        _ => println!("{result:?}"),
    }
}
