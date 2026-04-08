mod core;
mod error;
mod lower;
mod resolve;
mod source;
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
    // Pre-load stdlib into arena
    for (name, src) in stdlib::all() {
        arena.add(format!("<stdlib:{name}>"), src.to_owned());
    }

    let parsed = syntax::parse::parse(arena.content(main_file), main_file)?;
    let resolved = resolve::resolve_imports(parsed, arena, source_dir)?;
    // Arena is done growing — check and lower only read
    let infer_result = types::infer::check(arena, &resolved.module, &resolved.scope)?;
    lower::lower(arena, &resolved.module, &resolved.scope, &infer_result)
}

/// Convert a Str value (List(U8)) to a Rust byte vector.
fn value_to_bytes(val: &core::Value) -> Vec<u8> {
    let core::Value::VList(elems) = val else {
        panic!("expected Str (List(U8)), got {val:?}");
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

/// Convert a Rust byte slice to a Str value (List(U8)).
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
    // Append newline unless the output already ends with one
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
    if args.len() < 2 {
        eprintln!("usage: ori <file.ori>");
        process::exit(1);
    }
    let content = std::fs::read_to_string(&args[1]).unwrap_or_else(|e| {
        eprintln!("error reading {}: {e}", args[1]);
        process::exit(1);
    });

    let mut arena = SourceArena::new();
    let main_file = arena.add(args[1].clone(), content);

    let source_dir = std::path::Path::new(&args[1]).parent();
    let (program, input_vars) = match compile(&mut arena, main_file, source_dir) {
        Ok(result) => result,
        Err(e) => {
            eprintln!("{}", e.format(&arena));
            process::exit(1);
        }
    };

    // Build List(Str) from command line args (skip binary name and source file)
    let cli_args: Vec<core::Value> = args[2..]
        .iter()
        .map(|a| bytes_to_value(a.as_bytes()))
        .collect();
    let args_value = core::Value::VList(cli_args);

    // Read stdin (empty if terminal, read all if piped)
    let stdin_value = if std::io::stdin().is_terminal() {
        bytes_to_value(b"")
    } else {
        let mut buf = Vec::new();
        std::io::stdin().read_to_end(&mut buf).unwrap();
        bytes_to_value(&buf)
    };

    // Evaluate: main : List(Str), Str -> Result(Str, Str)
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

    // Handle Result(Str, Str) output
    match &result {
        core::Value::VConstruct { tag, fields } => {
            let name = program.debug_names.func_name(*tag);
            match name {
                "Ok" => {
                    print_value(&fields[0]);
                }
                "Err" => {
                    eprint_value(&fields[0]);
                    process::exit(1);
                }
                _ => {
                    println!("{result:?}");
                }
            }
        }
        _ => {
            println!("{result:?}");
        }
    }
}
