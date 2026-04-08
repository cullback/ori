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

use std::io::IsTerminal as _;
use std::io::Read as _;
use std::io::Write as _;
use std::process;

use error::CompileError;
use source::SourceArena;
use ssa::eval::RtValue;

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
    let infer_result = types::infer::check(arena, &resolved.module, &resolved.scope)?;
    lower::lower(arena, &resolved.module, &resolved.scope, &infer_result)
}

fn bytes_to_rt(bytes: &[u8]) -> RtValue {
    RtValue::List(bytes.iter().map(|&b| RtValue::U8(b)).collect())
}

fn rt_to_bytes(val: &RtValue) -> Vec<u8> {
    let RtValue::List(elems) = val else {
        panic!("expected Str, got {val:?}");
    };
    elems
        .iter()
        .map(|e| {
            let RtValue::U8(b) = e else {
                panic!("expected U8 in Str, got {e:?}");
            };
            *b
        })
        .collect()
}

fn print_rt(val: &RtValue) {
    match val {
        RtValue::List(_) => {
            let bytes = rt_to_bytes(val);
            std::io::stdout().write_all(&bytes).unwrap();
        }
        RtValue::I64(n) => print!("{n}"),
        RtValue::U64(n) => print!("{n}"),
        RtValue::F64(n) => print!("{n}"),
        RtValue::U8(n) => print!("{n}"),
        RtValue::I8(n) => print!("{n}"),
        other => print!("{other:?}"),
    }
    if let RtValue::List(elems) = val
        && elems.last() == Some(&RtValue::U8(b'\n'))
    {
        return;
    }
    println!();
}

fn eprint_rt(val: &RtValue) {
    match val {
        RtValue::List(_) => {
            let bytes = rt_to_bytes(val);
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

    // Lower Core → SSA
    let ssa_module = ssa::lower::lower(&program, &input_vars);

    // Build inputs
    let cli_args: Vec<RtValue> = args[2..]
        .iter()
        .map(|a| bytes_to_rt(a.as_bytes()))
        .collect();
    let args_value = RtValue::List(cli_args);

    let stdin_value = if std::io::stdin().is_terminal() {
        bytes_to_rt(b"")
    } else {
        let mut buf = Vec::new();
        std::io::stdin().read_to_end(&mut buf).unwrap();
        bytes_to_rt(&buf)
    };

    // Build the argument list matching the input_vars
    let mut main_args = Vec::new();
    for i in 0..input_vars.len() {
        match i {
            0 => main_args.push(args_value.clone()),
            1 => main_args.push(stdin_value.clone()),
            _ => main_args.push(RtValue::List(vec![])),
        }
    }

    // Evaluate via SSA
    let result = ssa::eval::eval(&ssa_module, &main_args);

    // Handle Result output
    match &result {
        RtValue::Construct { tag, fields } => match tag.as_str() {
            "Ok" => print_rt(&fields[0]),
            "Err" => {
                eprint_rt(&fields[0]);
                process::exit(1);
            }
            _ => println!("{result:?}"),
        },
        _ => println!("{result:?}"),
    }
}
