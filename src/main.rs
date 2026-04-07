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
use std::io::Read as _;
use std::process;

use error::CompileError;
use source::SourceArena;

fn compile(
    arena: &SourceArena,
    main_file: source::FileId,
    source_dir: Option<&std::path::Path>,
) -> Result<(crate::core::Program, crate::core::VarId), CompileError> {
    let parsed = syntax::parse::parse(arena.content(main_file), main_file)?;
    let resolved = resolve::resolve_imports(parsed, arena, source_dir)?;
    let infer_result = types::infer::check(arena, &resolved.module, &resolved.scope)?;
    lower::lower(arena, &resolved.module, &resolved.scope, &infer_result)
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

    let arena = SourceArena::new();
    let main_file = arena.add(args[1].clone(), content);

    let source_dir = std::path::Path::new(&args[1]).parent();
    let (program, input_var) = match compile(&arena, main_file, source_dir) {
        Ok(result) => result,
        Err(e) => {
            eprintln!("{}", e.format(&arena));
            process::exit(1);
        }
    };

    // Read input from stdin
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input).unwrap();
    let number: i64 = input.trim().parse().unwrap_or_else(|e| {
        eprintln!("error parsing input: {e}");
        process::exit(1);
    });

    // Evaluate
    let mut env = HashMap::new();
    env.insert(input_var, core::Value::VNum(core::NumVal::I64(number)));
    let result = core::eval::eval(&env, &program, &program.main);

    // Print result
    match result {
        core::Value::VNum(core::NumVal::U8(n)) => println!("{n}"),
        core::Value::VNum(core::NumVal::I8(n)) => println!("{n}"),
        core::Value::VNum(core::NumVal::I64(n)) => println!("{n}"),
        core::Value::VNum(core::NumVal::U64(n)) => println!("{n}"),
        core::Value::VNum(core::NumVal::F64(n)) => println!("{n}"),
        core::Value::VConstruct { .. } | core::Value::VRecord { .. } | core::Value::VList(_) => {
            println!("{result:?}");
        }
    }
}
