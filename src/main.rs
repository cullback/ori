mod core;
mod lower;
mod resolve;
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: ori <file.ori>");
        process::exit(1);
    }
    let source = std::fs::read_to_string(&args[1]).unwrap_or_else(|e| {
        eprintln!("error reading {}: {e}", args[1]);
        process::exit(1);
    });

    // Compile (catch panics from parser/type checker and print cleanly)
    std::panic::set_hook(Box::new(|_| {}));
    let source_dir = std::path::Path::new(&args[1]).parent();
    let compile_result = std::panic::catch_unwind(|| {
        let parsed = syntax::parse::parse(&source);
        let resolved = resolve::resolve_imports(parsed, source_dir);
        let infer_result = types::infer::check(&source, &resolved.module, &resolved.scope);
        lower::lower(&resolved.module, &resolved.scope, &infer_result)
    });
    drop(std::panic::take_hook());
    let (program, input_var) = match compile_result {
        Ok(result) => result,
        Err(e) => {
            let msg = if let Some(s) = e.downcast_ref::<String>() {
                s.as_str()
            } else if let Some(s) = e.downcast_ref::<&str>() {
                s
            } else {
                "unknown error"
            };
            eprintln!("{msg}");
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
