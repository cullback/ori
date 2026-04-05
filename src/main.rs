mod ast;
mod builder;
mod eval;
mod infer;
mod ir;
mod lower;
mod parse;
#[cfg(test)]
mod test_frontend;
#[cfg(test)]
mod test_programs;

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

    // Compile
    let module = parse::parse(&source);
    infer::check(&source, &module);
    let (program, input_var) = lower::lower(&module);

    // Read input from stdin
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input).unwrap();
    let number: i64 = input.trim().parse().unwrap_or_else(|e| {
        eprintln!("error parsing input: {e}");
        process::exit(1);
    });

    // Evaluate
    let mut env = HashMap::new();
    env.insert(input_var, ir::Value::VNum(ir::NumVal::I64(number)));
    let result = eval::eval(&env, &program, &program.main);

    // Print result
    match result {
        ir::Value::VNum(ir::NumVal::I64(n)) => println!("{n}"),
        ir::Value::VNum(ir::NumVal::U64(n)) => println!("{n}"),
        ir::Value::VNum(ir::NumVal::F64(n)) => println!("{n}"),
        ir::Value::VConstruct { .. } | ir::Value::VRecord { .. } => println!("{result:?}"),
    }
}
