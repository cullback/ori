/// All stdlib module names, in dependency order. Auto-imported at the
/// top of every compilation so their declarations (types, constructors,
/// and body-less method signatures) are in scope everywhere.
pub const MODULES: &[&str] = &[
    // Dependency order: Bool first (no deps), then numeric types
    // (reference Bool in eq/neq), then Result, List (references U64),
    // Str (references List, U8, U64, Bool).
    "Bool", "I8", "U8", "I64", "U64", "F64",
    "Result", "List", "Str",
];

pub fn get(name: &str) -> Option<&'static str> {
    match name {
        "list" | "List" => Some(include_str!("../standard/list.ori")),
        "bool" | "Bool" => Some(include_str!("../standard/bool.ori")),
        "result" | "Result" => Some(include_str!("../standard/result.ori")),
        "str" | "Str" => Some(include_str!("../standard/str.ori")),
        "i8" | "I8" => Some(include_str!("../standard/i8.ori")),
        "u8" | "U8" => Some(include_str!("../standard/u8.ori")),
        "i64" | "I64" => Some(include_str!("../standard/i64.ori")),
        "u64" | "U64" => Some(include_str!("../standard/u64.ori")),
        "f64" | "F64" => Some(include_str!("../standard/f64.ori")),
        _ => None,
    }
}
