/// All stdlib module names, in dependency order. Auto-imported at the
/// top of every compilation so their declarations (types, constructors,
/// and body-less method signatures) are in scope everywhere.
pub const MODULES: &[&str] = &[
    // Dependency order: Bool first (no deps), then Order (no deps),
    // then numeric types (reference Bool, Order), then Result,
    // List (references U64), Str (references List, U8, U64, Bool).
    "Bool", "Order",
    "I8", "U8", "I16", "U16", "I32", "U32", "I64", "U64", "F64",
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
        "i16" | "I16" => Some(include_str!("../standard/i16.ori")),
        "u16" | "U16" => Some(include_str!("../standard/u16.ori")),
        "i32" | "I32" => Some(include_str!("../standard/i32.ori")),
        "u32" | "U32" => Some(include_str!("../standard/u32.ori")),
        "i64" | "I64" => Some(include_str!("../standard/i64.ori")),
        "u64" | "U64" => Some(include_str!("../standard/u64.ori")),
        "f64" | "F64" => Some(include_str!("../standard/f64.ori")),
        "order" | "Order" => Some(include_str!("../standard/order.ori")),
        _ => None,
    }
}
