/// All stdlib module names, in dependency order.
pub const MODULES: &[&str] = &["Bool", "Result", "List", "Str"];

pub fn get(name: &str) -> Option<&'static str> {
    match name {
        "list" | "List" => Some(include_str!("../standard/list.ori")),
        "bool" | "Bool" => Some(include_str!("../standard/bool.ori")),
        "result" | "Result" => Some(include_str!("../standard/result.ori")),
        "str" | "Str" => Some(include_str!("../standard/str.ori")),
        _ => None,
    }
}
