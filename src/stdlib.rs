pub fn get(name: &str) -> Option<&'static str> {
    match name {
        "list" | "List" => Some(include_str!("../standard/list.ori")),
        "bool" | "Bool" => Some(include_str!("../standard/bool.ori")),
        "result" | "Result" => Some(include_str!("../standard/result.ori")),
        "str" | "Str" => Some(include_str!("../standard/str.ori")),
        _ => None,
    }
}

/// Return all stdlib modules as (name, source) pairs.
#[allow(dead_code)]
pub fn all() -> Vec<(&'static str, &'static str)> {
    vec![
        ("Bool", include_str!("../standard/bool.ori")),
        ("Result", include_str!("../standard/result.ori")),
        ("List", include_str!("../standard/list.ori")),
        ("Str", include_str!("../standard/str.ori")),
    ]
}
