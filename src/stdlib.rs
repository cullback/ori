pub fn get(name: &str) -> Option<&'static str> {
    match name {
        "list" | "List" => Some(include_str!("../standard/list.ori")),
        "bool" | "Bool" => Some(include_str!("../standard/bool.ori")),
        "result" | "Result" => Some(include_str!("../standard/result.ori")),
        _ => None,
    }
}
