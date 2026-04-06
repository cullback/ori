pub fn get(name: &str) -> Option<&'static str> {
    match name {
        "list" | "List" => Some(include_str!("../standard/list.ori")),
        _ => None,
    }
}
