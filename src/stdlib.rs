pub fn get(name: &str) -> Option<&'static str> {
    match name {
        "List" => Some(LIST),
        _ => None,
    }
}

const LIST: &str = "\
List(a) : [Nil, Cons(a, List(a))].(
    sum : List(I64) -> I64
    sum = |xs| fold xs
        : Nil then 0
        : Cons(hd, rest) then hd + rest

    length : List(a) -> I64
    length = |xs| fold xs
        : Nil then 0
        : Cons(_, rest) then rest + 1

    map : List(a), (a -> a) -> List(a)
    map = |xs, f| fold xs
        : Nil then Nil
        : Cons(hd, rest) then Cons(f(hd), rest)

    walk : List(a), b, (b, a -> b) -> b
    walk = |xs, init, f| fold xs
        : Nil then init
        : Cons(hd, acc) then f(acc, hd)

    reverse : List(a) -> List(a)
    reverse = |xs| List.walk(xs, Nil, |acc, x| Cons(x, acc))
)
";
