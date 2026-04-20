# Records

Records are named, unordered collections of fields:

```ruby
user = { name: "Alice", age: 30 }
point = { x: 1.0, y: 2.0 }
```

Field access uses dot syntax:

```ruby
user.name
point.x
```

Records are the default choice when fields have meaning. The names serve as documentation and prevent accidental field swaps — `{ width: 10, height: 20 }` can't silently become `{ height: 10, width: 20 }`.

## Open records (row polymorphism)

Record types support row polymorphism — a function can accept any record with certain fields, regardless of what other fields it has:

```ruby
get_name : { name: Str, .. } -> Str
get_name = |r| r.name

# Works with any record that has a `name` field
get_name({ name: "Alice", age: 30 })           # "Alice"
get_name({ name: "Bob", email: "bob@x.com" })  # "Bob"
```

The `..` in the type means "and possibly other fields." Without `..`, the record type is closed — extra fields are a type error.

This is what makes dot shorthand work with type variables. `.name` in a callback generates a row constraint:

```ruby
users.map(.name)
# desugars to: users.map(|x| x.name)
# inferred:    users.map(|x : { name: a, .. }| x.name)
```

The compiler infers that `x` must be a record with a `name` field — it doesn't need to know the full record type.

## Record update

```ruby
older = { user & age: 31 }
```

Creates a new record with all fields from `user`, replacing `age`. The original is unchanged.

## Type syntax

```ruby
user : { name: Str, age: I32 }
config : { port: U16, host: Str, debug: Bool }
nested : { point: { x: F64, y: F64 }, label: Str }

transform : { x: F64, y: F64 } -> { x: F64, y: F64 }
```

## Destructuring

```ruby
{ name, age } = user                # bind fields to matching names
{ name: n, age: a } = user          # rename bindings
{ name: _, age } = user             # discard a specific field
{ name, .. } = user                 # ignore extra fields
{ name, ..rest } = user             # capture extra fields as a record
```

Renaming is particularly useful since shadowing is a compile error — if `name` is already bound in scope, rename to get a fresh binding:

```ruby
name = "default"
# ...later...
{ name: user_name, ..} = fetch_user()   # can't rebind name, so rename
```

`..` and `..rest` mirror the list pattern syntax — `..` discards, `..rest` binds. For records, `..rest` captures the remaining fields as a record:

```ruby
{ name, ..rest } = { name: "Alice", age: 30, email: "a@b.com" }
# rest : { age: I32, email: Str }
```

All forms work in `if` arms, function parameters, and irrefutable `let` bindings.

## Nominal and opaque records

Records can be declared as transparent nominal (`:=`) or opaque (`::`) types, following the same rules as [tag unions](tags.md#type-declarations).

**Transparent nominal** — a distinct type, but fields are accessible everywhere:

```ruby
# point.rb
exports [Point]

Point := { x: F64, y: F64 }.(
    origin : Point
    origin = { x: 0.0, y: 0.0 }

    distance : Point, Point -> F64
    distance = |a, b| ((b.x - a.x) ** 2 + (b.y - a.y) ** 2).sqrt()
)
```

```ruby
# another module
import point exposing [Point]

p = Point.origin
p.x                          # field access works — internals visible
{ p & y: 3.0 }              # record update works

# Construction via type context — bare record unifies with Point
make_point : F64, F64 -> Point
make_point = |x, y| { x, y }

# Same when passing to a function that expects Point
distance({ x: 0.0, y: 0.0 }, { x: 3.0, y: 4.0 })
```

**Opaque** — inside the defining module, the type is transparent. Outside, only the public API is available:

```ruby
# user.rb
exports [User]

User :: { name: Str, age: I32, email: Str }.(
    new : Str, I32, Str -> Result(User, [InvalidUser])
    new = |name, age, email|
        if age > 0 and name.count_graphemes() > 0
            then Ok({ name, age, email })    # construct directly — module sees internals
            else Err(InvalidUser)

    name : User -> Str
    name = |u| u.name                        # field access works inside

    birthday : User -> User
    birthday = |u| { u & age: u.age + 1 }   # record update works inside
)
```

```ruby
# another module
import user exposing [User]

u = User.new("Alice", 30, "alice@x.com")
User.name(u)                 # through the API
# u.name                     # COMPILE ERROR — fields hidden
# { u & age: 31 }            # COMPILE ERROR — can't see fields
```

The module is the visibility boundary — same model as [opaque tag unions](tags.md#opaque-types) and [opaque tuples](tuples.md#nominal-and-opaque-tuples).

## Unit type

`{}` is the unit type — the empty record. It represents "no meaningful value" and is used for functions called purely for effects:

```ruby
greet : Str -> {}
greet = |name| print("hello ${name}")

default : {} -> Config
```

See [tuples](tuples.md#unit-type) for the full rationale on why `{}` instead of `()`.

## Design rationale

> Why records instead of positional arguments?

Named fields prevent accidental argument swaps — `create_user("Alice", 30)` is fragile, `create_user({ name: "Alice", age: 30 })` is self-documenting. Records also compose better: you can spread, update, and destructure them without knowing the full set of fields (via row polymorphism).

> Why unordered fields?

Field order shouldn't matter for equality or type compatibility. `{ name: "Alice", age: 30 }` and `{ age: 30, name: "Alice" }` are the same value. This matches the mental model (records are bags of named fields) and avoids a class of bugs where reordering fields changes behavior.
