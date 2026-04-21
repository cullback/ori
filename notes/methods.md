# Methods

Methods are functions, constants, and derived implementations attached to a type via the `.( )` block. The block defines the type's interface — everything callable through the type name. Dot dispatch is a convenience that falls out when the first parameter's type matches.

```ruby
Path := [Unix(List(U8)), Windows(List(U8))].(
    from_bytes : List(U8) -> Path
    to_bytes : Path -> List(U8)
    normalize : Path -> Path
    equals : _
    hash : _
)
```

## The `.( )` block

The `.( )` block contains both signatures and implementations. Derived functions use a signature with no body; everything else pairs a signature with its implementation:

```ruby
Color := [Red, Green, Blue].(
    to_hex : Color -> Str
    to_hex = |color|
        if color
            : Red then "#FF0000"
            : Green then "#00FF00"
            : Blue then "#0000FF"

    equals : _
    hash : _
)
```

Implementations must be inside the block — not as free functions in the module body. This avoids name collisions when a module defines multiple types with same-named methods (e.g. two types with `to_str`), and keeps each type's implementation self-contained.

The block is about *dispatch*, not *visibility* — visibility is controlled by [exports](modules.md#exports). The `.( )` block says "these functions can be called through the type name and with dot syntax." Private helpers are free functions in the module, not methods on the type.

Only nominal (`:=`) and opaque (`::`) types can have methods. Aliases (`:`) cannot — they're just names for existing types, not distinct types. The underlying type can be anything — tags, records, tuples, or scalars:

```ruby
UserId := U64.(
    from_u64 : U64 -> UserId
    from_u64 = |n| n

    to_u64 : UserId -> U64
    to_u64 = |id| id
)

Username :: Str.(
    from_str : Str -> Result(Username, [InvalidUsername])
    from_str = |s|
        if s.count_graphemes() > 0 and s.count_graphemes() <= 20
            then Ok(s)
            else Err(InvalidUsername)
)
```

The `|n| n` identity functions may look like no-ops, but the type annotation is doing the work. In `from_u64 : U64 -> UserId`, the return type tells the compiler to wrap the `U64` as a `UserId`. In `to_u64 : UserId -> U64`, the return type tells it to unwrap. This is the same context-based construction that [transparent nominal tags](tags.md#constructor-access) use — bare values unify with the nominal type when the context expects it.

There's no special `UserId(42)` constructor syntax. `UserId` is a type, not a function — making it callable would blur the type/value distinction and raise questions like "can I pass `UserId` to `map`?" The `from`/`to` methods are explicit, discoverable, and give opaque types a natural place to add validation:

```ruby
# Transparent — trivial wrapping
id = UserId.from_u64(42)
raw = id.to_u64()

# Opaque — validation at construction
name = Username.from_str("alice")   # Ok(Username) or Err(InvalidUsername)
```

## Calling conventions

Methods can be called two ways:

**Through the type name** — `Type.function(args)`:

```ruby
Path.from_bytes(bytes)         # static call
Color.to_hex(my_color)         # static call
Dict.get(d, "key")             # static call
```

**Dot syntax** — the value is passed as the first argument:

```ruby
path.normalize()               # same as Path.normalize(path)
my_color.to_hex()              # same as Color.to_hex(my_color)
d.get("key")                   # same as Dict.get(d, "key")
```

Dot syntax works when the value's type matches the first parameter's type. `path.normalize()` works because `normalize` takes a `Path` and `path` is a `Path`. `bytes.from_bytes()` would not — `from_bytes` takes `List(U8)`, so the compiler looks for `from_bytes` on `List`, not `Path`. Constructors like `from_bytes` use the static call form.

Dot dispatch resolves at compile time based on the value's type — there are no vtables, no runtime lookup.

## The `->` operator

When chaining calls across types, `->` pipes the value as the first argument to a named type's function:

```ruby
"1\n2\n3"
  .split_on("\n")
  ->Str.join_with(" ")
  ->Stdout.line!
```

Dot (`.`) dispatches on the value's own type. Arrow (`->`) dispatches on a specific type — useful when the target type differs from the value's type, or when you want to be explicit.

## Derivation

Certain functions have a natural default implementation based on a type's structure. Derivation lets you opt into these **structural defaults** by writing a type annotation with no body. No macros, no reflection, no `derive` keyword — the compiler knows the structure of every type and can generate the code directly.

```ruby
User :: { name: Str, age: I32 }.(
    equals : User, User -> Bool
    hash : _
    compare : _
    to_str : _
    encode : _
    decode : _
)
```

No body means derivation, body means custom. If the annotation doesn't match the structural default, the compiler reports an error.

```ruby
hash : _               # derived — compiler picks the signature
hash : User -> U64     # derived — you wrote it out, matches the default
hash : User -> Str     # error — doesn't match the structural default
hash : User -> U64     # custom — provide an implementation
hash = |user| ...      #   and derivation is skipped
```

### Who gets what automatically

Structural types (anonymous records and tag unions) auto-derive `equals`, `hash`, and `to_str` — no annotation needed. The capability propagates from components: a record has `equals` if all its field types have `equals`, a tag union has `equals` if all its payload types have `equals`.

Nominal types — both transparent (`:=`) and opaque (`::`) — must explicitly opt in. Write `equals : _` in the `.()` block to derive it, or provide a custom implementation.

```ruby
# Structural — auto-derived, no annotation
point = { x: 1.0, y: 2.0 }
point == { x: 1.0, y: 2.0 }      # works — records get equals automatically

# Nominal — must opt in
Color := [Red, Green, Blue].(equals : _, hash : _, to_str : _)
Red == Blue                        # works — explicitly derived

# Opaque — must opt in
Username :: Str.(
    equals : _                     # structural equality on the inner Str
    to_str : Username -> Str       # custom — don't expose internals
    to_str = |s| s
)
```

This is roughly the same amount of ceremony as Rust's `#[derive(PartialEq, Hash, Debug)]` — you list what you want, and the compiler generates it. The advantage over auto-deriving for all types: nominal types have intentional APIs, and the author controls which capabilities the type supports.

### Structural defaults

**Equals** — structural equality. Two values are equal if all their fields/variants are equal. For records, compares each field. For tag unions, checks the tag matches and payloads are equal.

**Hash** — structural hashing. Hashes each field/variant component and combines them. Implies Equals (the `Hash` constraint includes `Eq`).

**Compare** — structural ordering. For records, compares fields in declaration order. For tag unions, compares by variant order then by payload. Returns `Order` (`Lt`, `Eq`, `Gt`).

**to_str** — structural string representation. Produces a developer-readable string showing the type's structure: `{ name: "Alice", age: 30 }` for records, `Circle(5.0)` for tag unions. This is what string interpolation (`${}`) calls.

**dbg** — a compiler-provided expression for printf-style debugging. Prints the expression text, its value (via `to_str`), and the file/line location to stderr. Works on any type without requiring constraints.

**Encode** — produces a format-agnostic description of the value's structure that a format (JSON, binary, etc.) turns into bytes.

**Decode** — the inverse: takes format-specific bytes and builds a value using a format-agnostic structural description.

### Encode and Decode — usage

Define a type with `encode : _` and `decode : _`, then call `Encode.to_bytes` / `Decode.from_bytes` with a format:

```ruby
import user exposing [User]
import json exposing [Json]
import encode exposing [Encode]
import decode exposing [Decode]

user = User.new("Alice", 30)

# Encode
bytes = Encode.to_bytes(user, Json.utf8())
# → {"name":"Alice","age":30}

# Decode
result : Result(User, DecodeErr)
result = Decode.from_bytes(bytes, Json.utf8())
```

Same type, different format — the only thing that changes is the call site:

```ruby
json_bytes = Encode.to_bytes(user, Json.utf8())
yaml_bytes = Encode.to_bytes(user, Yaml.default())
binary_bytes = Encode.to_bytes(user, Binary.default())
```

Naming conventions are configured on the format, not the type:

```ruby
decoder = Json.utf8_with({ field_name_mapping: PascalCase })
user = Decode.from_bytes(input, decoder)
# Parses {"Name":"Alice","Age":30} into { name: "Alice", age: 30 }
```

Nested types compose automatically:

```ruby
Team :: { name: Str, members: List(User) }.(encode : _, decode : _)

bytes = Encode.to_bytes(team, Json.utf8())
# {"name":"Engineering","members":[{"name":"Alice","age":30},{"name":"Bob","age":25}]}
```

Tag unions use the format's representation:

```ruby
Shape := [Circle(F64), Rect(F64, F64)].(encode : _, decode : _)

Encode.to_bytes(Shape.Circle(5.0), Json.utf8())
# {"tag":"Circle","payload":[5.0]}
```

For the rare case where field names don't match, write a custom decoder:

```ruby
User :: { name: Str, age: I32 }.(
    encode : _
    decoder : Decoder(User, fmt)
    decoder = Decode.succeed(|name, age| { name, age })
        ->Decode.field("user_name", Str.decoder)
        ->Decode.field("user_age", I32.decoder)
)
```

### Encode and Decode — internals

Encode and decode are format-polymorphic. They don't produce bytes directly — they describe structure, and a format handles the byte representation.

```ruby
a.Encode(fmt) : [a.to_encoder : a -> Encoder(fmt)]
a.Decode(fmt) : [a.decoder : Decoder(a, fmt)]
```

The `fmt` parameter is the format — JSON, YAML, binary, etc. You always pair encode/decode with a format at the call site.

#### Core types

```ruby
# Appends encoded bytes to a buffer, using format config
Encoder(fmt) := (List(U8), fmt -> List(U8))

# Consumes bytes, produces a value + remaining bytes
Decoder(a, fmt) := (List(U8), fmt -> DecodeResult(a))
DecodeResult(a) : { result: Result(a, DecodeErr), rest: List(U8) }
```

An `Encoder` is a pending operation — it captures _what_ to encode, and runs later when given a byte buffer and format config. A `Decoder` consumes bytes from the front and returns the decoded value plus remaining bytes, allowing sequential parsing.

#### Format constraint

Every format implements methods for encoding and decoding each value kind:

```ruby
fmt.EncoderFormat : [
    fmt.encode_u8 : U8 -> Encoder(fmt),
    fmt.encode_i32 : I32 -> Encoder(fmt),
    fmt.encode_f64 : F64 -> Encoder(fmt),
    fmt.encode_str : Str -> Encoder(fmt),
    fmt.encode_bool : Bool -> Encoder(fmt),
    fmt.encode_list : List(Encoder(fmt)) -> Encoder(fmt),
    fmt.encode_record : List({ key: Str, value: Encoder(fmt) }) -> Encoder(fmt),
    fmt.encode_tag : Str, List(Encoder(fmt)) -> Encoder(fmt),
]

fmt.DecoderFormat : [
    fmt.decode_u8 : Decoder(U8, fmt),
    fmt.decode_i32 : Decoder(I32, fmt),
    fmt.decode_f64 : Decoder(F64, fmt),
    fmt.decode_str : Decoder(Str, fmt),
    fmt.decode_bool : Decoder(Bool, fmt),
    fmt.decode_list : Decoder(a, fmt) -> Decoder(List(a), fmt),
    fmt.decode_record : state, (state, Str -> [Keep(Decoder(state, fmt)), Skip])
        -> Decoder(state, fmt),
]
```

#### What the compiler generates — encoding

For `User :: { name: Str, age: I32 }.(encode : _)`:

```ruby
to_encoder : User -> Encoder(fmt) where [fmt.EncoderFormat]
to_encoder = |user| (
    import fmt as Fmt
    Fmt.encode_record([
        { key: "name", value: Fmt.encode_str(user.name) },
        { key: "age", value: Fmt.encode_i32(user.age) },
    ])
)
```

For tag unions like `Shape := [Circle(F64), Rect(F64, F64)]`:

```ruby
to_encoder : Shape -> Encoder(fmt) where [fmt.EncoderFormat]
to_encoder = |shape| (
    import fmt as Fmt
    if shape
        is Circle(r) then Fmt.encode_tag("Circle", [Fmt.encode_f64(r)])
        is Rect(w, h) then Fmt.encode_tag("Rect", [Fmt.encode_f64(w), Fmt.encode_f64(h)])
)
```

#### What the compiler generates — decoding

For `User :: { name: Str, age: I32 }.(decode : _)`:

```ruby
decoder : Decoder(User, fmt) where [fmt.DecoderFormat]
decoder = (
    import fmt as Fmt
    Fmt.decode_record(
        |name, age| { name, age },
        |_state, key|
            if key == "name" then Keep(Fmt.decode_str())
            else if key == "age" then Keep(Fmt.decode_i32())
            else Skip
    )
)
```

#### Traced example — encoding

```ruby
Encode.to_bytes({ name: "Alice", age: 30 }, Json.utf8())
```

1. `Encode.to_bytes` calls `user.to_encoder()`, which (since fmt=Json) produces:
   `Json.encode_record([{ key: "name", value: Json.encode_str("Alice") }, ...])`
2. Returns an `Encoder(Json)` — a pending function, no bytes yet
3. `Encode.to_bytes` runs it with an empty buffer and the Json config
4. `encode_record` iterates the fields, checking `field_name_mapping` (None → no change)
5. `Json.encode_str("Alice")` writes `"Alice"`, `Json.encode_i32(30)` writes `30`
6. Wraps in braces: `{"name":"Alice","age":30}`

#### Traced example — decoding

```ruby
user : User
user = Decode.from_bytes("{\"name\":\"Alice\",\"age\":30}".to_utf8(), Json.utf8())
```

1. `Decode.from_bytes` uses `User.decoder` (inferred from return type)
2. `User.decoder` calls `Json.decode_record(constructor, step_fn)`
3. Json parses `{`, finds key `"name"`:
   - `step_fn(state, "name")` → `Keep(Json.decode_str())`
   - Parses `"Alice"`, applies to constructor → `|age| { name: "Alice", age }`
4. Finds key `"age"`:
   - `step_fn(state, "age")` → `Keep(Json.decode_i32())`
   - Parses `30`, applies to constructor → `{ name: "Alice", age: 30 }`
5. Parses `}` → returns `Ok({ name: "Alice", age: 30 })`

Field order in JSON doesn't matter — the step function matches by name.

#### How a format satisfies the constraint

A sketch of Json's encoding methods:

```ruby
Json :: { field_name_mapping: [None, PascalCase, CamelCase, SnakeCase] }.(
    utf8 : Json
    utf8 = { field_name_mapping: None }

    utf8_with : { field_name_mapping: [None, PascalCase, CamelCase, SnakeCase] } -> Json
    utf8_with = |config| config

    encode_str : Str -> Encoder(Json)
    encode_str = |s| Encoder(|bytes, _json|
        bytes.append('"').concat(escape_json(s)).append('"')
    )

    encode_i32 : I32 -> Encoder(Json)
    encode_i32 = |n| Encoder(|bytes, _json|
        bytes.concat(n.to_str().to_utf8())
    )

    encode_record : List({ key: Str, value: Encoder(Json) }) -> Encoder(Json)
    encode_record = |fields| Encoder(|bytes, json| (
        entries = fields.map(|f| (
            key = apply_mapping(json.field_name_mapping, f.key)
            Encoder.run(Json.encode_str(key), [], json)
                .append(':')
                .concat(Encoder.run(f.value, [], json))
        ))
        bytes.append('{').concat(entries->Bytes.join(',')).append('}')
    ))

    encode_tag : Str, List(Encoder(Json)) -> Encoder(Json)
    encode_tag = |name, payloads|
        if payloads.is_empty()
            then Json.encode_str(name)
            else Json.encode_record([
                { key: "tag", value: Json.encode_str(name) },
                { key: "payload", value: Json.encode_list(payloads) },
            ])
)
```

### Performance

The encode/decode architecture is structurally similar to Rust's serde: compile-time code generation, format-polymorphic via a type parameter that monomorphizes away, and a visitor-style pattern where the generated code calls format methods.

After monomorphization (fmt=Json) and inlining, the compiler transforms:

```ruby
# Generated code
Json.encode_record([
    { key: "name", value: Json.encode_str("Alice") },
    { key: "age", value: Json.encode_i32(30) },
])
```

Into sequential buffer appends:

```ruby
# After inlining — closures, field list, encode_record all gone
bytes
    .append('{')
    .append('"').concat("name".to_utf8()).append('"').append(':')
    .append('"').concat(escape_json("Alice")).append('"')
    .append(',')
    .append('"').concat("age".to_utf8()).append('"').append(':')
    .concat("30".to_utf8())
    .append('}')
```

Derivation is part of the compiler, not a separate code generation step. The optimizer sees the full picture — from `Encode.to_bytes` through the generated `to_encoder` through `Json.encode_record` — and can inline across all boundaries.

**Where this falls short of serde:** Zero-copy deserialization. Serde can borrow `&str` directly from input bytes via Rust's lifetime system. In a pure functional language with reference counting, strings are copied during decoding.

## Design rationale

> Why attach functions to types instead of using typeclasses/traits?

The type's module is the single authority for its functions — no third party can define functions on a type they don't own. This eliminates orphan rules, coherence problems, and the "where does this impl come from?" question. The tradeoff (no ad-hoc extension) is offset by [constraints](constraints.md), which provide interface polymorphism structurally.

> Why must implementations live inside the `.( )` block?

Name collisions. A module can define multiple types, and those types can have same-named methods (`to_str`, `equals`). If implementations were free functions in the module body, two types with `to_str` would collide. Scoping implementations inside the block avoids this entirely — each type's `to_str` lives in its own block.

This also makes opaque type access cleaner. Code inside the `.( )` block can see the type's internals; code outside cannot, even in the same module. The block is the trust boundary for the type's representation, not the module. This means a free function copied between modules works identically regardless of where it lives — no module-specific privileges.

> Why `.( )` syntax specifically?

The dot visually connects the block to the type, and parens group the contents. `Color := [Red, Green, Blue].( ... )` reads naturally as "Color is this union, with these functions." The syntax also works with the bracket notation for tag unions — `[...].( )` chains directly.

> Why no `derive` keyword or attribute?

A bare type annotation with no body is unambiguous — the compiler sees a signature it knows how to implement and generates the structural default. No new syntax needed. Derived and hand-written implementations use the same mechanism — the only difference is whether you provide a body.

> Why format-polymorphic encode/decode instead of encoding directly to bytes?

Separating structure description from byte representation means one `encode : _` annotation works for every format. The format is chosen at the call site, not the type definition. This directly addresses Rust's serde ecosystem lock-in — in Rust, if a competing serialization library appears, every crate needs updating, and the orphan rules prevent third parties from bridging the gap. In Ori, a type derives `encode : _` once, and that works for all formats — current and future.

> Why put field name mapping on the format instead of the type?

Naming conventions are about the serialization context, not the type. The same `User` type might need PascalCase for one API and snake_case for another. Putting this on the format keeps the type definition clean.

> Why one `to_str` instead of separate Display and Debug?

Most languages with two string representations (Rust's `Display`/`Debug`, Python's `__str__`/`__repr__`) find that developers constantly confuse which to implement and when. User-facing formatting is always domain-specific (`price.format(locale)`, not `price.to_str()`). Ori picks the simple path: one `to_str`, auto-derived for structural types, called by `${}` interpolation.

> Why no PartialEq / PartialOrd split?

Rust separates `PartialEq`/`Eq` and `PartialOrd`/`Ord` because IEEE 754 says `NaN != NaN`. This means four constraints instead of two, floats can't be dict keys without workarounds, and every generic function must choose partial or total. Ori uses total equality and total ordering on floats: `NaN == NaN` is `True`, NaN sorts after positive infinity. This follows Java and Kotlin's approach. The tradeoff is deviating from IEEE 754's NaN semantics, but that behavior causes more bugs than it prevents.
