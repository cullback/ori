//! Numeric helpers: integer-constant emission by width, and bit-cast
//! destination-type resolution for `<T>.to_bits()`.

use crate::ssa::Value;
use crate::ssa::builder::Builder;
use crate::ssa::instruction::ScalarType;
use crate::types::engine::Type;

/// Destination type for `<T>.to_bits` by type name. Each signed
/// integer maps to its same-width unsigned counterpart; F64 to U64.
/// Panics for types that don't support `to_bits`.
pub fn bits_dest_ty(type_name: &str) -> ScalarType {
    match type_name {
        "I8" => ScalarType::U8,
        "I16" => ScalarType::U16,
        "I32" => ScalarType::U32,
        "I64" | "F64" => ScalarType::U64,
        other => panic!("to_bits not supported on {other}"),
    }
}

/// Destination type for `value.to_bits()` given the receiver's
/// inferred type. Same mapping as `bits_dest_ty` but driven from a
/// `Type` instead of a type-name string.
pub fn bits_dest_ty_for_ty(ty: &Type) -> ScalarType {
    let name = match ty {
        Type::Con(name) | Type::App(name, _) => name.as_str(),
        _ => panic!("to_bits receiver not a nominal numeric type"),
    };
    bits_dest_ty(name)
}

/// Emit an SSA constant for an integer literal, dispatching to the
/// correct width based on the resolved type.
#[expect(
    clippy::cast_sign_loss,
    clippy::cast_precision_loss,
    clippy::cast_possible_truncation,
    reason = "integer literal width dispatch"
)]
pub fn lower_int_const(builder: &mut Builder, n: i64, ty: &Type) -> Value {
    use crate::numeric::NumericType;
    if let Type::Con(name) = ty {
        if let Some(num) = NumericType::from_name(name) {
            return match num {
                NumericType::I8 => builder.const_i8(n as i8),
                NumericType::U8 => builder.const_u8(n as u8),
                NumericType::I16 => builder.const_i16(n as i16),
                NumericType::U16 => builder.const_u16(n as u16),
                NumericType::I32 => builder.const_i32(n as i32),
                NumericType::U32 => builder.const_u32(n as u32),
                NumericType::I64 => builder.const_i64(n),
                NumericType::U64 => builder.const_u64(n as u64),
                NumericType::F64 => builder.const_f64(n as f64),
            };
        }
    }
    builder.const_i64(n)
}
