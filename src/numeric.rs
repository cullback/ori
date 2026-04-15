//! Centralized definition of the compiler's numeric types.
//!
//! Every numeric type name, its properties, and its mapping to SSA
//! `ScalarType` are defined here. Other passes reference this enum
//! instead of hardcoding type-name strings.

use crate::ssa::ScalarType;

/// The numeric types supported by the compiler.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumericType {
    I8,
    U8,
    I16,
    U16,
    I32,
    U32,
    I64,
    U64,
    F64,
}

/// All numeric type variants, in canonical order.
pub const ALL: &[NumericType] = &[
    NumericType::I8,
    NumericType::U8,
    NumericType::I16,
    NumericType::U16,
    NumericType::I32,
    NumericType::U32,
    NumericType::I64,
    NumericType::U64,
    NumericType::F64,
];

impl NumericType {
    /// Parse a type name string into a `NumericType`, if it matches.
    pub fn from_name(s: &str) -> Option<Self> {
        match s {
            "I8" => Some(Self::I8),
            "U8" => Some(Self::U8),
            "I16" => Some(Self::I16),
            "U16" => Some(Self::U16),
            "I32" => Some(Self::I32),
            "U32" => Some(Self::U32),
            "I64" => Some(Self::I64),
            "U64" => Some(Self::U64),
            "F64" => Some(Self::F64),
            _ => None,
        }
    }

    /// The type name as it appears in source code and the AST.
    pub const fn name(self) -> &'static str {
        match self {
            Self::I8 => "I8",
            Self::U8 => "U8",
            Self::I16 => "I16",
            Self::U16 => "U16",
            Self::I32 => "I32",
            Self::U32 => "U32",
            Self::I64 => "I64",
            Self::U64 => "U64",
            Self::F64 => "F64",
        }
    }

    /// The corresponding SSA scalar type.
    pub const fn scalar_type(self) -> ScalarType {
        match self {
            Self::I8 => ScalarType::I8,
            Self::U8 => ScalarType::U8,
            Self::I16 => ScalarType::I16,
            Self::U16 => ScalarType::U16,
            Self::I32 => ScalarType::I32,
            Self::U32 => ScalarType::U32,
            Self::I64 => ScalarType::I64,
            Self::U64 => ScalarType::U64,
            Self::F64 => ScalarType::F64,
        }
    }

    pub const fn is_integer(self) -> bool {
        !matches!(self, Self::F64)
    }

    /// True if this type supports the given builtin method.
    /// All numeric types support `add`, `sub`, `mul`, `div`, `equals`,
    /// `to_str`. Only integers support `mod`.
    pub fn has_builtin_method(self, method: &str) -> bool {
        match method {
            "add" | "sub" | "mul" | "div" | "equals" | "compare" | "to_str" | "hash" => true,
            "mod" => self.is_integer(),
            "from_u8" => matches!(self, Self::U64),
            _ => false,
        }
    }
}
