use std::fmt;

use super::{Function, Module};
use crate::ssa::instruction::{BinaryOp, Inst, ScalarType, Terminator, Value};
use std::collections::HashMap;

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut names: Vec<&String> = self.functions.keys().collect();
        names.sort();
        for name in names {
            let func = &self.functions[name];
            write!(f, "{func}")?;
            writeln!(f)?;
        }
        Ok(())
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fn {}(", self.name)?;
        for (i, p) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            let ty = self.value_types.get(p).copied().unwrap_or(ScalarType::Ptr);
            write!(f, "{p}: {ty}")?;
        }
        write!(f, ") -> {}:", self.return_type)?;
        writeln!(f)?;
        for (i, block) in self.blocks.iter().enumerate() {
            write!(f, "  b{i}")?;
            if !block.params.is_empty() {
                write!(f, "(")?;
                for (j, p) in block.params.iter().enumerate() {
                    if j > 0 {
                        write!(f, ", ")?;
                    }
                    let ty = self.value_types.get(p).copied().unwrap_or(ScalarType::Ptr);
                    write!(f, "{p}: {ty}")?;
                }
                write!(f, ")")?;
            }
            writeln!(f, ":")?;
            for inst in &block.insts {
                writeln!(f, "    {}", InstDisplay(inst, &self.value_types))?;
            }
            writeln!(f, "    {}", block.terminator)?;
        }
        Ok(())
    }
}

/// Helper to display an instruction with type annotations from value_types.
struct InstDisplay<'a>(&'a Inst, &'a HashMap<Value, ScalarType>);

impl fmt::Display for InstDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let types = self.1;
        match self.0 {
            Inst::Const(d, ty, bits) => {
                let dt = types.get(d).copied().unwrap_or(*ty);
                match ty {
                    ScalarType::F64 => {
                        write!(f, "{d}: {dt} = const {}_f64", f64::from_bits(*bits))
                    }
                    ScalarType::Bool => write!(f, "{d}: {dt} = const {}", *bits != 0),
                    ScalarType::Ptr => write!(f, "{d}: {dt} = const 0x{bits:x}_ptr"),
                    _ => write!(f, "{d}: {dt} = const {bits}_{ty}"),
                }
            }
            Inst::BinOp(d, op, l, r) => {
                let dt = types.get(d).copied().unwrap_or(ScalarType::Ptr);
                write!(f, "{d}: {dt} = {op} {l}, {r}")
            }
            Inst::Call(d, name, args) => {
                let dt = types.get(d).copied().unwrap_or(ScalarType::Ptr);
                write!(f, "{d}: {dt} = call {name}(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{a}")?;
                }
                write!(f, ")")
            }
            Inst::Alloc(d, size) => {
                let dt = types.get(d).copied().unwrap_or(ScalarType::Ptr);
                write!(f, "{d}: {dt} = alloc {size}")
            }
            Inst::Load(d, ptr, off) => {
                let dt = types.get(d).copied().unwrap_or(ScalarType::Ptr);
                write!(f, "{d}: {dt} = load {ptr}[{off}]")
            }
            Inst::Store(ptr, off, val) => write!(f, "store {val} -> {ptr}[{off}]"),
            Inst::LoadDyn(d, ptr, idx) => {
                let dt = types.get(d).copied().unwrap_or(ScalarType::Ptr);
                write!(f, "{d}: {dt} = load_dyn {ptr}[{idx}]")
            }
            Inst::StoreDyn(ptr, idx, val) => write!(f, "store_dyn {val} -> {ptr}[{idx}]"),
            Inst::RcInc(ptr) => write!(f, "rc_inc {ptr}"),
            Inst::RcDec(ptr) => write!(f, "rc_dec {ptr}"),
        }
    }
}

impl fmt::Display for ScalarType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::I8 => write!(f, "i8"),
            Self::U8 => write!(f, "u8"),
            Self::I16 => write!(f, "i16"),
            Self::U16 => write!(f, "u16"),
            Self::I32 => write!(f, "i32"),
            Self::U32 => write!(f, "u32"),
            Self::I64 => write!(f, "i64"),
            Self::U64 => write!(f, "u64"),
            Self::F64 => write!(f, "f64"),
            Self::Bool => write!(f, "bool"),
            Self::Ptr => write!(f, "ptr"),
        }
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Add => write!(f, "add"),
            Self::Sub => write!(f, "sub"),
            Self::Mul => write!(f, "mul"),
            Self::Div => write!(f, "div"),
            Self::Rem => write!(f, "rem"),
            Self::Eq => write!(f, "eq"),
            Self::Neq => write!(f, "neq"),
            Self::Max => write!(f, "max"),
        }
    }
}

impl fmt::Display for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::None => write!(f, "<incomplete>"),
            Self::Return(v) => write!(f, "ret {v}"),
            Self::Jump(target, args) => {
                write!(f, "jump {target}")?;
                if !args.is_empty() {
                    write!(f, "(")?;
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{a}")?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            Self::Branch {
                cond,
                then_block,
                then_args,
                else_block,
                else_args,
            } => {
                write!(f, "branch {cond} ? {then_block}")?;
                if !then_args.is_empty() {
                    write!(f, "(")?;
                    for (i, a) in then_args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{a}")?;
                    }
                    write!(f, ")")?;
                }
                write!(f, " : {else_block}")?;
                if !else_args.is_empty() {
                    write!(f, "(")?;
                    for (i, a) in else_args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{a}")?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            Self::SwitchInt {
                scrutinee,
                arms,
                default,
            } => {
                write!(f, "switch {scrutinee}")?;
                for (val, block, args) in arms {
                    write!(f, "\n      {val} -> {block}")?;
                    if !args.is_empty() {
                        write!(f, "(")?;
                        for (i, a) in args.iter().enumerate() {
                            if i > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{a}")?;
                        }
                        write!(f, ")")?;
                    }
                }
                if let Some((block, args)) = default {
                    write!(f, "\n      _ -> {block}")?;
                    if !args.is_empty() {
                        write!(f, "(")?;
                        for (i, a) in args.iter().enumerate() {
                            if i > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{a}")?;
                        }
                        write!(f, ")")?;
                    }
                }
                Ok(())
            }
        }
    }
}
