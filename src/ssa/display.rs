use std::fmt;

use super::{Function, Module};
use crate::ssa::instruction::{BinaryOp, Inst, ScalarType, Terminator};

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
            write!(f, "{p}")?;
        }
        writeln!(f, "):")?;
        for (i, block) in self.blocks.iter().enumerate() {
            write!(f, "  b{i}")?;
            if !block.params.is_empty() {
                write!(f, "(")?;
                for (j, p) in block.params.iter().enumerate() {
                    if j > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{p}")?;
                }
                write!(f, ")")?;
            }
            writeln!(f, ":")?;
            for inst in &block.insts {
                writeln!(f, "    {inst}")?;
            }
            writeln!(f, "    {}", block.terminator)?;
        }
        Ok(())
    }
}

impl fmt::Display for ScalarType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::I8 => write!(f, "i8"),
            Self::U8 => write!(f, "u8"),
            Self::I64 => write!(f, "i64"),
            Self::U64 => write!(f, "u64"),
            Self::F64 => write!(f, "f64"),
            Self::Bool => write!(f, "bool"),
            Self::Ptr => write!(f, "ptr"),
        }
    }
}

impl fmt::Display for Inst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Const(d, ty, bits) => match ty {
                ScalarType::F64 => write!(f, "{d} = const {}_f64", f64::from_bits(*bits)),
                ScalarType::Bool => write!(f, "{d} = const {}", *bits != 0),
                ScalarType::Ptr => write!(f, "{d} = const 0x{bits:x}_ptr"),
                _ => write!(f, "{d} = const {bits}_{ty}"),
            },
            Self::BinOp(d, op, l, r) => write!(f, "{d} = {op} {l}, {r}"),
            Self::Call(d, name, args) => {
                write!(f, "{d} = call {name}(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{a}")?;
                }
                write!(f, ")")
            }
            Self::Alloc(d, size) => write!(f, "{d} = alloc {size}"),
            Self::Load(d, ty, ptr, off) => write!(f, "{d} = load {ty} {ptr}[{off}]"),
            Self::Store(ptr, off, val) => write!(f, "store {val} -> {ptr}[{off}]"),
            Self::RcInc(ptr) => write!(f, "rc_inc {ptr}"),
            Self::RcDec(ptr) => write!(f, "rc_dec {ptr}"),
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
