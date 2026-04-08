use std::fmt;

use super::{Block, Function, Module};
use crate::ssa::instruction::{BinaryOp, Inst, Terminator};

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

impl fmt::Display for Inst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Const(d, n) => write!(f, "{d} = const {n}_i64"),
            Self::ConstU64(d, n) => write!(f, "{d} = const {n}_u64"),
            Self::ConstF64(d, n) => write!(f, "{d} = const {n}_f64"),
            Self::ConstU8(d, n) => write!(f, "{d} = const {n}_u8"),
            Self::ConstI8(d, n) => write!(f, "{d} = const {n}_i8"),
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
            Self::Construct(d, tag, fields) => {
                write!(f, "{d} = construct {tag}")?;
                if !fields.is_empty() {
                    write!(f, "(")?;
                    for (i, v) in fields.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{v}")?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            Self::RecordNew(d, fields) => {
                write!(f, "{d} = record {{")?;
                for (i, (name, v)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    write!(f, " {name}: {v}")?;
                }
                write!(f, " }}")
            }
            Self::FieldGet(d, rec, name) => write!(f, "{d} = {rec}.{name}"),
            Self::ListNew(d, elems) => {
                write!(f, "{d} = list[")?;
                for (i, v) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v}")?;
                }
                write!(f, "]")
            }
            Self::ListGet(d, list, idx) => write!(f, "{d} = {list}[{idx}]"),
            Self::ListSet(d, list, idx, val) => write!(f, "{d} = {list}[{idx}] = {val}"),
            Self::ListAppend(d, list, val) => write!(f, "{d} = {list}.append({val})"),
            Self::ListLen(d, list) => write!(f, "{d} = {list}.len()"),
            Self::NumToStr(d, num) => write!(f, "{d} = {num}.to_str()"),
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

impl fmt::Display for Block {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Used via Function::Display
        write!(f, "{}", self.terminator)
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
            Self::Switch { scrutinee, arms } => {
                writeln!(f, "switch {scrutinee}")?;
                for (tag, block) in arms {
                    write!(f, "      : {tag} -> {block}")?;
                }
                Ok(())
            }
        }
    }
}
