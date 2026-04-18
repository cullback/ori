use std::fmt;

use super::{Function, Module, StaticSlot};
use crate::ssa::instruction::{BinaryOp, Inst, ScalarType, Terminator, Value};
use std::collections::HashMap;

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.statics.is_empty() {
            writeln!(f, ".statics:")?;
            for (i, obj) in self.statics.iter().enumerate() {
                write!(f, "  @{i} = [")?;
                for (j, slot) in obj.slots.iter().enumerate() {
                    if j > 0 {
                        write!(f, ", ")?;
                    }
                    match slot {
                        StaticSlot::U8(b) => write!(f, "{b}_u8")?,
                        StaticSlot::U32(n) => write!(f, "{n}_u32")?,
                        StaticSlot::U64(n) => write!(f, "{n}_u64")?,
                        StaticSlot::I64(n) => write!(f, "{n}_i64")?,
                        StaticSlot::StaticPtr(id) => write!(f, "@{id}")?,
                    }
                }
                // Try to render U8 arrays as strings for readability.
                if obj.slots.iter().all(|s| matches!(s, StaticSlot::U8(_))) {
                    let bytes: Vec<u8> = obj
                        .slots
                        .iter()
                        .filter_map(|s| if let StaticSlot::U8(b) = s { Some(*b) } else { None })
                        .collect();
                    if let Ok(s) = std::str::from_utf8(&bytes) {
                        write!(f, "  ; \"{s}\"")?;
                    }
                }
                writeln!(f, "]")?;
            }
            writeln!(f)?;
        }
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

/// Format a constant literal for inline display.
fn fmt_const(ty: ScalarType, bits: u64) -> String {
    match ty {
        ScalarType::F64 => format!("{}_f64", f64::from_bits(bits)),
        ScalarType::Ptr => format!("0x{bits:x}_ptr"),
        _ => format!("{bits}_{ty}"),
    }
}

/// Display a value, inlining constants.
fn fmt_val(v: Value, consts: &HashMap<Value, (ScalarType, u64)>) -> String {
    if let Some(&(ty, bits)) = consts.get(&v) {
        fmt_const(ty, bits)
    } else {
        format!("{v}")
    }
}

/// Display a comma-separated arg list, inlining constants.
fn fmt_args(args: &[Value], consts: &HashMap<Value, (ScalarType, u64)>) -> String {
    args.iter()
        .map(|v| fmt_val(*v, consts))
        .collect::<Vec<_>>()
        .join(", ")
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Collect all constants for inline display.
        let consts = collect_consts(self);

        write!(f, "fn {}(", self.name)?;
        for (i, p) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{p}: {}", p.ty)?;
        }
        write!(f, ") -> {}:", self.return_type)?;
        writeln!(f)?;
        for (&bid, block) in &self.blocks {
            write!(f, "  {bid}")?;
            if !block.params.is_empty() {
                write!(f, "(")?;
                for (j, p) in block.params.iter().enumerate() {
                    if j > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{p}: {}", p.ty)?;
                }
                write!(f, ")")?;
            }
            writeln!(f, ":")?;
            for inst in &block.insts {
                // Skip Const instructions — they're shown inline at use sites.
                if matches!(inst, Inst::Const(..)) {
                    continue;
                }
                writeln!(f, "    {}", FmtInst(inst, &consts))?;
            }
            writeln!(f, "    {}", FmtTerm(&block.terminator, &consts))?;
        }
        Ok(())
    }
}

/// Collect all Const instructions in a function.
fn collect_consts(func: &Function) -> HashMap<Value, (ScalarType, u64)> {
    let mut consts = HashMap::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Const(dest, bits) = inst {
                consts.insert(*dest, (dest.ty, *bits));
            }
        }
    }
    consts
}

/// Display an instruction with constants inlined.
struct FmtInst<'a>(&'a Inst, &'a HashMap<Value, (ScalarType, u64)>);

impl fmt::Display for FmtInst<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let consts = self.1;
        match self.0 {
            Inst::Const(..) => Ok(()), // suppressed
            Inst::BinOp(d, op, l, r) => {
                let dt = d.ty;
                write!(f, "{d}: {dt} = {op} {}, {}", fmt_val(*l, consts), fmt_val(*r, consts))
            }
            Inst::Call(d, name, args) => {
                let dt = d.ty;
                write!(f, "{d}: {dt} = call {name}({})", fmt_args(args, consts))
            }
            Inst::Alloc(d, size) => {
                let dt = d.ty;
                write!(f, "{d}: {dt} = alloc {size}")
            }
            Inst::AllocDyn(d, size_val) => {
                let dt = d.ty;
                write!(f, "{d}: {dt} = alloc_dyn {}", fmt_val(*size_val, consts))
            }
            Inst::Load(d, ptr, off) => {
                let dt = d.ty;
                write!(f, "{d}: {dt} = load {}[{off}]", fmt_val(*ptr, consts))
            }
            Inst::Store(ptr, off, val) => {
                write!(f, "store {} -> {}[{off}]", fmt_val(*val, consts), fmt_val(*ptr, consts))
            }
            Inst::LoadDyn(d, ptr, idx) => {
                let dt = d.ty;
                write!(f, "{d}: {dt} = load_dyn {}[{}]", fmt_val(*ptr, consts), fmt_val(*idx, consts))
            }
            Inst::StoreDyn(ptr, idx, val) => {
                write!(f, "store_dyn {} -> {}[{}]",
                    fmt_val(*val, consts), fmt_val(*ptr, consts), fmt_val(*idx, consts))
            }
            Inst::RcInc(ptr) => write!(f, "rc_inc {}", fmt_val(*ptr, consts)),
            Inst::RcDec(ptr) => write!(f, "rc_dec {}", fmt_val(*ptr, consts)),
            Inst::Reset(d, ptr, _) => write!(f, "{d}: ptr = reset {}", fmt_val(*ptr, consts)),
            Inst::Reuse(d, tok, n) => write!(f, "{d}: ptr = reuse {}, {n}", fmt_val(*tok, consts)),
            Inst::ReuseDyn(d, tok, n) => write!(f, "{d}: ptr = reuse_dyn {}, {}", fmt_val(*tok, consts), fmt_val(*n, consts)),
            Inst::StaticRef(d, id) => write!(f, "{d}: ptr = static_ref @{id}"),
            Inst::Pack(d, fields) => {
                write!(f, "{d} = pack({})", fmt_args(fields, consts))
            }
            Inst::Extract(d, agg, idx) => {
                let dt = d.ty;
                write!(f, "{d}: {dt} = extract {}, {idx}", fmt_val(*agg, consts))
            }
            Inst::Insert(d, agg, idx, val) => {
                write!(f, "{d} = insert {}, {idx}, {}", fmt_val(*agg, consts), fmt_val(*val, consts))
            }
        }
    }
}

/// Display a terminator with constants inlined.
struct FmtTerm<'a>(&'a Terminator, &'a HashMap<Value, (ScalarType, u64)>);

impl fmt::Display for FmtTerm<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let consts = self.1;
        match self.0 {
            Terminator::Return(v) => write!(f, "ret {}", fmt_val(*v, consts)),
            Terminator::Jump(edge) => {
                write!(f, "jump {}", edge.target)?;
                if !edge.args.is_empty() {
                    write!(f, "({})", fmt_args(&edge.args, consts))?;
                }
                Ok(())
            }
            Terminator::Branch {
                cond,
                then_edge,
                else_edge,
            } => {
                write!(f, "branch {} ? {}", fmt_val(*cond, consts), then_edge.target)?;
                if !then_edge.args.is_empty() {
                    write!(f, "({})", fmt_args(&then_edge.args, consts))?;
                }
                write!(f, " : {}", else_edge.target)?;
                if !else_edge.args.is_empty() {
                    write!(f, "({})", fmt_args(&else_edge.args, consts))?;
                }
                Ok(())
            }
            Terminator::SwitchInt {
                scrutinee,
                arms,
                default,
            } => {
                write!(f, "switch {}", fmt_val(*scrutinee, consts))?;
                for (val, edge) in arms {
                    write!(f, "\n      {val} -> {}", edge.target)?;
                    if !edge.args.is_empty() {
                        write!(f, "({})", fmt_args(&edge.args, consts))?;
                    }
                }
                if let Some(edge) = default {
                    write!(f, "\n      _ -> {}", edge.target)?;
                    if !edge.args.is_empty() {
                        write!(f, "({})", fmt_args(&edge.args, consts))?;
                    }
                }
                Ok(())
            }
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
            Self::Ptr => write!(f, "ptr"),
            Self::Agg(n) => write!(f, "agg{n}"),
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
            Self::And => write!(f, "and"),
            Self::Or => write!(f, "or"),
            Self::Xor => write!(f, "xor"),
            Self::Shl => write!(f, "shl"),
            Self::Shr => write!(f, "shr"),
            Self::Eq => write!(f, "eq"),
            Self::Neq => write!(f, "neq"),
            Self::Lt => write!(f, "lt"),
            Self::Le => write!(f, "le"),
            Self::Gt => write!(f, "gt"),
            Self::Ge => write!(f, "ge"),
            Self::Max => write!(f, "max"),
        }
    }
}

// BlockId and Value Display impls live in instruction.rs.
