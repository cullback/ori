//! Pretty-printer for Core IR.
//!
//! Output is structural rather than source-like — the goal is to
//! make tests debuggable, not pretty Ori code. Local bindings
//! render as `%n`, callables as `@n`, type IDs as `T(n)`, declared
//! tags as `D(n)`, closure tags as `λn`.
//!
//! Use via `Display`:
//!
//! ```rust,no_run
//! # use core_ir::Builder;
//! let b = Builder::new();
//! let prog = b.int(42);
//! println!("{prog}");
//! ```

use std::fmt::{self, Display, Formatter};

use crate::expr::{Expr, FoldKind, FoldShape, MatchArm};
use crate::literal::{Literal, StrLit};
use crate::pattern::{Binder, Pattern};
use crate::sym::{ClosureTagId, DeclTagId, FnId, LocalId, TagId, TypeId};
use crate::ty::{CoreType, Scalar};

const INDENT: &str = "  ";

impl Display for LocalId {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "%{}", self.0)
    }
}

impl Display for FnId {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "@{}", self.0)
    }
}

impl Display for DeclTagId {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "D{}", self.0)
    }
}

impl Display for ClosureTagId {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "λ{}", self.0)
    }
}

impl Display for TypeId {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "T{}", self.0)
    }
}

impl Display for TagId {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Declared(d) => write!(f, "{d}"),
            Self::Closure(c) => write!(f, "{c}"),
        }
    }
}

impl Display for Scalar {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Bool => "Bool",
            Self::I8 => "I8",
            Self::I16 => "I16",
            Self::I32 => "I32",
            Self::I64 => "I64",
            Self::U8 => "U8",
            Self::U16 => "U16",
            Self::U32 => "U32",
            Self::U64 => "U64",
            Self::F32 => "F32",
            Self::F64 => "F64",
        };
        f.write_str(s)
    }
}

impl Display for CoreType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Prim(s) => write!(f, "{s}"),
            Self::Adt(head, args) => {
                write!(f, "{head}")?;
                if !args.is_empty() {
                    f.write_str("(")?;
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            f.write_str(", ")?;
                        }
                        write!(f, "{a}")?;
                    }
                    f.write_str(")")?;
                }
                Ok(())
            }
        }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(n) => write!(f, "{n}"),
            Self::Float(x) => write!(f, "{x}"),
        }
    }
}

impl Display for StrLit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = String::from_utf8_lossy(&self.0);
        write!(f, "{s:?}")
    }
}

impl Display for FoldKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Total => "Total",
            Self::EarlyExit => "EarlyExit",
        })
    }
}

impl Display for FoldShape {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Map => "Map",
            Self::Filter => "Filter",
            Self::Scan => "Scan",
            Self::Zip => "Zip",
            Self::Take => "Take",
            Self::Drop => "Drop",
        })
    }
}

impl Display for Binder {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Sym(s) => write!(f, "{s}"),
            Self::Wildcard => f.write_str("_"),
        }
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Wildcard => f.write_str("_"),
            Self::Binding(s) => write!(f, "{s}"),
            Self::Constructor { tag, binders } => {
                write!(f, "{tag}")?;
                if !binders.is_empty() {
                    f.write_str("(")?;
                    for (i, b) in binders.iter().enumerate() {
                        if i > 0 {
                            f.write_str(", ")?;
                        }
                        write!(f, "{b}")?;
                    }
                    f.write_str(")")?;
                }
                Ok(())
            }
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write_expr(f, self, 0)
    }
}

fn write_expr(f: &mut Formatter<'_>, expr: &Expr, depth: usize) -> fmt::Result {
    let pad = INDENT.repeat(depth);
    match expr {
        Expr::Var { sym, ty } => write!(f, "{sym}:{ty}"),
        Expr::Lit { value, ty } => write!(f, "{value}:{ty}"),
        Expr::Crash { msg, ty } => write!(f, "Crash({msg}):{ty}"),
        Expr::App { target, args, ty } => {
            write!(f, "{target}")?;
            f.write_str("(")?;
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    f.write_str(", ")?;
                }
                write_expr(f, a, depth)?;
            }
            write!(f, "):{ty}")
        }
        Expr::Con { tag, args, ty } => {
            write!(f, "{tag}")?;
            if !args.is_empty() {
                f.write_str("(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write_expr(f, a, depth)?;
                }
                f.write_str(")")?;
            }
            write!(f, ":{ty}")
        }
        Expr::Let { binder, value, body, ty } => {
            writeln!(f, "let {binder} =")?;
            write!(f, "{pad}{INDENT}")?;
            write_expr(f, value, depth + 1)?;
            writeln!(f, " in  // :{ty}")?;
            write!(f, "{pad}{INDENT}")?;
            write_expr(f, body, depth + 1)
        }
        Expr::Match { scrutinee, arms, ty } => {
            f.write_str("match ")?;
            write_expr(f, scrutinee, depth)?;
            writeln!(f, " : {ty} of")?;
            for (i, arm) in arms.iter().enumerate() {
                if i > 0 {
                    writeln!(f)?;
                }
                write!(f, "{pad}{INDENT}| ")?;
                write_arm(f, arm, depth + 1)?;
            }
            Ok(())
        }
        Expr::Fold { kind, fold_fn, target, init, captures, shape, ty } => {
            write!(f, "Fold[{kind}")?;
            if let Some(s) = shape {
                write!(f, ", {s}")?;
            }
            writeln!(f, "] {fold_fn} : {ty}")?;
            write!(f, "{pad}{INDENT}target = ")?;
            write_expr(f, target, depth + 1)?;
            f.write_str("\n")?;
            write!(f, "{pad}{INDENT}init = ")?;
            write_list(f, init, depth + 1)?;
            f.write_str("\n")?;
            write!(f, "{pad}{INDENT}captures = ")?;
            write_list(f, captures, depth + 1)
        }
        Expr::Gen { bound, step_fn, init, captures, elem_ty, ty } => {
            writeln!(f, "Gen {step_fn} : {ty} (elem={elem_ty})")?;
            write!(f, "{pad}{INDENT}bound = ")?;
            write_expr(f, bound, depth + 1)?;
            f.write_str("\n")?;
            write!(f, "{pad}{INDENT}init = ")?;
            write_list(f, init, depth + 1)?;
            f.write_str("\n")?;
            write!(f, "{pad}{INDENT}captures = ")?;
            write_list(f, captures, depth + 1)
        }
        Expr::BufLit { elements, elem_ty, ty } => {
            write!(f, "[")?;
            for (i, e) in elements.iter().enumerate() {
                if i > 0 {
                    f.write_str(", ")?;
                }
                write_expr(f, e, depth)?;
            }
            write!(f, "]:{ty}({elem_ty})")
        }
        Expr::BufLoad { buf, idx, ty } => {
            f.write_str("BufLoad(")?;
            write_expr(f, buf, depth)?;
            f.write_str(", ")?;
            write_expr(f, idx, depth)?;
            write!(f, "):{ty}")
        }
        Expr::BufLoadUnchecked { buf, idx, ty } => {
            f.write_str("BufLoadUnchecked(")?;
            write_expr(f, buf, depth)?;
            f.write_str(", ")?;
            write_expr(f, idx, depth)?;
            write!(f, "):{ty}")
        }
        Expr::BufAppend { buf, val, ty } => {
            f.write_str("BufAppend(")?;
            write_expr(f, buf, depth)?;
            f.write_str(", ")?;
            write_expr(f, val, depth)?;
            write!(f, "):{ty}")
        }
        Expr::BufSet { buf, idx, val, ty } => {
            f.write_str("BufSet(")?;
            write_expr(f, buf, depth)?;
            f.write_str(", ")?;
            write_expr(f, idx, depth)?;
            f.write_str(", ")?;
            write_expr(f, val, depth)?;
            write!(f, "):{ty}")
        }
    }
}

fn write_list(f: &mut Formatter<'_>, items: &[Expr], depth: usize) -> fmt::Result {
    if items.is_empty() {
        return f.write_str("[]");
    }
    f.write_str("[")?;
    for (i, e) in items.iter().enumerate() {
        if i > 0 {
            f.write_str(", ")?;
        }
        write_expr(f, e, depth)?;
    }
    f.write_str("]")
}

fn write_arm(f: &mut Formatter<'_>, arm: &MatchArm, depth: usize) -> fmt::Result {
    write!(f, "{}", arm.pattern)?;
    for g in &arm.guards {
        f.write_str(" and ")?;
        write_expr(f, g, depth)?;
    }
    f.write_str(if arm.is_return { " return " } else { " -> " })?;
    write_expr(f, &arm.body, depth)
}
