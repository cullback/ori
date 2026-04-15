//! Pretty-printer for the raw (post-parse) AST.
//!
//! Produces a deterministic, indented format for snapshot testing and
//! debugging. Style mirrors `src/ssa/display.rs`: line-oriented, keyword-led,
//! 2-space indent. Leaf nodes render inline (`IntLit 42`, `Name foo`);
//! compound nodes render as `label:` followed by indented children.
//!
//! Spans are intentionally omitted from the output because they would make
//! snapshots churn on whitespace changes in source files.

use std::fmt;

use super::raw::{
    BinOp, ConstraintDecl, Decl, Expr, ExprKind, Import, MatchArm, Module, Pattern, Stmt, TagDecl,
    TypeDeclKind, TypeExpr,
};

// ---- Module ----

impl fmt::Display for Module<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "module:")?;
        if !self.exports.is_empty() {
            write_indent(f, 1)?;
            write!(f, "exports:")?;
            for e in &self.exports {
                write!(f, " {e}")?;
            }
            writeln!(f)?;
        }
        for imp in &self.imports {
            write_import(f, imp, 1)?;
        }
        for decl in &self.decls {
            write_decl(f, decl, 1)?;
        }
        Ok(())
    }
}

// ---- Indentation helpers ----

fn write_indent(f: &mut fmt::Formatter<'_>, level: usize) -> fmt::Result {
    for _ in 0..level {
        write!(f, "  ")?;
    }
    Ok(())
}

fn write_line(
    f: &mut fmt::Formatter<'_>,
    level: usize,
    content: fmt::Arguments<'_>,
) -> fmt::Result {
    write_indent(f, level)?;
    f.write_fmt(content)?;
    writeln!(f)
}

// ---- Imports ----

fn write_import(f: &mut fmt::Formatter<'_>, imp: &Import<'_>, level: usize) -> fmt::Result {
    write_indent(f, level)?;
    write!(f, "import {}", imp.module)?;
    if !imp.exposing.is_empty() {
        write!(f, " exposing (")?;
        for (i, name) in imp.exposing.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{name}")?;
        }
        write!(f, ")")?;
    }
    writeln!(f)
}

// ---- Declarations ----

fn write_decl(f: &mut fmt::Formatter<'_>, decl: &Decl<'_>, level: usize) -> fmt::Result {
    match decl {
        Decl::TypeAnno {
            name,
            type_params,
            ty,
            where_clause,
            methods,
            kind,
            ..
        } => {
            write_indent(f, level)?;
            write!(f, "{} {}", type_decl_kind(*kind), name)?;
            if !type_params.is_empty() {
                write!(f, "(")?;
                for (i, p) in type_params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{p}")?;
                }
                write!(f, ")")?;
            }
            writeln!(f, ":")?;
            write_type_expr(f, ty, level + 1)?;
            if !where_clause.is_empty() {
                write_line(f, level + 1, format_args!("where:"))?;
                for c in where_clause {
                    write_constraint(f, c, level + 2)?;
                }
            }
            if !methods.is_empty() {
                write_line(f, level + 1, format_args!("methods:"))?;
                for m in methods {
                    write_decl(f, m, level + 2)?;
                }
            }
            Ok(())
        }
        Decl::FuncDef {
            name, params, body, ..
        } => {
            write_indent(f, level)?;
            write!(f, "fn {name}(")?;
            for (i, p) in params.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{p}")?;
            }
            writeln!(f, "):")?;
            write_expr(f, body, level + 1)
        }
    }
}

const fn type_decl_kind(kind: TypeDeclKind) -> &'static str {
    match kind {
        TypeDeclKind::Alias => "type-alias",
        TypeDeclKind::Transparent => "type-transparent",
        TypeDeclKind::Opaque => "type-opaque",
    }
}

fn write_constraint(
    f: &mut fmt::Formatter<'_>,
    c: &ConstraintDecl<'_>,
    level: usize,
) -> fmt::Result {
    write_indent(f, level)?;
    write!(f, "{}.{}", c.type_var, c.method)?;
    if let Some(ty) = &c.method_type {
        writeln!(f, ":")?;
        write_type_expr(f, ty, level + 1)
    } else {
        writeln!(f)
    }
}

// ---- Type expressions ----

fn write_type_expr(f: &mut fmt::Formatter<'_>, ty: &TypeExpr<'_>, level: usize) -> fmt::Result {
    match ty {
        TypeExpr::Named(name) => write_line(f, level, format_args!("Named {name}")),
        TypeExpr::App(name, args) => {
            write_line(f, level, format_args!("App {name}:"))?;
            for a in args {
                write_type_expr(f, a, level + 1)?;
            }
            Ok(())
        }
        TypeExpr::TagUnion(tags, open) => {
            let label = if *open { "TagUnion (open):" } else { "TagUnion:" };
            write_line(f, level, format_args!("{label}"))?;
            for t in tags {
                write_tag_decl(f, t, level + 1)?;
            }
            Ok(())
        }
        TypeExpr::Arrow(params, ret) => {
            write_line(f, level, format_args!("Arrow:"))?;
            write_line(f, level + 1, format_args!("params:"))?;
            for p in params {
                write_type_expr(f, p, level + 2)?;
            }
            write_line(f, level + 1, format_args!("ret:"))?;
            write_type_expr(f, ret, level + 2)
        }
        TypeExpr::Record(fields) => {
            write_line(f, level, format_args!("Record:"))?;
            for (name, ty) in fields {
                write_line(f, level + 1, format_args!("{name}:"))?;
                write_type_expr(f, ty, level + 2)?;
            }
            Ok(())
        }
        TypeExpr::Tuple(elems) => {
            write_line(f, level, format_args!("Tuple:"))?;
            for e in elems {
                write_type_expr(f, e, level + 1)?;
            }
            Ok(())
        }
    }
}

fn write_tag_decl(f: &mut fmt::Formatter<'_>, tag: &TagDecl<'_>, level: usize) -> fmt::Result {
    if tag.fields.is_empty() {
        write_line(f, level, format_args!("tag {}", tag.name))
    } else {
        write_line(f, level, format_args!("tag {}:", tag.name))?;
        for field in &tag.fields {
            write_type_expr(f, field, level + 1)?;
        }
        Ok(())
    }
}

// ---- Expressions ----

fn write_expr(f: &mut fmt::Formatter<'_>, expr: &Expr<'_>, level: usize) -> fmt::Result {
    match &expr.kind {
        ExprKind::IntLit(n) => write_line(f, level, format_args!("IntLit {n}")),
        ExprKind::FloatLit(n) => write_line(f, level, format_args!("FloatLit {n}")),
        ExprKind::StrLit(bytes) => {
            let s = String::from_utf8_lossy(bytes);
            write_line(f, level, format_args!("StrLit {s:?}"))
        }
        ExprKind::Name(name) => write_line(f, level, format_args!("Name {name}")),
        ExprKind::BinOp { op, lhs, rhs } => {
            write_line(f, level, format_args!("BinOp {}:", bin_op(*op)))?;
            write_expr(f, lhs, level + 1)?;
            write_expr(f, rhs, level + 1)
        }
        ExprKind::Call { func, args } => write_named_args(f, level, "Call", func, args),
        ExprKind::QualifiedCall { segments, args } => {
            write_named_args(f, level, "QualifiedCall", &segments.join("."), args)
        }
        ExprKind::Block(stmts, result) => write_block_expr(f, level, stmts, result),
        ExprKind::If {
            expr: scrutinee,
            arms,
            else_body,
        } => write_if_expr(f, level, scrutinee, arms, else_body.as_deref()),
        ExprKind::Fold {
            expr: scrutinee,
            arms,
        } => write_fold_expr(f, level, scrutinee, arms),
        ExprKind::Lambda { params, body } => write_lambda_expr(f, level, params, body),
        ExprKind::Record { fields } => write_record_expr(f, level, fields),
        ExprKind::FieldAccess { record, field } => {
            write_line(f, level, format_args!("FieldAccess .{field}:"))?;
            write_expr(f, record, level + 1)
        }
        ExprKind::Tuple(elems) => write_seq_expr(f, level, "Tuple", "()", elems),
        ExprKind::ListLit(elems) => write_seq_expr(f, level, "ListLit", "[]", elems),
        ExprKind::MethodCall {
            receiver,
            method,
            args,
        } => write_method_call(f, level, receiver, method, args),
        ExprKind::Is {
            expr: inner,
            pattern,
        } => write_is_expr(f, level, inner, pattern),
        ExprKind::RecordUpdate { base, updates } => {
            write_line(f, level, format_args!("RecordUpdate:"))?;
            write_expr(f, base, level + 1)?;
            for (name, val) in updates {
                write_line(f, level + 1, format_args!("& {name}:"))?;
                write_expr(f, val, level + 2)?;
            }
            Ok(())
        }
    }
}

/// Helper for nodes like `Call name` / `QualifiedCall path` that carry a
/// label, a textual name, and a flat argument list.
fn write_named_args(
    f: &mut fmt::Formatter<'_>,
    level: usize,
    label: &str,
    name: &str,
    args: &[Expr<'_>],
) -> fmt::Result {
    if args.is_empty() {
        write_line(f, level, format_args!("{label} {name}"))
    } else {
        write_line(f, level, format_args!("{label} {name}:"))?;
        for a in args {
            write_expr(f, a, level + 1)?;
        }
        Ok(())
    }
}

/// Helper for flat sequence exprs (`Tuple`, `ListLit`) with an empty-case marker.
fn write_seq_expr(
    f: &mut fmt::Formatter<'_>,
    level: usize,
    label: &str,
    empty: &str,
    elems: &[Expr<'_>],
) -> fmt::Result {
    if elems.is_empty() {
        write_line(f, level, format_args!("{label} {empty}"))
    } else {
        write_line(f, level, format_args!("{label}:"))?;
        for e in elems {
            write_expr(f, e, level + 1)?;
        }
        Ok(())
    }
}

fn write_block_expr(
    f: &mut fmt::Formatter<'_>,
    level: usize,
    stmts: &[Stmt<'_>],
    result: &Expr<'_>,
) -> fmt::Result {
    write_line(f, level, format_args!("Block:"))?;
    for s in stmts {
        write_stmt(f, s, level + 1)?;
    }
    write_line(f, level + 1, format_args!("result:"))?;
    write_expr(f, result, level + 2)
}

fn write_if_expr(
    f: &mut fmt::Formatter<'_>,
    level: usize,
    scrutinee: &Expr<'_>,
    arms: &[MatchArm<'_>],
    else_body: Option<&Expr<'_>>,
) -> fmt::Result {
    write_line(f, level, format_args!("If:"))?;
    write_line(f, level + 1, format_args!("scrutinee:"))?;
    write_expr(f, scrutinee, level + 2)?;
    for arm in arms {
        write_match_arm(f, arm, level + 1)?;
    }
    if let Some(eb) = else_body {
        write_line(f, level + 1, format_args!("else:"))?;
        write_expr(f, eb, level + 2)?;
    }
    Ok(())
}

fn write_fold_expr(
    f: &mut fmt::Formatter<'_>,
    level: usize,
    scrutinee: &Expr<'_>,
    arms: &[MatchArm<'_>],
) -> fmt::Result {
    write_line(f, level, format_args!("Fold:"))?;
    write_line(f, level + 1, format_args!("scrutinee:"))?;
    write_expr(f, scrutinee, level + 2)?;
    for arm in arms {
        write_match_arm(f, arm, level + 1)?;
    }
    Ok(())
}

fn write_lambda_expr(
    f: &mut fmt::Formatter<'_>,
    level: usize,
    params: &[&str],
    body: &Expr<'_>,
) -> fmt::Result {
    write_indent(f, level)?;
    write!(f, "Lambda(")?;
    for (i, p) in params.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{p}")?;
    }
    writeln!(f, "):")?;
    write_expr(f, body, level + 1)
}

fn write_record_expr(
    f: &mut fmt::Formatter<'_>,
    level: usize,
    fields: &[(&str, Expr<'_>)],
) -> fmt::Result {
    if fields.is_empty() {
        write_line(f, level, format_args!("Record {{}}"))
    } else {
        write_line(f, level, format_args!("Record:"))?;
        for (name, val) in fields {
            write_line(f, level + 1, format_args!("{name}:"))?;
            write_expr(f, val, level + 2)?;
        }
        Ok(())
    }
}

fn write_method_call(
    f: &mut fmt::Formatter<'_>,
    level: usize,
    receiver: &Expr<'_>,
    method: &str,
    args: &[Expr<'_>],
) -> fmt::Result {
    write_line(f, level, format_args!("MethodCall .{method}:"))?;
    write_line(f, level + 1, format_args!("receiver:"))?;
    write_expr(f, receiver, level + 2)?;
    if !args.is_empty() {
        write_line(f, level + 1, format_args!("args:"))?;
        for a in args {
            write_expr(f, a, level + 2)?;
        }
    }
    Ok(())
}

fn write_is_expr(
    f: &mut fmt::Formatter<'_>,
    level: usize,
    inner: &Expr<'_>,
    pattern: &Pattern<'_>,
) -> fmt::Result {
    write_line(f, level, format_args!("Is:"))?;
    write_line(f, level + 1, format_args!("expr:"))?;
    write_expr(f, inner, level + 2)?;
    write_line(f, level + 1, format_args!("pattern:"))?;
    write_pattern(f, pattern, level + 2)
}

const fn bin_op(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "Add",
        BinOp::Sub => "Sub",
        BinOp::Mul => "Mul",
        BinOp::Div => "Div",
        BinOp::Rem => "Rem",
        BinOp::BitOr => "BitOr",
        BinOp::BitXor => "BitXor",
        BinOp::Eq => "Eq",
        BinOp::Neq => "Neq",
        BinOp::Lt => "Lt",
        BinOp::Gt => "Gt",
        BinOp::Le => "Le",
        BinOp::Ge => "Ge",
        BinOp::And => "And",
        BinOp::Or => "Or",
    }
}

// ---- Match arms ----

fn write_match_arm(f: &mut fmt::Formatter<'_>, arm: &MatchArm<'_>, level: usize) -> fmt::Result {
    let header = if arm.is_return {
        "arm (return):"
    } else {
        "arm:"
    };
    write_line(f, level, format_args!("{header}"))?;
    write_line(f, level + 1, format_args!("pattern:"))?;
    write_pattern(f, &arm.pattern, level + 2)?;
    if !arm.guards.is_empty() {
        write_line(f, level + 1, format_args!("guards:"))?;
        for g in &arm.guards {
            write_expr(f, g, level + 2)?;
        }
    }
    write_line(f, level + 1, format_args!("body:"))?;
    write_expr(f, &arm.body, level + 2)
}

// ---- Patterns ----

fn write_pattern(f: &mut fmt::Formatter<'_>, pat: &Pattern<'_>, level: usize) -> fmt::Result {
    match pat {
        Pattern::Wildcard => write_line(f, level, format_args!("Wildcard")),
        Pattern::Binding(name) => write_line(f, level, format_args!("Bind {name}")),
        Pattern::Constructor { name, fields } => {
            if fields.is_empty() {
                write_line(f, level, format_args!("Con {name}"))
            } else {
                write_line(f, level, format_args!("Con {name}:"))?;
                for field in fields {
                    write_pattern(f, field, level + 1)?;
                }
                Ok(())
            }
        }
        Pattern::Record { fields, .. } => {
            if fields.is_empty() {
                write_line(f, level, format_args!("PRecord {{}}"))
            } else {
                write_line(f, level, format_args!("PRecord:"))?;
                for (name, sub) in fields {
                    write_line(f, level + 1, format_args!("{name}:"))?;
                    write_pattern(f, sub, level + 2)?;
                }
                Ok(())
            }
        }
        Pattern::Tuple(elems) => {
            if elems.is_empty() {
                write_line(f, level, format_args!("PTuple ()"))
            } else {
                write_line(f, level, format_args!("PTuple:"))?;
                for e in elems {
                    write_pattern(f, e, level + 1)?;
                }
                Ok(())
            }
        }
        Pattern::IntLit(n) => write_line(f, level, format_args!("{n}")),
        Pattern::StrLit(b) => {
            let s = String::from_utf8_lossy(b);
            write_line(f, level, format_args!("\"{s}\""))
        }
        Pattern::List(elems) => {
            if elems.is_empty() {
                write_line(f, level, format_args!("PList []"))
            } else {
                write_line(f, level, format_args!("PList:"))?;
                for elem in elems {
                    match elem {
                        crate::syntax::raw::ListPatternElem::Pattern(p) => {
                            write_pattern(f, p, level + 1)?;
                        }
                        crate::syntax::raw::ListPatternElem::Spread(Some(name)) => {
                            write_line(f, level + 1, format_args!("..{name}"))?;
                        }
                        crate::syntax::raw::ListPatternElem::Spread(None) => {
                            write_line(f, level + 1, format_args!(".."))?;
                        }
                    }
                }
                Ok(())
            }
        }
    }
}

// ---- Statements ----

fn write_stmt(f: &mut fmt::Formatter<'_>, stmt: &Stmt<'_>, level: usize) -> fmt::Result {
    match stmt {
        Stmt::Let { name, val } => {
            write_line(f, level, format_args!("Let {name}:"))?;
            write_expr(f, val, level + 1)
        }
        Stmt::TypeHint { name, ty } => {
            write_line(f, level, format_args!("TypeHint {name}:"))?;
            write_type_expr(f, ty, level + 1)
        }
        Stmt::Destructure { pattern, val } => {
            write_line(f, level, format_args!("Destructure:"))?;
            write_line(f, level + 1, format_args!("pattern:"))?;
            write_pattern(f, pattern, level + 2)?;
            write_line(f, level + 1, format_args!("val:"))?;
            write_expr(f, val, level + 2)
        }
        Stmt::Guard {
            condition,
            return_val,
        } => {
            write_line(f, level, format_args!("Guard:"))?;
            write_line(f, level + 1, format_args!("cond:"))?;
            write_expr(f, condition, level + 2)?;
            write_line(f, level + 1, format_args!("return:"))?;
            write_expr(f, return_val, level + 2)
        }
    }
}
