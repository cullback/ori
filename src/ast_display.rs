//! Pretty-printer for the elaborated AST (`ast::Module`).
//!
//! Threads a `SymbolTable` through every writer so that `SymbolId`
//! fields render with their source names. Use [`render`] to produce a
//! `String` for a module; internal writers take a `Printer` that
//! bundles the formatter and the symbol table.
//!
//! Style mirrors `src/ssa/display.rs`: line-oriented, keyword-led,
//! 2-space indent. Leaf nodes render inline (`IntLit 42`, `Name foo`);
//! compound nodes render as `label:` followed by indented children.
//! Spans are omitted.

use std::fmt::{self, Write};

use crate::ast::{
    BinOp, ConstraintDecl, Decl, Expr, ExprKind, Import, MatchArm, Module, Pattern, Stmt, TagDecl,
    TypeDeclKind, TypeExpr,
};
use crate::symbol::{FieldInterner, FieldSym, SymbolTable};
use crate::types::engine::Type;

/// Render a full `Module` as a `String`. Every `SymbolId` is displayed
/// via the `SymbolTable`'s source name; every `FieldSym` via the
/// `FieldInterner`'s source name.
#[allow(dead_code, reason = "used by ast_snapshot tests")]
pub fn render(module: &Module<'_>, symbols: &SymbolTable, fields: &FieldInterner) -> String {
    let mut out = String::new();
    let mut p = Printer {
        buf: &mut out,
        symbols,
        fields,
    };
    p.write_module(module).expect("writing to String is infallible");
    out
}

struct Printer<'a, W: Write> {
    buf: &'a mut W,
    symbols: &'a SymbolTable,
    fields: &'a FieldInterner,
}

impl<W: Write> Printer<'_, W> {
    // ---- Indentation helpers ----

    fn indent(&mut self, level: usize) -> fmt::Result {
        for _ in 0..level {
            self.buf.write_str("  ")?;
        }
        Ok(())
    }

    fn line(&mut self, level: usize, args: fmt::Arguments<'_>) -> fmt::Result {
        self.indent(level)?;
        self.buf.write_fmt(args)?;
        self.buf.write_char('\n')
    }

    // ---- Module ----

    fn write_module(&mut self, module: &Module<'_>) -> fmt::Result {
        self.buf.write_str("module:\n")?;
        if !module.exports.is_empty() {
            self.indent(1)?;
            self.buf.write_str("exports:")?;
            for e in &module.exports {
                write!(self.buf, " {e}")?;
            }
            self.buf.write_char('\n')?;
        }
        for imp in &module.imports {
            self.write_import(imp, 1)?;
        }
        for decl in &module.decls {
            self.write_decl(decl, 1)?;
        }
        Ok(())
    }

    // ---- Imports ----

    fn write_import(&mut self, imp: &Import<'_>, level: usize) -> fmt::Result {
        self.indent(level)?;
        write!(self.buf, "import {}", imp.module)?;
        if !imp.exposing.is_empty() {
            self.buf.write_str(" exposing (")?;
            for (i, name) in imp.exposing.iter().enumerate() {
                if i > 0 {
                    self.buf.write_str(", ")?;
                }
                self.buf.write_str(name)?;
            }
            self.buf.write_char(')')?;
        }
        self.buf.write_char('\n')
    }

    // ---- Declarations ----

    fn write_decl(&mut self, decl: &Decl<'_>, level: usize) -> fmt::Result {
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
                self.indent(level)?;
                let name_str = self.symbols.display(*name);
                write!(self.buf, "{} {}", type_decl_kind(*kind), name_str)?;
                if !type_params.is_empty() {
                    self.buf.write_char('(')?;
                    for (i, p) in type_params.iter().enumerate() {
                        if i > 0 {
                            self.buf.write_str(", ")?;
                        }
                        self.buf.write_str(p)?;
                    }
                    self.buf.write_char(')')?;
                }
                self.buf.write_str(":\n")?;
                self.write_type_expr(ty, level + 1)?;
                if !where_clause.is_empty() {
                    self.line(level + 1, format_args!("where:"))?;
                    for c in where_clause {
                        self.write_constraint(c, level + 2)?;
                    }
                }
                if !methods.is_empty() {
                    self.line(level + 1, format_args!("methods:"))?;
                    for m in methods {
                        self.write_decl(m, level + 2)?;
                    }
                }
                Ok(())
            }
            Decl::FuncDef {
                name, params, body, ..
            } => {
                self.indent(level)?;
                let name_str = self.symbols.display(*name);
                write!(self.buf, "fn {name_str}(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        self.buf.write_str(", ")?;
                    }
                    let pname = self.symbols.display(*p);
                    self.buf.write_str(pname)?;
                }
                self.buf.write_str("):\n")?;
                self.write_expr(body, level + 1)
            }
        }
    }

    fn write_constraint(&mut self, c: &ConstraintDecl<'_>, level: usize) -> fmt::Result {
        self.indent(level)?;
        write!(self.buf, "{}.{}", c.type_var, c.method)?;
        if let Some(ty) = &c.method_type {
            self.buf.write_str(":\n")?;
            self.write_type_expr(ty, level + 1)
        } else {
            self.buf.write_char('\n')
        }
    }

    // ---- Type expressions ----

    fn write_type_expr(&mut self, ty: &TypeExpr<'_>, level: usize) -> fmt::Result {
        match ty {
            TypeExpr::Named(name) => self.line(level, format_args!("Named {name}")),
            TypeExpr::App(name, args) => {
                self.line(level, format_args!("App {name}:"))?;
                for a in args {
                    self.write_type_expr(a, level + 1)?;
                }
                Ok(())
            }
            TypeExpr::TagUnion(tags, _) => {
                self.line(level, format_args!("TagUnion:"))?;
                for t in tags {
                    self.write_tag_decl(t, level + 1)?;
                }
                Ok(())
            }
            TypeExpr::Arrow(params, ret) => {
                self.line(level, format_args!("Arrow:"))?;
                self.line(level + 1, format_args!("params:"))?;
                for p in params {
                    self.write_type_expr(p, level + 2)?;
                }
                self.line(level + 1, format_args!("ret:"))?;
                self.write_type_expr(ret, level + 2)
            }
            TypeExpr::Record(fields) => {
                self.line(level, format_args!("Record:"))?;
                for (field_sym, ty) in fields {
                    let name = self.fields.get(*field_sym);
                    self.line(level + 1, format_args!("{name}:"))?;
                    self.write_type_expr(ty, level + 2)?;
                }
                Ok(())
            }
            TypeExpr::Tuple(elems) => {
                self.line(level, format_args!("Tuple:"))?;
                for e in elems {
                    self.write_type_expr(e, level + 1)?;
                }
                Ok(())
            }
        }
    }

    fn write_tag_decl(&mut self, tag: &TagDecl<'_>, level: usize) -> fmt::Result {
        if tag.fields.is_empty() {
            self.line(level, format_args!("tag {}", tag.name))
        } else {
            self.line(level, format_args!("tag {}:", tag.name))?;
            for field in &tag.fields {
                self.write_type_expr(field, level + 1)?;
            }
            Ok(())
        }
    }

    // ---- Expressions ----

    fn write_expr(&mut self, expr: &Expr<'_>, level: usize) -> fmt::Result {
        let t = fmt_ty(&expr.ty);
        match &expr.kind {
            ExprKind::IntLit(n) => self.line(level, format_args!("IntLit {n} : {t}")),
            ExprKind::FloatLit(n) => self.line(level, format_args!("FloatLit {n} : {t}")),
            ExprKind::StrLit(bytes) => {
                let s = String::from_utf8_lossy(bytes);
                self.line(level, format_args!("StrLit {s:?} : {t}"))
            }
            ExprKind::Name(sym) => {
                let name = self.symbols.display(*sym);
                self.line(level, format_args!("Name {name} : {t}"))
            }
            ExprKind::BinOp { op, lhs, rhs } => {
                self.line(level, format_args!("BinOp {} : {t}:", bin_op(*op)))?;
                self.write_expr(lhs, level + 1)?;
                self.write_expr(rhs, level + 1)
            }
            ExprKind::Call { target, args, .. } => {
                let name = self.symbols.display(*target);
                self.write_named_args(level, "Call", name, args, &t)
            }
            ExprKind::QualifiedCall {
                segments,
                args,
                resolved,
            } => {
                let name = segments.join(".");
                let label = match resolved {
                    Some(r) if *r != name => format!("QualifiedCall {name} => {r}"),
                    _ => format!("QualifiedCall {name}"),
                };
                self.write_named_label(level, &label, args, &t)
            }
            ExprKind::Block(stmts, result) => self.write_block_expr(level, stmts, result, &t),
            ExprKind::If {
                expr: scrutinee,
                arms,
                else_body,
            } => self.write_if_expr(level, scrutinee, arms, else_body.as_deref(), &t),
            ExprKind::Fold {
                expr: scrutinee,
                arms,
            } => self.write_fold_expr(level, scrutinee, arms, &t),
            ExprKind::Lambda { params, body } => self.write_lambda_expr(level, params, body, &t),
            ExprKind::Record { fields } => self.write_record_expr(level, fields, &t),
            ExprKind::FieldAccess { record, field } => {
                let field_name = self.fields.get(*field);
                self.line(level, format_args!("FieldAccess .{field_name} : {t}:"))?;
                self.write_expr(record, level + 1)
            }
            ExprKind::Tuple(elems) => self.write_seq_expr(level, "Tuple", "()", elems, &t),
            ExprKind::ListLit(elems) => self.write_seq_expr(level, "ListLit", "[]", elems, &t),
            ExprKind::MethodCall {
                receiver,
                method,
                args,
                resolved,
            } => self.write_method_call(level, receiver, method, args, resolved.as_deref(), &t),
            ExprKind::Is {
                expr: inner,
                pattern,
            } => self.write_is_expr(level, inner, pattern, &t),
            ExprKind::RecordUpdate { base, updates } => {
                self.line(level, format_args!("RecordUpdate : {t}:"))?;
                self.write_expr(base, level + 1)?;
                for (field_sym, val) in updates {
                    let name = self.fields.get(*field_sym);
                    self.line(level + 1, format_args!("& {name}:"))?;
                    self.write_expr(val, level + 2)?;
                }
                Ok(())
            }
        }
    }

    fn write_named_args(
        &mut self,
        level: usize,
        label: &str,
        name: &str,
        args: &[Expr<'_>],
        ty: &str,
    ) -> fmt::Result {
        if args.is_empty() {
            self.line(level, format_args!("{label} {name} : {ty}"))
        } else {
            self.line(level, format_args!("{label} {name} : {ty}:"))?;
            for a in args {
                self.write_expr(a, level + 1)?;
            }
            Ok(())
        }
    }

    fn write_named_label(
        &mut self,
        level: usize,
        label: &str,
        args: &[Expr<'_>],
        ty: &str,
    ) -> fmt::Result {
        if args.is_empty() {
            self.line(level, format_args!("{label} : {ty}"))
        } else {
            self.line(level, format_args!("{label} : {ty}:"))?;
            for a in args {
                self.write_expr(a, level + 1)?;
            }
            Ok(())
        }
    }

    fn write_seq_expr(
        &mut self,
        level: usize,
        label: &str,
        empty: &str,
        elems: &[Expr<'_>],
        ty: &str,
    ) -> fmt::Result {
        if elems.is_empty() {
            self.line(level, format_args!("{label} {empty} : {ty}"))
        } else {
            self.line(level, format_args!("{label} : {ty}:"))?;
            for e in elems {
                self.write_expr(e, level + 1)?;
            }
            Ok(())
        }
    }

    fn write_block_expr(
        &mut self,
        level: usize,
        stmts: &[Stmt<'_>],
        result: &Expr<'_>,
        ty: &str,
    ) -> fmt::Result {
        self.line(level, format_args!("Block : {ty}:"))?;
        for s in stmts {
            self.write_stmt(s, level + 1)?;
        }
        self.line(level + 1, format_args!("result:"))?;
        self.write_expr(result, level + 2)
    }

    fn write_if_expr(
        &mut self,
        level: usize,
        scrutinee: &Expr<'_>,
        arms: &[MatchArm<'_>],
        else_body: Option<&Expr<'_>>,
        ty: &str,
    ) -> fmt::Result {
        self.line(level, format_args!("If : {ty}:"))?;
        self.line(level + 1, format_args!("scrutinee:"))?;
        self.write_expr(scrutinee, level + 2)?;
        for arm in arms {
            self.write_match_arm(arm, level + 1)?;
        }
        if let Some(eb) = else_body {
            self.line(level + 1, format_args!("else:"))?;
            self.write_expr(eb, level + 2)?;
        }
        Ok(())
    }

    fn write_fold_expr(
        &mut self,
        level: usize,
        scrutinee: &Expr<'_>,
        arms: &[MatchArm<'_>],
        ty: &str,
    ) -> fmt::Result {
        self.line(level, format_args!("Fold : {ty}:"))?;
        self.line(level + 1, format_args!("scrutinee:"))?;
        self.write_expr(scrutinee, level + 2)?;
        for arm in arms {
            self.write_match_arm(arm, level + 1)?;
        }
        Ok(())
    }

    fn write_lambda_expr(
        &mut self,
        level: usize,
        params: &[crate::symbol::SymbolId],
        body: &Expr<'_>,
        ty: &str,
    ) -> fmt::Result {
        self.indent(level)?;
        self.buf.write_str("Lambda(")?;
        for (i, p) in params.iter().enumerate() {
            if i > 0 {
                self.buf.write_str(", ")?;
            }
            self.buf.write_str(self.symbols.display(*p))?;
        }
        writeln!(self.buf, ") : {ty}:")?;
        self.write_expr(body, level + 1)
    }

    fn write_record_expr(
        &mut self,
        level: usize,
        fields: &[(FieldSym, Expr<'_>)],
        ty: &str,
    ) -> fmt::Result {
        if fields.is_empty() {
            self.line(level, format_args!("Record {{}} : {ty}"))
        } else {
            self.line(level, format_args!("Record : {ty}:"))?;
            for (field_sym, val) in fields {
                let name = self.fields.get(*field_sym);
                self.line(level + 1, format_args!("{name}:"))?;
                self.write_expr(val, level + 2)?;
            }
            Ok(())
        }
    }

    fn write_method_call(
        &mut self,
        level: usize,
        receiver: &Expr<'_>,
        method: &str,
        args: &[Expr<'_>],
        resolved: Option<&str>,
        ty: &str,
    ) -> fmt::Result {
        match resolved {
            Some(r) => self.line(
                level,
                format_args!("MethodCall .{method} => {r} : {ty}:"),
            )?,
            None => self.line(level, format_args!("MethodCall .{method} : {ty}:"))?,
        }
        self.line(level + 1, format_args!("receiver:"))?;
        self.write_expr(receiver, level + 2)?;
        if !args.is_empty() {
            self.line(level + 1, format_args!("args:"))?;
            for a in args {
                self.write_expr(a, level + 2)?;
            }
        }
        Ok(())
    }

    fn write_is_expr(
        &mut self,
        level: usize,
        inner: &Expr<'_>,
        pattern: &Pattern<'_>,
        ty: &str,
    ) -> fmt::Result {
        self.line(level, format_args!("Is : {ty}:"))?;
        self.line(level + 1, format_args!("expr:"))?;
        self.write_expr(inner, level + 2)?;
        self.line(level + 1, format_args!("pattern:"))?;
        self.write_pattern(pattern, level + 2)
    }

    // ---- Match arms ----

    fn write_match_arm(&mut self, arm: &MatchArm<'_>, level: usize) -> fmt::Result {
        let header = if arm.is_return {
            "arm (return):"
        } else {
            "arm:"
        };
        self.line(level, format_args!("{header}"))?;
        self.line(level + 1, format_args!("pattern:"))?;
        self.write_pattern(&arm.pattern, level + 2)?;
        if !arm.guards.is_empty() {
            self.line(level + 1, format_args!("guards:"))?;
            for g in &arm.guards {
                self.write_expr(g, level + 2)?;
            }
        }
        self.line(level + 1, format_args!("body:"))?;
        self.write_expr(&arm.body, level + 2)
    }

    // ---- Patterns ----

    fn write_pattern(&mut self, pat: &Pattern<'_>, level: usize) -> fmt::Result {
        match pat {
            Pattern::Wildcard => self.line(level, format_args!("Wildcard")),
            Pattern::Binding(sym) => {
                let name = self.symbols.display(*sym);
                self.line(level, format_args!("Bind {name}"))
            }
            Pattern::Constructor { name, fields } => {
                if fields.is_empty() {
                    self.line(level, format_args!("Con {name}"))
                } else {
                    self.line(level, format_args!("Con {name}:"))?;
                    for field in fields {
                        self.write_pattern(field, level + 1)?;
                    }
                    Ok(())
                }
            }
            Pattern::Record { fields, .. } => {
                if fields.is_empty() {
                    self.line(level, format_args!("PRecord {{}}"))
                } else {
                    self.line(level, format_args!("PRecord:"))?;
                    for (field_sym, sub) in fields {
                        let name = self.fields.get(*field_sym);
                        self.line(level + 1, format_args!("{name}:"))?;
                        self.write_pattern(sub, level + 2)?;
                    }
                    Ok(())
                }
            }
            Pattern::Tuple(elems) => {
                if elems.is_empty() {
                    self.line(level, format_args!("PTuple ()"))
                } else {
                    self.line(level, format_args!("PTuple:"))?;
                    for e in elems {
                        self.write_pattern(e, level + 1)?;
                    }
                    Ok(())
                }
            }
            Pattern::IntLit(n) => self.line(level, format_args!("{n}")),
            Pattern::StrLit(b) => {
                let s = String::from_utf8_lossy(b);
                self.line(level, format_args!("\"{s}\""))
            }
            Pattern::List(elems) => {
                if elems.is_empty() {
                    self.line(level, format_args!("PList []"))
                } else {
                    self.line(level, format_args!("PList:"))?;
                    for elem in elems {
                        match elem {
                            crate::ast::ListPatternElem::Pattern(p) => {
                                self.write_pattern(p, level + 1)?;
                            }
                            crate::ast::ListPatternElem::Spread(Some(sym)) => {
                                let name = self.symbols.display(*sym);
                                self.line(level + 1, format_args!("..{name}"))?;
                            }
                            crate::ast::ListPatternElem::Spread(None) => {
                                self.line(level + 1, format_args!(".."))?;
                            }
                        }
                    }
                    Ok(())
                }
            }
        }
    }

    // ---- Statements ----

    fn write_stmt(&mut self, stmt: &Stmt<'_>, level: usize) -> fmt::Result {
        match stmt {
            Stmt::Let { name, val } => {
                let name_str = self.symbols.display(*name);
                self.line(level, format_args!("Let {name_str}:"))?;
                self.write_expr(val, level + 1)
            }
            Stmt::TypeHint { name, ty } => {
                self.line(level, format_args!("TypeHint {name}:"))?;
                self.write_type_expr(ty, level + 1)
            }
            Stmt::Destructure { pattern, val } => {
                self.line(level, format_args!("Destructure:"))?;
                self.line(level + 1, format_args!("pattern:"))?;
                self.write_pattern(pattern, level + 2)?;
                self.line(level + 1, format_args!("val:"))?;
                self.write_expr(val, level + 2)
            }
            Stmt::Guard {
                condition,
                return_val,
            } => {
                self.line(level, format_args!("Guard:"))?;
                self.line(level + 1, format_args!("cond:"))?;
                self.write_expr(condition, level + 2)?;
                self.line(level + 1, format_args!("return:"))?;
                self.write_expr(return_val, level + 2)
            }
        }
    }
}

// ---- Inferred type rendering ----

/// Format a resolved `Type` compactly for inline display on expression lines.
fn fmt_ty(ty: &Type) -> String {
    let mut out = String::new();
    write_ty(&mut out, ty);
    out
}

fn write_ty(out: &mut String, ty: &Type) {
    match ty {
        // Unresolved type variables render as `'_` because their numeric
        // IDs depend on allocation order — which varies with test
        // parallelism — and the exact ID isn't meaningful for review.
        Type::Var(_) => out.push_str("'_"),
        Type::Con(name) => out.push_str(name),
        Type::App(name, args) => {
            out.push_str(name);
            out.push('(');
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write_ty(out, a);
            }
            out.push(')');
        }
        Type::Arrow(params, ret) => {
            out.push('(');
            for (i, p) in params.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write_ty(out, p);
            }
            out.push_str(") -> ");
            write_ty(out, ret);
        }
        Type::Record { fields, rest } => {
            out.push('{');
            for (i, (name, ty)) in fields.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                } else {
                    out.push(' ');
                }
                out.push_str(name);
                out.push_str(": ");
                write_ty(out, ty);
            }
            if let Some(r) = rest {
                out.push_str(" | ");
                write_ty(out, r);
            }
            out.push_str(" }");
        }
        Type::TagUnion { tags, rest } => {
            out.push('[');
            for (i, (name, payloads)) in tags.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(name);
                if !payloads.is_empty() {
                    out.push('(');
                    for (j, p) in payloads.iter().enumerate() {
                        if j > 0 {
                            out.push_str(", ");
                        }
                        write_ty(out, p);
                    }
                    out.push(')');
                }
            }
            if rest.is_some() {
                if !tags.is_empty() {
                    out.push_str(", ");
                }
                out.push_str("..");
            }
            out.push(']');
        }
        Type::Tuple(elems) => {
            out.push('(');
            for (i, e) in elems.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write_ty(out, e);
            }
            out.push(')');
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

const fn bin_op(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "Add",
        BinOp::Sub => "Sub",
        BinOp::Mul => "Mul",
        BinOp::Div => "Div",
        BinOp::Rem => "Rem",
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
