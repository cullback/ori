use std::collections::HashMap;

use pest::Parser as _;
use pest::iterators::Pair;
use pest::pratt_parser::{Assoc, Op, PrattParser};
use pest_derive::Parser;

use crate::error::CompileError;
use crate::source::FileId;
use crate::syntax::ast::{
    BinOp, ConstraintDecl, Decl, Expr, ExprKind, Import, MatchArm, Module, Pattern, Span, Stmt,
    TagDecl, TypeDeclKind, TypeExpr,
};

#[derive(Parser)]
#[grammar = "syntax/grammar.pest"]
struct OriParser;

struct ParseCtx {
    file: FileId,
    /// Maps byte offset of the first non-comment token after a comment block
    /// to the accumulated doc string.
    doc_comments: HashMap<usize, String>,
}

pub fn parse(source: &str, file: FileId) -> Result<Module<'_>, CompileError> {
    let pairs =
        OriParser::parse(Rule::module, source).map_err(|e| CompileError::new(e.to_string()))?;
    let module_pair = pairs.into_iter().next().unwrap();
    let doc_comments = extract_doc_comments(source);
    let ctx = ParseCtx { file, doc_comments };
    Ok(ctx.parse_module(module_pair))
}

/// Pre-pass: collect `#` comment blocks and map them to the byte offset of
/// the next non-blank, non-comment line. The parser attaches these as doc
/// comments to any `Decl` whose span starts at that offset.
fn extract_doc_comments(source: &str) -> HashMap<usize, String> {
    let mut docs = HashMap::new();
    let mut comment_lines: Vec<String> = Vec::new();
    let mut offset = 0;

    for line in source.split('\n') {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix('#') {
            // Strip one leading space after # if present
            let content = rest.strip_prefix(' ').unwrap_or(rest);
            comment_lines.push(content.to_owned());
        } else if trimmed.is_empty() {
            // Blank line breaks the doc comment block
            comment_lines.clear();
        } else if !comment_lines.is_empty() {
            // Non-blank, non-comment line: record the doc comment at
            // the byte offset of the first non-whitespace character
            let leading = line.len() - line.trim_start().len();
            let target = offset + leading;
            docs.insert(target, comment_lines.join("\n"));
            comment_lines.clear();
        } else {
            // Non-blank, non-comment line with no preceding comment block
        }
        offset += line.len() + 1; // +1 for the \n
    }
    docs
}

impl ParseCtx {
    fn span_of(&self, pair: &Pair<'_, Rule>) -> Span {
        let pest_span = pair.as_span();
        Span {
            file: self.file,
            start: pest_span.start(),
            end: pest_span.end(),
        }
    }

    fn doc_at(&self, span: &Span) -> Option<String> {
        self.doc_comments.get(&span.start).cloned()
    }

    fn parse_module<'src>(&self, pair: Pair<'src, Rule>) -> Module<'src> {
        let mut exports = Vec::new();
        let mut imports = Vec::new();
        let mut decls = Vec::new();
        for inner in pair.into_inner() {
            match inner.as_rule() {
                Rule::exports_decl => {
                    exports = inner
                        .into_inner()
                        .filter(|p| p.as_rule() == Rule::name)
                        .map(|p| p.as_str())
                        .collect();
                }
                Rule::import_decl => {
                    let mut parts = inner.into_inner();
                    let module = parts.next().unwrap().as_str();
                    let exposing = parts
                        .find(|p| p.as_rule() == Rule::exposing_clause)
                        .map(|clause| {
                            clause
                                .into_inner()
                                .filter(|p| p.as_rule() == Rule::name)
                                .map(|p| p.as_str())
                                .collect()
                        })
                        .unwrap_or_default();
                    imports.push(Import { module, exposing });
                }
                Rule::decl => decls.push(self.parse_decl(inner)),
                _ => {}
            }
        }
        Module {
            exports,
            imports,
            decls,
        }
    }

    fn parse_decl<'src>(&self, pair: Pair<'src, Rule>) -> Decl<'src> {
        let inner = pair.into_inner().next().unwrap();
        match inner.as_rule() {
            Rule::type_anno => self.parse_type_anno(inner),
            Rule::assignment => self.parse_assignment_as_decl(inner),
            other => panic!("unexpected decl rule: {other:?}"),
        }
    }

    fn parse_type_anno<'src>(&self, pair: Pair<'src, Rule>) -> Decl<'src> {
        let span = self.span_of(&pair);
        let doc = self.doc_at(&span);
        let text = pair.as_str();
        let kind = if text.contains(":=") {
            TypeDeclKind::Transparent
        } else if text.contains("::") {
            TypeDeclKind::Opaque
        } else {
            TypeDeclKind::Alias
        };
        let mut inner = pair.into_inner();
        let first = inner.next().unwrap();
        let name = match first.as_rule() {
            Rule::type_head => {
                let text = first.as_str();
                &text[..text.len() - 1] // strip trailing "("
            }
            _ => first.as_str(), // plain name
        };

        let mut type_params = Vec::new();
        let mut ty = None;
        let mut where_clause = Vec::new();
        let mut methods = Vec::new();

        for part in inner {
            match part.as_rule() {
                Rule::type_params => {
                    for p in part.into_inner() {
                        type_params.push(p.as_str());
                    }
                }
                Rule::type_expr | Rule::type_atom => {
                    ty = Some(parse_type_expr(part));
                }
                Rule::where_clause => {
                    for constraint in part.into_inner() {
                        if constraint.as_rule() == Rule::constraint_decl {
                            where_clause.push(parse_constraint_decl(constraint));
                        }
                    }
                }
                Rule::method_block => {
                    for method_pair in part.into_inner() {
                        if method_pair.as_rule() == Rule::decl {
                            methods.push(self.parse_decl(method_pair));
                        }
                    }
                }
                _ => {}
            }
        }

        Decl::TypeAnno {
            span,
            name,
            type_params,
            ty: ty.expect("type declaration missing type expression"),
            where_clause,
            methods,
            kind,
            doc,
        }
    }

    fn parse_assignment_as_decl<'src>(&self, pair: Pair<'src, Rule>) -> Decl<'src> {
        let span = self.span_of(&pair);
        let doc = self.doc_at(&span);
        let mut inner = pair.into_inner();
        let lhs = inner.next().unwrap(); // irrefutable
        let name = lhs.as_str().trim();
        let body = self.parse_expr(inner.next().unwrap());

        // If the body is a lambda, extract its params as the function's params
        if let ExprKind::Lambda {
            params,
            body: lam_body,
        } = body.kind
        {
            Decl::FuncDef {
                span,
                name,
                params,
                body: *lam_body,
                doc,
            }
        } else {
            Decl::FuncDef {
                span,
                name,
                params: vec![],
                body,
                doc,
            }
        }
    }

    // ---- Expressions (Pratt parser for operators) ----

    fn parse_expr<'src>(&self, pair: Pair<'src, Rule>) -> Expr<'src> {
        let span = self.span_of(&pair);
        match pair.as_rule() {
            Rule::expr => {
                let parser = pratt_parser();
                parser
                    .map_primary(|p| self.parse_expr(p))
                    .map_infix(|lhs, op_pair, rhs| {
                        let infix_span = Span {
                            file: self.file,
                            start: lhs.span.start,
                            end: rhs.span.end,
                        };
                        let binop = match op_pair.as_str() {
                            "+" => BinOp::Add,
                            "-" => BinOp::Sub,
                            "*" => BinOp::Mul,
                            "/" => BinOp::Div,
                            "%" => BinOp::Rem,
                            "==" => BinOp::Eq,
                            "!=" => BinOp::Neq,
                            other => panic!("unknown operator: {other}"),
                        };
                        Expr::new(
                            ExprKind::BinOp {
                                op: binop,
                                lhs: Box::new(lhs),
                                rhs: Box::new(rhs),
                            },
                            infix_span,
                        )
                    })
                    .parse(pair.into_inner())
            }
            Rule::atom => {
                let inner = pair.into_inner().next().unwrap();
                self.parse_expr(inner)
            }
            Rule::string_lit => {
                let raw = pair.as_str();
                // Strip surrounding quotes
                let inner = &raw[1..raw.len() - 1];
                let bytes = unescape_string(inner);
                Expr::new(ExprKind::StrLit(bytes), span)
            }
            Rule::float_lit => {
                let n: f64 = pair.as_str().parse().unwrap();
                Expr::new(ExprKind::FloatLit(n), span)
            }
            Rule::int_lit => {
                let n: i64 = pair.as_str().parse().unwrap();
                Expr::new(ExprKind::IntLit(n), span)
            }
            Rule::neg_expr => {
                let inner = pair.into_inner().next().unwrap();
                Expr::new(
                    ExprKind::BinOp {
                        op: BinOp::Sub,
                        lhs: Box::new(Expr::new(ExprKind::IntLit(0), span)),
                        rhs: Box::new(self.parse_expr(inner)),
                    },
                    span,
                )
            }
            Rule::call_or_access => self.parse_call_or_access(pair, span),
            Rule::block => self.parse_block(pair, span),
            Rule::if_expr => self.parse_if_expr(pair, span),
            Rule::fold_expr => self.parse_fold_expr(pair, span),
            Rule::lambda => self.parse_lambda(pair, span),
            Rule::record_literal => self.parse_record_literal(pair, span),
            Rule::list_literal => {
                let elements: Vec<Expr<'_>> =
                    pair.into_inner().map(|p| self.parse_expr(p)).collect();
                Expr::new(ExprKind::ListLit(elements), span)
            }
            Rule::tuple => self.parse_tuple(pair, span),
            _ => panic!("unexpected expression rule: {:?}", pair.as_rule()),
        }
    }

    fn parse_call_or_access<'src>(&self, pair: Pair<'src, Rule>, span: Span) -> Expr<'src> {
        let mut inner: Vec<Pair<'src, Rule>> = pair.into_inner().collect();
        let first = inner.remove(0);

        match first.as_rule() {
            Rule::qualified_head => {
                let text = first.as_str();
                let without_paren = &text[..text.len() - 1];
                let segments: Vec<&str> = without_paren.split('.').collect();
                let args = inner
                    .first()
                    .filter(|p| p.as_rule() == Rule::args)
                    .map(|p| p.clone().into_inner().map(|a| self.parse_expr(a)).collect())
                    .unwrap_or_default();
                Expr::new(ExprKind::QualifiedCall { segments, args }, span)
            }
            Rule::call_head => {
                let text = first.as_str();
                let func = &text[..text.len() - 1];
                let args = inner
                    .first()
                    .filter(|p| p.as_rule() == Rule::args)
                    .map(|p| p.clone().into_inner().map(|a| self.parse_expr(a)).collect())
                    .unwrap_or_default();
                Expr::new(ExprKind::Call { func, args }, span)
            }
            Rule::name => {
                let first_name = first.as_str();
                if inner.is_empty() {
                    return Expr::new(ExprKind::Name(first_name), span);
                }
                // Field access chain
                let mut result = Expr::new(ExprKind::Name(first_name), span);
                for field in inner {
                    if field.as_rule() == Rule::name {
                        result = Expr::new(
                            ExprKind::FieldAccess {
                                record: Box::new(result),
                                field: field.as_str(),
                            },
                            span,
                        );
                    }
                }
                result
            }
            other => panic!("unexpected call_or_access child: {other:?}"),
        }
    }

    fn parse_block<'src>(&self, pair: Pair<'src, Rule>, span: Span) -> Expr<'src> {
        let mut stmts = Vec::new();
        let mut result_expr = None;

        // block = { "(" ~ block_body ~ ")" }, so descend into block_body
        let body = pair
            .into_inner()
            .find(|p| p.as_rule() == Rule::block_body)
            .unwrap_or_else(|| panic!("block missing block_body"));

        for inner in body.into_inner() {
            match inner.as_rule() {
                Rule::block_stmt => {
                    let stmt_inner = inner.into_inner().next().unwrap();
                    match stmt_inner.as_rule() {
                        Rule::assignment => {
                            let mut parts = stmt_inner.into_inner();
                            let lhs = parts.next().unwrap(); // irrefutable
                            let val = self.parse_expr(parts.next().unwrap());
                            let pattern = parse_irrefutable(lhs);
                            match pattern {
                                Pattern::Binding(name) => {
                                    stmts.push(Stmt::Let { name, val });
                                }
                                _ => {
                                    stmts.push(Stmt::Destructure { pattern, val });
                                }
                            }
                        }
                        Rule::type_hint => {
                            let mut parts = stmt_inner.into_inner();
                            let name = parts.next().unwrap().as_str();
                            let ty = parse_type_expr(parts.next().unwrap());
                            stmts.push(Stmt::TypeHint { name, ty });
                        }
                        other => panic!("unexpected block statement: {other:?}"),
                    }
                }
                Rule::expr | Rule::atom => {
                    result_expr = Some(self.parse_expr(inner));
                }
                _ => {}
            }
        }

        let result = result_expr.expect("block must have a result expression");
        if stmts.is_empty() {
            result
        } else {
            Expr::new(ExprKind::Block(stmts, Box::new(result)), span)
        }
    }

    fn parse_if_expr<'src>(&self, pair: Pair<'src, Rule>, span: Span) -> Expr<'src> {
        let mut inner: Vec<Pair<'src, Rule>> = pair.into_inner().collect();

        // Check if it's boolean if-then-else or multi-arm match
        let has_match_arm = inner.iter().any(|p| p.as_rule() == Rule::match_arm);

        let scrutinee = self.parse_expr(inner.remove(0));
        if has_match_arm {
            let mut arms = Vec::new();
            let mut else_body = None;

            for part in inner {
                match part.as_rule() {
                    Rule::match_arm => arms.push(self.parse_match_arm(part)),
                    Rule::expr | Rule::atom => else_body = Some(Box::new(self.parse_expr(part))),
                    _ => {}
                }
            }

            Expr::new(
                ExprKind::If {
                    expr: Box::new(scrutinee),
                    arms,
                    else_body,
                },
                span,
            )
        } else {
            let then_body = self.parse_expr(inner.remove(0));
            let else_body = self.parse_expr(inner.remove(0));

            Expr::new(
                ExprKind::If {
                    expr: Box::new(scrutinee),
                    arms: vec![
                        MatchArm {
                            pattern: Pattern::Constructor {
                                name: "True",
                                fields: vec![],
                            },
                            body: then_body,
                        },
                        MatchArm {
                            pattern: Pattern::Constructor {
                                name: "False",
                                fields: vec![],
                            },
                            body: else_body,
                        },
                    ],
                    else_body: None,
                },
                span,
            )
        }
    }

    fn parse_fold_expr<'src>(&self, pair: Pair<'src, Rule>, span: Span) -> Expr<'src> {
        let mut inner = pair.into_inner();
        let scrutinee = self.parse_expr(inner.next().unwrap());
        let arms: Vec<MatchArm<'_>> = inner.map(|p| self.parse_match_arm(p)).collect();
        Expr::new(
            ExprKind::Fold {
                expr: Box::new(scrutinee),
                arms,
            },
            span,
        )
    }

    fn parse_match_arm<'src>(&self, pair: Pair<'src, Rule>) -> MatchArm<'src> {
        let mut inner = pair.into_inner();
        let pattern = parse_pattern(inner.next().unwrap());
        let body = self.parse_expr(inner.next().unwrap());
        MatchArm { pattern, body }
    }

    fn parse_lambda<'src>(&self, pair: Pair<'src, Rule>, span: Span) -> Expr<'src> {
        let mut inner: Vec<Pair<'src, Rule>> = pair.into_inner().collect();
        let body = self.parse_expr(inner.pop().unwrap());
        let params: Vec<&str> = inner
            .into_iter()
            .filter(|p| p.as_rule() == Rule::lambda_param)
            .map(|p| p.as_str())
            .collect();
        Expr::new(
            ExprKind::Lambda {
                params,
                body: Box::new(body),
            },
            span,
        )
    }

    fn parse_record_literal<'src>(&self, pair: Pair<'src, Rule>, span: Span) -> Expr<'src> {
        let fields: Vec<(&str, Expr<'_>)> = pair
            .into_inner()
            .map(|fi| {
                let mut inner = fi.into_inner();
                let name = inner.next().unwrap().as_str();
                let val = self.parse_expr(inner.next().unwrap());
                (name, val)
            })
            .collect();
        Expr::new(ExprKind::Record { fields }, span)
    }

    fn parse_tuple<'src>(&self, pair: Pair<'src, Rule>, span: Span) -> Expr<'src> {
        let elements: Vec<Expr<'_>> = pair.into_inner().map(|p| self.parse_expr(p)).collect();
        Expr::new(ExprKind::Tuple(elements), span)
    }
}

// ---- Type expressions (no span needed, stateless) ----

fn parse_constraint_decl(pair: Pair<'_, Rule>) -> ConstraintDecl<'_> {
    let mut inner = pair.into_inner();
    let type_var = inner.next().unwrap().as_str();
    let method = inner.next().unwrap().as_str();
    let method_type = inner.next().map(parse_type_expr);
    ConstraintDecl {
        type_var,
        method,
        method_type,
    }
}

fn parse_type_expr(pair: Pair<'_, Rule>) -> TypeExpr<'_> {
    match pair.as_rule() {
        Rule::type_expr => {
            let mut parts: Vec<Pair<'_, Rule>> = pair.into_inner().collect();
            // Check if last element is a type_expr (Arrow return type)
            if parts.len() >= 2 && parts.last().is_some_and(|p| p.as_rule() == Rule::type_expr) {
                let ret = parse_type_expr(parts.pop().unwrap());
                let params: Vec<TypeExpr<'_>> = parts.into_iter().map(parse_type_expr).collect();
                TypeExpr::Arrow(params, Box::new(ret))
            } else if parts.len() == 1 {
                parse_type_expr(parts.pop().unwrap())
            } else {
                panic!("unexpected type_expr structure");
            }
        }
        Rule::type_atom => {
            let mut inner: Vec<Pair<'_, Rule>> = pair.into_inner().collect();
            if inner.is_empty() {
                // Empty record type: {} (unit type)
                return TypeExpr::Record(vec![]);
            }
            let first = &inner[0];
            match first.as_rule() {
                Rule::name => {
                    let name = first.as_str();
                    if inner.len() == 1 {
                        TypeExpr::Named(name)
                    } else if inner[1].as_rule() == Rule::type_atom {
                        let args: Vec<TypeExpr<'_>> =
                            inner.drain(1..).map(parse_type_expr).collect();
                        TypeExpr::App(name, args)
                    } else {
                        panic!("unexpected type_atom after name");
                    }
                }
                Rule::tag_decl => {
                    let tags: Vec<TagDecl<'_>> = inner.into_iter().map(parse_tag_decl).collect();
                    TypeExpr::TagUnion(tags)
                }
                Rule::field_type => {
                    let fields: Vec<(&str, TypeExpr<'_>)> =
                        inner.into_iter().map(parse_field_type).collect();
                    TypeExpr::Record(fields)
                }
                Rule::type_atom => {
                    // Tuple type: all children are type_atoms
                    let elements: Vec<TypeExpr<'_>> =
                        inner.into_iter().map(parse_type_expr).collect();
                    TypeExpr::Tuple(elements)
                }
                Rule::type_expr => {
                    // Parenthesized type expression: (A -> B)
                    parse_type_expr(inner.into_iter().next().unwrap())
                }
                _ => panic!("unexpected type_atom content: {:?}", first.as_rule()),
            }
        }
        _ => panic!("unexpected rule in type position: {:?}", pair.as_rule()),
    }
}

fn parse_tag_decl(pair: Pair<'_, Rule>) -> TagDecl<'_> {
    let mut inner = pair.into_inner();
    let name = inner.next().unwrap().as_str();
    let fields: Vec<TypeExpr<'_>> = inner.map(parse_type_expr).collect();
    TagDecl { name, fields }
}

fn parse_field_type(pair: Pair<'_, Rule>) -> (&str, TypeExpr<'_>) {
    let mut inner = pair.into_inner();
    let name = inner.next().unwrap().as_str();
    let ty = parse_type_expr(inner.next().unwrap());
    (name, ty)
}

// ---- Pratt parser ----

fn pratt_parser() -> PrattParser<Rule> {
    PrattParser::new()
        .op(Op::infix(Rule::cmp_op, Assoc::Left))
        .op(Op::infix(Rule::add_op, Assoc::Left))
        .op(Op::infix(Rule::mul_op, Assoc::Left))
}

// ---- Irrefutable patterns (no span needed) ----

fn parse_irrefutable(pair: Pair<'_, Rule>) -> Pattern<'_> {
    let text = pair.as_str().trim();
    if text == "_" {
        return Pattern::Wildcard;
    }
    let inner: Vec<Pair<'_, Rule>> = pair.into_inner().collect();
    if inner.is_empty() {
        if text == "_" {
            return Pattern::Wildcard;
        }
        return Pattern::Binding(text);
    }
    if inner.len() == 1 && inner[0].as_rule() == Rule::name {
        return Pattern::Binding(inner[0].as_str());
    }
    let first = &inner[0];
    match first.as_rule() {
        Rule::irrefutable => {
            // Tuple pattern: (a, b)
            let sub_pats: Vec<Pattern<'_>> = inner
                .into_iter()
                .filter(|p| p.as_rule() == Rule::irrefutable)
                .map(parse_irrefutable)
                .collect();
            Pattern::Tuple(sub_pats)
        }
        Rule::field_irrefutable => {
            // Record pattern: { x, y: z }
            let fields: Vec<(&str, Pattern<'_>)> = inner
                .into_iter()
                .map(|fi| {
                    let mut fi_inner = fi.into_inner();
                    let name = fi_inner.next().unwrap().as_str();
                    if let Some(pat) = fi_inner.next() {
                        (name, parse_irrefutable(pat))
                    } else {
                        (name, Pattern::Binding(name))
                    }
                })
                .collect();
            Pattern::Record { fields }
        }
        _ => panic!("unexpected irrefutable pattern: {:?}", first.as_rule()),
    }
}

// ---- Patterns ----

fn is_constructor_name(s: &str) -> bool {
    s.starts_with(|c: char| c.is_ascii_uppercase())
}

fn parse_pattern(pair: Pair<'_, Rule>) -> Pattern<'_> {
    let text = pair.as_str().trim();
    let inner: Vec<Pair<'_, Rule>> = pair.into_inner().collect();

    if inner.is_empty() {
        if text == "_" {
            return Pattern::Wildcard;
        }
        panic!("empty pattern: '{text}'");
    }

    let first = &inner[0];
    match first.as_rule() {
        Rule::name => {
            let name = first.as_str();
            if inner.len() > 1 {
                // Constructor with fields: Name(pat, ...)
                let fields: Vec<Pattern<'_>> =
                    inner.into_iter().skip(1).map(parse_pattern).collect();
                Pattern::Constructor { name, fields }
            } else if is_constructor_name(name) {
                // Bare uppercase name: nullary constructor
                Pattern::Constructor {
                    name,
                    fields: vec![],
                }
            } else {
                Pattern::Binding(name)
            }
        }
        Rule::field_pattern => {
            let fields: Vec<(&str, Pattern<'_>)> =
                inner.into_iter().map(parse_field_pattern).collect();
            Pattern::Record { fields }
        }
        Rule::pattern => {
            // Tuple pattern: all children are sub-patterns
            let elements: Vec<Pattern<'_>> = inner.into_iter().map(parse_pattern).collect();
            Pattern::Tuple(elements)
        }
        _ => {
            if first.as_str() == "_" {
                Pattern::Wildcard
            } else {
                panic!("unexpected pattern: {:?}", first.as_rule());
            }
        }
    }
}

fn parse_field_pattern(pair: Pair<'_, Rule>) -> (&str, Pattern<'_>) {
    let mut inner = pair.into_inner();
    let name = inner.next().unwrap().as_str();
    if let Some(pat) = inner.next() {
        (name, parse_pattern(pat))
    } else {
        (name, Pattern::Binding(name))
    }
}

/// Process escape sequences in a string literal and return UTF-8 bytes.
fn unescape_string(s: &str) -> Vec<u8> {
    let mut bytes = Vec::new();
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => bytes.push(b'\n'),
                Some('t') => bytes.push(b'\t'),
                Some('r') => bytes.push(b'\r'),
                Some('0') => bytes.push(0),
                Some('"') => bytes.push(b'"'),
                Some('\\') | None => bytes.push(b'\\'),
                Some(other) => {
                    bytes.push(b'\\');
                    let mut buf = [0_u8; 4];
                    bytes.extend_from_slice(other.encode_utf8(&mut buf).as_bytes());
                }
            }
        } else {
            let mut buf = [0_u8; 4];
            bytes.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
        }
    }
    bytes
}
