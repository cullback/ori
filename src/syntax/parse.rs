use pest::Parser as _;
use pest::iterators::Pair;
use pest::pratt_parser::{Assoc, Op, PrattParser};
use pest_derive::Parser;

use crate::error::CompileError;
use crate::syntax::ast::{
    BinOp, ConstraintDecl, Decl, Expr, ExprKind, Import, MatchArm, Module, Pattern, Span, Stmt,
    TagDecl, TypeExpr,
};

#[derive(Parser)]
#[grammar = "syntax/grammar.pest"]
struct OriParser;

fn span_of(pair: &Pair<'_, Rule>) -> Span {
    let pest_span = pair.as_span();
    Span {
        start: pest_span.start(),
        end: pest_span.end(),
    }
}

pub fn parse(source: &str) -> Result<Module<'_>, CompileError> {
    let pairs =
        OriParser::parse(Rule::module, source).map_err(|e| CompileError::new(e.to_string()))?;
    let module_pair = pairs.into_iter().next().unwrap();
    Ok(parse_module(module_pair))
}

fn parse_module(pair: Pair<'_, Rule>) -> Module<'_> {
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
            Rule::decl => decls.push(parse_decl(inner)),
            _ => {}
        }
    }
    Module {
        exports,
        imports,
        decls,
    }
}

fn parse_decl(pair: Pair<'_, Rule>) -> Decl<'_> {
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::type_anno => parse_type_anno(inner),
        Rule::assignment => parse_assignment_as_decl(inner),
        other => panic!("unexpected decl rule: {other:?}"),
    }
}

fn parse_type_anno(pair: Pair<'_, Rule>) -> Decl<'_> {
    let text = pair.as_str();
    let nominal = text.contains(":=");
    let mut inner = pair.into_inner();
    let name = inner.next().unwrap().as_str();

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
                        methods.push(parse_decl(method_pair));
                    }
                }
            }
            _ => {}
        }
    }

    Decl::TypeAnno {
        name,
        type_params,
        ty: ty.expect("type declaration missing type expression"),
        where_clause,
        methods,
        nominal,
    }
}

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

fn parse_assignment_as_decl(pair: Pair<'_, Rule>) -> Decl<'_> {
    let mut inner = pair.into_inner();
    let lhs = inner.next().unwrap(); // irrefutable
    let name = lhs.as_str().trim();
    let body = parse_expr(inner.next().unwrap());

    // If the body is a lambda, extract its params as the function's params
    if let ExprKind::Lambda {
        params,
        body: lam_body,
    } = body.kind
    {
        Decl::FuncDef {
            name,
            params,
            body: *lam_body,
        }
    } else {
        Decl::FuncDef {
            name,
            params: vec![],
            body,
        }
    }
}

// ---- Type expressions ----

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

// ---- Expressions (Pratt parser for operators) ----

fn pratt_parser() -> PrattParser<Rule> {
    PrattParser::new()
        .op(Op::infix(Rule::cmp_op, Assoc::Left))
        .op(Op::infix(Rule::add_op, Assoc::Left))
        .op(Op::infix(Rule::mul_op, Assoc::Left))
}

fn parse_expr(pair: Pair<'_, Rule>) -> Expr<'_> {
    let span = span_of(&pair);
    match pair.as_rule() {
        Rule::expr => {
            let parser = pratt_parser();
            parser
                .map_primary(parse_expr)
                .map_infix(|lhs, op_pair, rhs| {
                    let infix_start = lhs.span.start;
                    let infix_end = rhs.span.end;
                    let infix_span = Span {
                        start: infix_start,
                        end: infix_end,
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
            parse_expr(inner)
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
                    rhs: Box::new(parse_expr(inner)),
                },
                span,
            )
        }
        Rule::call_or_access => parse_call_or_access(pair, span),
        Rule::block => parse_block(pair, span),
        Rule::if_expr => parse_if_expr(pair, span),
        Rule::fold_expr => parse_fold_expr(pair, span),
        Rule::lambda => parse_lambda(pair, span),
        Rule::record_literal => parse_record_literal(pair, span),
        Rule::list_literal => {
            let elements: Vec<Expr<'_>> = pair.into_inner().map(parse_expr).collect();
            Expr::new(ExprKind::ListLit(elements), span)
        }
        Rule::tuple => parse_tuple(pair, span),
        _ => panic!("unexpected expression rule: {:?}", pair.as_rule()),
    }
}

fn parse_call_or_access(pair: Pair<'_, Rule>, span: Span) -> Expr<'_> {
    let mut inner: Vec<Pair<'_, Rule>> = pair.into_inner().collect();
    let first = inner.remove(0);

    match first.as_rule() {
        Rule::qualified_head => {
            let text = first.as_str();
            let without_paren = &text[..text.len() - 1];
            let segments: Vec<&str> = without_paren.split('.').collect();
            let args = inner
                .first()
                .filter(|p| p.as_rule() == Rule::args)
                .map(|p| p.clone().into_inner().map(parse_expr).collect())
                .unwrap_or_default();
            Expr::new(ExprKind::QualifiedCall { segments, args }, span)
        }
        Rule::call_head => {
            let text = first.as_str();
            let func = &text[..text.len() - 1];
            let args = inner
                .first()
                .filter(|p| p.as_rule() == Rule::args)
                .map(|p| p.clone().into_inner().map(parse_expr).collect())
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

fn parse_block(pair: Pair<'_, Rule>, span: Span) -> Expr<'_> {
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
                        let val = parse_expr(parts.next().unwrap());
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
                result_expr = Some(parse_expr(inner));
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

fn parse_if_expr(pair: Pair<'_, Rule>, span: Span) -> Expr<'_> {
    let mut inner: Vec<Pair<'_, Rule>> = pair.into_inner().collect();

    // Check if it's boolean if-then-else or multi-arm match
    let has_match_arm = inner.iter().any(|p| p.as_rule() == Rule::match_arm);

    let scrutinee = parse_expr(inner.remove(0));
    if has_match_arm {
        let mut arms = Vec::new();
        let mut else_body = None;

        for part in inner {
            match part.as_rule() {
                Rule::match_arm => arms.push(parse_match_arm(part)),
                Rule::expr | Rule::atom => else_body = Some(Box::new(parse_expr(part))),
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
        let then_body = parse_expr(inner.remove(0));
        let else_body = parse_expr(inner.remove(0));

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

fn parse_fold_expr(pair: Pair<'_, Rule>, span: Span) -> Expr<'_> {
    let mut inner = pair.into_inner();
    let scrutinee = parse_expr(inner.next().unwrap());
    let arms: Vec<MatchArm<'_>> = inner.map(parse_match_arm).collect();
    Expr::new(
        ExprKind::Fold {
            expr: Box::new(scrutinee),
            arms,
        },
        span,
    )
}

fn parse_match_arm(pair: Pair<'_, Rule>) -> MatchArm<'_> {
    let mut inner = pair.into_inner();
    let pattern = parse_pattern(inner.next().unwrap());
    let body = parse_expr(inner.next().unwrap());
    MatchArm { pattern, body }
}

fn parse_lambda(pair: Pair<'_, Rule>, span: Span) -> Expr<'_> {
    let mut inner: Vec<Pair<'_, Rule>> = pair.into_inner().collect();
    let body = parse_expr(inner.pop().unwrap());
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

fn parse_record_literal(pair: Pair<'_, Rule>, span: Span) -> Expr<'_> {
    let fields: Vec<(&str, Expr<'_>)> = pair
        .into_inner()
        .map(|fi| {
            let mut inner = fi.into_inner();
            let name = inner.next().unwrap().as_str();
            let val = parse_expr(inner.next().unwrap());
            (name, val)
        })
        .collect();
    Expr::new(ExprKind::Record { fields }, span)
}

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

fn parse_tuple(pair: Pair<'_, Rule>, span: Span) -> Expr<'_> {
    let elements: Vec<Expr<'_>> = pair.into_inner().map(parse_expr).collect();
    Expr::new(ExprKind::Tuple(elements), span)
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
