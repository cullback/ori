use pest::Parser as _;
use pest::iterators::Pair;
use pest::pratt_parser::{Assoc, Op, PrattParser};
use pest_derive::Parser;

use crate::ast::{
    BinOp, Decl, Expr, ExprKind, MatchArm, Module, Pattern, Span, Stmt, TagDecl, TypeExpr,
};

#[derive(Parser)]
#[grammar = "ori.pest"]
struct OriParser;

fn span_of(pair: &Pair<'_, Rule>) -> Span {
    let pest_span = pair.as_span();
    Span {
        start: pest_span.start(),
        end: pest_span.end(),
    }
}

pub fn parse(source: &str) -> Module {
    let pairs = OriParser::parse(Rule::module, source).unwrap_or_else(|e| panic!("{e}"));
    let module_pair = pairs.into_iter().next().unwrap();
    parse_module(module_pair)
}

fn parse_module(pair: Pair<'_, Rule>) -> Module {
    let mut decls = Vec::new();
    for inner in pair.into_inner() {
        if inner.as_rule() == Rule::decl {
            decls.push(parse_decl(inner));
        }
    }
    Module { decls }
}

fn parse_decl(pair: Pair<'_, Rule>) -> Decl {
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::type_anno => parse_type_anno(inner),
        Rule::assignment => parse_assignment_as_decl(inner),
        other => panic!("unexpected decl rule: {other:?}"),
    }
}

fn parse_type_anno(pair: Pair<'_, Rule>) -> Decl {
    let mut inner = pair.into_inner();
    let name = inner.next().unwrap().as_str().to_owned();

    let mut type_params = Vec::new();
    let mut ty = None;
    let mut methods = Vec::new();

    for part in inner {
        match part.as_rule() {
            Rule::type_params => {
                for p in part.into_inner() {
                    type_params.push(p.as_str().to_owned());
                }
            }
            Rule::type_expr | Rule::type_atom => {
                ty = Some(parse_type_expr(part));
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
        ty: ty.expect("type annotation missing type"),
        methods,
    }
}

fn parse_assignment_as_decl(pair: Pair<'_, Rule>) -> Decl {
    let mut inner = pair.into_inner();
    let lhs = inner.next().unwrap(); // irrefutable
    let name = lhs.as_str().trim().to_owned();
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

fn parse_type_expr(pair: Pair<'_, Rule>) -> TypeExpr {
    match pair.as_rule() {
        Rule::type_expr => {
            let mut parts: Vec<Pair<'_, Rule>> = pair.into_inner().collect();
            // Check if last element is a type_expr (Arrow return type)
            if parts.len() >= 2 && parts.last().is_some_and(|p| p.as_rule() == Rule::type_expr) {
                let ret = parse_type_expr(parts.pop().unwrap());
                let params: Vec<TypeExpr> = parts.into_iter().map(parse_type_expr).collect();
                TypeExpr::Arrow(params, Box::new(ret))
            } else if parts.len() == 1 {
                parse_type_expr(parts.pop().unwrap())
            } else {
                panic!("unexpected type_expr structure");
            }
        }
        Rule::type_atom => {
            let mut inner: Vec<Pair<'_, Rule>> = pair.into_inner().collect();
            assert!(!inner.is_empty(), "empty type_atom");
            let first = &inner[0];
            match first.as_rule() {
                Rule::type_name => {
                    let name = first.as_str().to_owned();
                    if inner.len() == 1 {
                        TypeExpr::Named(name)
                    } else {
                        let args: Vec<TypeExpr> = inner.drain(1..).map(parse_type_expr).collect();
                        TypeExpr::App(name, args)
                    }
                }
                Rule::tag_decl => {
                    let tags: Vec<TagDecl> = inner.into_iter().map(parse_tag_decl).collect();
                    TypeExpr::TagUnion(tags)
                }
                Rule::field_type => {
                    let fields: Vec<(String, TypeExpr)> =
                        inner.into_iter().map(parse_field_type).collect();
                    TypeExpr::Record(fields)
                }
                Rule::type_atom => {
                    // Tuple type: all children are type_atoms
                    let elements: Vec<TypeExpr> = inner.into_iter().map(parse_type_expr).collect();
                    TypeExpr::Tuple(elements)
                }
                _ => panic!("unexpected type_atom content: {:?}", first.as_rule()),
            }
        }
        _ => panic!("unexpected rule in type position: {:?}", pair.as_rule()),
    }
}

fn parse_tag_decl(pair: Pair<'_, Rule>) -> TagDecl {
    let mut inner = pair.into_inner();
    let name = inner.next().unwrap().as_str().to_owned();
    let fields: Vec<TypeExpr> = inner.map(parse_type_expr).collect();
    TagDecl { name, fields }
}

fn parse_field_type(pair: Pair<'_, Rule>) -> (String, TypeExpr) {
    let mut inner = pair.into_inner();
    let name = inner.next().unwrap().as_str().to_owned();
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

fn parse_expr(pair: Pair<'_, Rule>) -> Expr {
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
        Rule::prefix => {
            let inner = pair.into_inner().next().unwrap();
            parse_expr(inner)
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
        Rule::tuple => parse_tuple(pair, span),
        _ => panic!("unexpected expression rule: {:?}", pair.as_rule()),
    }
}

fn parse_call_head(text: &str) -> (&str, Option<(&str, &str)>) {
    // Atomic head text like "List.sum(" or "foo(" or "Cons("
    let without_paren = &text[..text.len() - 1];
    if let Some(dot_pos) = without_paren.find('.') {
        let owner = &without_paren[..dot_pos];
        let method = &without_paren[dot_pos + 1..];
        (owner, Some((owner, method)))
    } else {
        (without_paren, None)
    }
}

fn parse_call_or_access(pair: Pair<'_, Rule>, span: Span) -> Expr {
    let mut inner: Vec<Pair<'_, Rule>> = pair.into_inner().collect();
    let first = inner.remove(0);

    match first.as_rule() {
        Rule::qualified_head => {
            let text = first.as_str();
            let (_, Some((owner, method))) = parse_call_head(text) else {
                unreachable!()
            };
            let args = inner
                .first()
                .filter(|p| p.as_rule() == Rule::args)
                .map(|p| p.clone().into_inner().map(parse_expr).collect())
                .unwrap_or_default();
            Expr::new(
                ExprKind::QualifiedCall {
                    owner: owner.to_owned(),
                    method: method.to_owned(),
                    args,
                },
                span,
            )
        }
        Rule::constructor_head | Rule::function_head => {
            let text = first.as_str();
            let func = text[..text.len() - 1].to_owned();
            let args = inner
                .first()
                .filter(|p| p.as_rule() == Rule::args)
                .map(|p| p.clone().into_inner().map(parse_expr).collect())
                .unwrap_or_default();
            Expr::new(ExprKind::Call { func, args }, span)
        }
        Rule::constructor | Rule::ident => {
            let first_name = first.as_str().to_owned();
            if inner.is_empty() {
                return Expr::new(ExprKind::Name(first_name), span);
            }
            // Field access chain
            let mut result = Expr::new(ExprKind::Name(first_name), span);
            for field in inner {
                if field.as_rule() == Rule::ident {
                    result = Expr::new(
                        ExprKind::FieldAccess {
                            record: Box::new(result),
                            field: field.as_str().to_owned(),
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

fn parse_block(pair: Pair<'_, Rule>, span: Span) -> Expr {
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
                                stmts.push(Stmt::TupleDestructure { pattern, val });
                            }
                        }
                    }
                    Rule::type_hint => {
                        let mut parts = stmt_inner.into_inner();
                        let name = parts.next().unwrap().as_str().to_owned();
                        let ty = parse_type_expr(parts.next().unwrap());
                        stmts.push(Stmt::TypeHint { name, ty });
                    }
                    other => panic!("unexpected block statement: {other:?}"),
                }
            }
            Rule::expr | Rule::prefix => {
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

fn parse_if_expr(pair: Pair<'_, Rule>, span: Span) -> Expr {
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
                Rule::expr | Rule::prefix => else_body = Some(Box::new(parse_expr(part))),
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
                            name: "True".to_owned(),
                            fields: vec![],
                        },
                        body: then_body,
                    },
                    MatchArm {
                        pattern: Pattern::Constructor {
                            name: "False".to_owned(),
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

fn parse_fold_expr(pair: Pair<'_, Rule>, span: Span) -> Expr {
    let mut inner = pair.into_inner();
    let scrutinee = parse_expr(inner.next().unwrap());
    let arms: Vec<MatchArm> = inner.map(parse_match_arm).collect();
    Expr::new(
        ExprKind::Fold {
            expr: Box::new(scrutinee),
            arms,
        },
        span,
    )
}

fn parse_match_arm(pair: Pair<'_, Rule>) -> MatchArm {
    let mut inner = pair.into_inner();
    let pattern = parse_pattern(inner.next().unwrap());
    let body = parse_expr(inner.next().unwrap());
    MatchArm { pattern, body }
}

fn parse_lambda(pair: Pair<'_, Rule>, span: Span) -> Expr {
    let mut inner: Vec<Pair<'_, Rule>> = pair.into_inner().collect();
    let body = parse_expr(inner.pop().unwrap());
    let params: Vec<String> = inner
        .into_iter()
        .filter(|p| p.as_rule() == Rule::lambda_param)
        .map(|p| p.as_str().to_owned())
        .collect();
    Expr::new(
        ExprKind::Lambda {
            params,
            body: Box::new(body),
        },
        span,
    )
}

fn parse_record_literal(pair: Pair<'_, Rule>, span: Span) -> Expr {
    let fields: Vec<(String, Expr)> = pair
        .into_inner()
        .map(|fi| {
            let mut inner = fi.into_inner();
            let name = inner.next().unwrap().as_str().to_owned();
            let val = parse_expr(inner.next().unwrap());
            (name, val)
        })
        .collect();
    Expr::new(ExprKind::Record { fields }, span)
}

fn parse_irrefutable(pair: Pair<'_, Rule>) -> Pattern {
    let text = pair.as_str().trim();
    if text == "_" {
        return Pattern::Wildcard;
    }
    let inner: Vec<Pair<'_, Rule>> = pair.into_inner().collect();
    if inner.is_empty() {
        // bare ident or _
        if text == "_" {
            return Pattern::Wildcard;
        }
        return Pattern::Binding(text.to_owned());
    }
    if inner.len() == 1 && inner[0].as_rule() == Rule::ident {
        return Pattern::Binding(inner[0].as_str().to_owned());
    }
    // Tuple pattern: all children are irrefutable
    let sub_pats: Vec<Pattern> = inner
        .into_iter()
        .filter(|p| p.as_rule() == Rule::irrefutable)
        .map(parse_irrefutable)
        .collect();
    Pattern::Tuple(sub_pats)
}

fn parse_tuple(pair: Pair<'_, Rule>, span: Span) -> Expr {
    let elements: Vec<Expr> = pair.into_inner().map(parse_expr).collect();
    Expr::new(ExprKind::Tuple(elements), span)
}

// ---- Patterns ----

fn parse_pattern(pair: Pair<'_, Rule>) -> Pattern {
    let text = pair.as_str().trim();
    let inner: Vec<Pair<'_, Rule>> = pair.into_inner().collect();

    if inner.is_empty() {
        // Literal `_` wildcard (no inner pairs)
        if text == "_" {
            return Pattern::Wildcard;
        }
        panic!("empty pattern: '{text}'");
    }

    let first = &inner[0];
    match first.as_rule() {
        Rule::constructor => {
            let name = first.as_str().to_owned();
            let fields: Vec<Pattern> = inner.into_iter().skip(1).map(parse_pattern).collect();
            Pattern::Constructor { name, fields }
        }
        Rule::field_pattern => {
            let fields: Vec<(String, Pattern)> =
                inner.into_iter().map(parse_field_pattern).collect();
            Pattern::Record { fields }
        }
        Rule::pattern => {
            // Tuple pattern: all children are sub-patterns
            let elements: Vec<Pattern> = inner.into_iter().map(parse_pattern).collect();
            Pattern::Tuple(elements)
        }
        Rule::ident => {
            let name = first.as_str();
            if name == "_" {
                Pattern::Wildcard
            } else {
                Pattern::Binding(name.to_owned())
            }
        }
        _ => {
            let first_text = first.as_str();
            if first_text == "_" {
                Pattern::Wildcard
            } else {
                panic!("unexpected pattern: {first_text}");
            }
        }
    }
}

fn parse_field_pattern(pair: Pair<'_, Rule>) -> (String, Pattern) {
    let mut inner = pair.into_inner();
    let name = inner.next().unwrap().as_str().to_owned();
    if let Some(pat) = inner.next() {
        (name, parse_pattern(pat))
    } else {
        (name.clone(), Pattern::Binding(name))
    }
}
