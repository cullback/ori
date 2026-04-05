use crate::ast::{BinOp, Decl, Expr, Module, Stmt, TypeExpr};
use crate::token::Token;

pub fn parse(tokens: Vec<Token>) -> Module {
    let mut parser = Parser { tokens, pos: 0 };
    parser.parse_module()
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

#[expect(
    clippy::arithmetic_side_effects,
    reason = "position arithmetic in parser is bounds-checked"
)]
impl Parser {
    fn peek(&self) -> &Token {
        &self.tokens[self.pos]
    }

    fn peek_at(&self, offset: usize) -> &Token {
        let idx = self.pos + offset;
        if idx < self.tokens.len() {
            &self.tokens[idx]
        } else {
            &Token::Eof
        }
    }

    fn advance(&mut self) -> Token {
        let tok = self.tokens[self.pos].clone();
        self.pos += 1;
        tok
    }

    fn expect(&mut self, expected: &Token) {
        let tok = self.advance();
        assert!(tok == *expected, "expected {expected:?}, got {tok:?}");
    }

    fn skip_newlines(&mut self) {
        while *self.peek() == Token::Newline {
            self.advance();
        }
    }

    fn parse_module(&mut self) -> Module {
        let mut decls = Vec::new();
        self.skip_newlines();

        while *self.peek() != Token::Eof {
            decls.push(self.parse_decl());
            self.skip_newlines();
        }

        Module { decls }
    }

    fn parse_decl(&mut self) -> Decl {
        // Lookahead: Ident Colon → type annotation, Ident Eq → func def
        let Token::Ident(name) = self.peek().clone() else {
            panic!(
                "expected identifier at start of declaration, got {:?}",
                self.peek()
            );
        };

        match self.peek_at(1) {
            Token::Colon => self.parse_type_anno(),
            Token::Eq => self.parse_func_def(),
            other => panic!("expected ':' or '=' after '{name}', got {other:?}"),
        }
    }

    fn parse_type_anno(&mut self) -> Decl {
        let Token::Ident(name) = self.advance() else {
            panic!("expected identifier")
        };
        self.expect(&Token::Colon);
        let ty = self.parse_type_expr();
        self.skip_newlines();
        Decl::TypeAnno { name, ty }
    }

    fn parse_type_expr(&mut self) -> TypeExpr {
        let Token::Ident(name) = self.advance() else {
            panic!("expected type name, got {:?}", self.tokens[self.pos - 1]);
        };
        TypeExpr::Named(name)
    }

    fn parse_func_def(&mut self) -> Decl {
        let Token::Ident(name) = self.advance() else {
            panic!("expected identifier")
        };
        self.expect(&Token::Eq);
        self.skip_newlines();

        // Check for lambda: |params| body
        if *self.peek() == Token::Pipe {
            self.advance(); // consume |
            let mut params = Vec::new();
            if *self.peek() != Token::Pipe {
                loop {
                    let Token::Ident(param) = self.advance() else {
                        panic!(
                            "expected parameter name, got {:?}",
                            self.tokens[self.pos - 1]
                        );
                    };
                    params.push(param);
                    if *self.peek() == Token::Pipe {
                        break;
                    }
                    self.expect(&Token::Comma);
                }
            }
            self.expect(&Token::Pipe);
            self.skip_newlines();
            let body = self.parse_expr();
            self.skip_newlines();
            Decl::FuncDef { name, params, body }
        } else {
            // Constant: name = expr
            let body = self.parse_expr();
            self.skip_newlines();
            Decl::FuncDef {
                name,
                params: vec![],
                body,
            }
        }
    }

    fn parse_expr(&mut self) -> Expr {
        self.parse_expr_bp(0)
    }

    fn parse_expr_bp(&mut self, min_bp: u8) -> Expr {
        let mut lhs = self.parse_prefix();

        loop {
            let Some((l_bp, r_bp, op)) = self.infix_bp() else {
                break;
            };
            if l_bp < min_bp {
                break;
            }
            self.advance(); // consume operator
            let rhs = self.parse_expr_bp(r_bp);
            lhs = Expr::BinOp {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
        }

        lhs
    }

    fn parse_prefix(&mut self) -> Expr {
        match self.peek().clone() {
            Token::IntLit(n) => {
                self.advance();
                Expr::IntLit(n)
            }

            Token::Ident(name) => {
                self.advance();
                // Check for function call: ident(args)
                if *self.peek() == Token::LParen {
                    self.advance(); // consume (
                    let mut args = Vec::new();
                    if *self.peek() != Token::RParen {
                        args.push(self.parse_expr());
                        while *self.peek() == Token::Comma {
                            self.advance();
                            args.push(self.parse_expr());
                        }
                    }
                    self.expect(&Token::RParen);
                    Expr::Call { func: name, args }
                } else {
                    Expr::Var(name)
                }
            }

            Token::LParen => {
                self.advance(); // consume (
                self.parse_block()
            }

            Token::Minus => {
                self.advance();
                let operand = self.parse_prefix();
                // Desugar -x as 0 - x
                Expr::BinOp {
                    op: BinOp::Sub,
                    lhs: Box::new(Expr::IntLit(0)),
                    rhs: Box::new(operand),
                }
            }

            other => panic!("expected expression, got {other:?}"),
        }
    }

    fn parse_block(&mut self) -> Expr {
        self.skip_newlines();
        let mut stmts = Vec::new();

        loop {
            // Check if this is a let statement: Ident Eq (not EqEq)
            if let Token::Ident(_) = self.peek()
                && *self.peek_at(1) == Token::Eq
            {
                let Token::Ident(name) = self.advance() else {
                    panic!("expected identifier")
                };
                self.expect(&Token::Eq);
                let val = self.parse_expr();
                stmts.push(Stmt::Let { name, val });
                self.skip_newlines();
                continue;
            }
            // Not a let statement — this must be the final expression
            break;
        }

        let result = self.parse_expr();
        self.skip_newlines();
        self.expect(&Token::RParen);

        if stmts.is_empty() {
            // Parenthesized expression, not a block
            result
        } else {
            Expr::Block(stmts, Box::new(result))
        }
    }

    fn infix_bp(&self) -> Option<(u8, u8, BinOp)> {
        match self.peek() {
            Token::EqEq => Some((3, 4, BinOp::Eq)),
            Token::BangEq => Some((3, 4, BinOp::Neq)),
            Token::Plus => Some((5, 6, BinOp::Add)),
            Token::Minus => Some((5, 6, BinOp::Sub)),
            Token::Star => Some((7, 8, BinOp::Mul)),
            Token::Slash => Some((7, 8, BinOp::Div)),
            Token::Percent => Some((7, 8, BinOp::Rem)),
            _ => None,
        }
    }
}
