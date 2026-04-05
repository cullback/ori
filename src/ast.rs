#[derive(Debug)]
pub struct Module {
    pub decls: Vec<Decl>,
}

#[derive(Debug)]
#[expect(dead_code, reason = "TypeAnno parsed but not used until type checker")]
pub enum Decl {
    TypeAnno {
        name: String,
        ty: TypeExpr,
    },
    FuncDef {
        name: String,
        params: Vec<String>,
        body: Expr,
    },
}

#[derive(Debug)]
#[expect(dead_code, reason = "parsed but not used until type checker")]
pub enum TypeExpr {
    Named(String),
}

#[derive(Debug)]
pub enum Expr {
    IntLit(i64),
    Var(String),
    BinOp {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Call {
        func: String,
        args: Vec<Expr>,
    },
    Block(Vec<Stmt>, Box<Expr>),
}

#[derive(Debug)]
pub enum Stmt {
    Let { name: String, val: Expr },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Neq,
}
