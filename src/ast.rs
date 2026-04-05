#[derive(Debug)]
pub struct Module {
    pub decls: Vec<Decl>,
}

#[derive(Debug)]
#[allow(dead_code)]
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
#[allow(dead_code)]
pub enum TypeExpr {
    Named(String),
    TagUnion(Vec<TagDecl>),
    Arrow(Vec<TypeExpr>, Box<TypeExpr>),
}

#[derive(Debug)]
pub struct TagDecl {
    pub name: String,
    pub fields: Vec<TypeExpr>,
}

#[derive(Debug)]
pub enum Expr {
    IntLit(i64),
    Name(String),
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
    If {
        expr: Box<Expr>,
        arms: Vec<MatchArm>,
        #[allow(dead_code)]
        else_body: Option<Box<Expr>>,
    },
}

#[derive(Debug)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
}

#[derive(Debug)]
pub enum Pattern {
    Constructor { name: String, fields: Vec<Pattern> },
    Wildcard,
    Binding(String),
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
