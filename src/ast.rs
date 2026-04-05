#[derive(Debug, Clone)]
pub struct Module {
    pub decls: Vec<Decl>,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum Decl {
    TypeAnno {
        name: String,
        type_params: Vec<String>,
        ty: TypeExpr,
        methods: Vec<Decl>,
    },
    FuncDef {
        name: String,
        params: Vec<String>,
        body: Expr,
    },
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum TypeExpr {
    Named(String),
    App(String, Vec<TypeExpr>),
    TagUnion(Vec<TagDecl>),
    Arrow(Vec<TypeExpr>, Box<TypeExpr>),
    Record(Vec<(String, TypeExpr)>),
}

#[derive(Debug, Clone)]
pub struct TagDecl {
    pub name: String,
    pub fields: Vec<TypeExpr>,
}

#[derive(Debug, Clone)]
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
    Fold {
        expr: Box<Expr>,
        arms: Vec<MatchArm>,
    },
    Lambda {
        params: Vec<String>,
        body: Box<Expr>,
    },
    QualifiedCall {
        owner: String,
        method: String,
        args: Vec<Expr>,
    },
    Record {
        fields: Vec<(String, Expr)>,
    },
    FieldAccess {
        record: Box<Expr>,
        field: String,
    },
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub enum Pattern {
    Constructor { name: String, fields: Vec<Pattern> },
    Record { fields: Vec<(String, Pattern)> },
    Wildcard,
    Binding(String),
}

#[derive(Debug, Clone)]
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
