#[derive(Debug, Clone)]
pub struct Module<'src> {
    pub imports: Vec<&'src str>,
    pub decls: Vec<Decl<'src>>,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum Decl<'src> {
    TypeAnno {
        name: &'src str,
        type_params: Vec<&'src str>,
        ty: TypeExpr<'src>,
        methods: Vec<Decl<'src>>,
    },
    FuncDef {
        name: &'src str,
        params: Vec<&'src str>,
        body: Expr<'src>,
    },
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum TypeExpr<'src> {
    Named(&'src str),
    App(&'src str, Vec<TypeExpr<'src>>),
    TagUnion(Vec<TagDecl<'src>>),
    Arrow(Vec<TypeExpr<'src>>, Box<TypeExpr<'src>>),
    Record(Vec<(&'src str, TypeExpr<'src>)>),
    Tuple(Vec<TypeExpr<'src>>),
}

#[derive(Debug, Clone)]
pub struct TagDecl<'src> {
    pub name: &'src str,
    pub fields: Vec<TypeExpr<'src>>,
}

#[derive(Debug, Clone, Copy, Default)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone)]
pub struct Expr<'src> {
    pub kind: ExprKind<'src>,
    pub span: Span,
}

impl<'src> Expr<'src> {
    pub const fn new(kind: ExprKind<'src>, span: Span) -> Self {
        Self { kind, span }
    }
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum ExprKind<'src> {
    IntLit(i64),
    Name(&'src str),
    BinOp {
        op: BinOp,
        lhs: Box<Expr<'src>>,
        rhs: Box<Expr<'src>>,
    },
    Call {
        func: &'src str,
        args: Vec<Expr<'src>>,
    },
    Block(Vec<Stmt<'src>>, Box<Expr<'src>>),
    If {
        expr: Box<Expr<'src>>,
        arms: Vec<MatchArm<'src>>,
        #[allow(dead_code)]
        else_body: Option<Box<Expr<'src>>>,
    },
    Fold {
        expr: Box<Expr<'src>>,
        arms: Vec<MatchArm<'src>>,
    },
    Lambda {
        params: Vec<&'src str>,
        body: Box<Expr<'src>>,
    },
    QualifiedCall {
        owner: &'src str,
        method: &'src str,
        args: Vec<Expr<'src>>,
    },
    Record {
        fields: Vec<(&'src str, Expr<'src>)>,
    },
    FieldAccess {
        record: Box<Expr<'src>>,
        field: &'src str,
    },
    Tuple(Vec<Expr<'src>>),
}

#[derive(Debug, Clone)]
pub struct MatchArm<'src> {
    pub pattern: Pattern<'src>,
    pub body: Expr<'src>,
}

#[derive(Debug, Clone)]
pub enum Pattern<'src> {
    Constructor {
        name: &'src str,
        fields: Vec<Pattern<'src>>,
    },
    Record {
        fields: Vec<(&'src str, Pattern<'src>)>,
    },
    Tuple(Vec<Pattern<'src>>),
    Wildcard,
    Binding(&'src str),
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum Stmt<'src> {
    Let {
        name: &'src str,
        val: Expr<'src>,
    },
    TypeHint {
        name: &'src str,
        ty: TypeExpr<'src>,
    },
    Destructure {
        pattern: Pattern<'src>,
        val: Expr<'src>,
    },
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
