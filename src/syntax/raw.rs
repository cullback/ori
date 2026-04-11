use crate::source::FileId;

#[derive(Debug, Clone)]
pub struct Module<'src> {
    pub exports: Vec<&'src str>,
    pub imports: Vec<Import<'src>>,
    pub decls: Vec<Decl<'src>>,
}

#[derive(Debug, Clone)]
pub struct Import<'src> {
    pub module: &'src str,
    pub exposing: Vec<&'src str>,
}

/// Constraint declaration in a `where` clause: `a.method` or `a.method : type`
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct ConstraintDecl<'src> {
    pub type_var: &'src str,
    pub method: &'src str,
    pub method_type: Option<TypeExpr<'src>>,
}

/// How a type was declared: alias (`:`), transparent nominal (`:=`), or opaque (`::`)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeDeclKind {
    /// `:` — just a name for an existing type, no distinct type, no `.()` block.
    Alias,
    /// `:=` — distinct type, internals visible everywhere, `.()` block allowed.
    Transparent,
    /// `::` — distinct type, internals hidden outside `.()` block.
    Opaque,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum Decl<'src> {
    TypeAnno {
        span: Span,
        name: &'src str,
        type_params: Vec<&'src str>,
        ty: TypeExpr<'src>,
        where_clause: Vec<ConstraintDecl<'src>>,
        methods: Vec<Decl<'src>>,
        kind: TypeDeclKind,
        doc: Option<String>,
    },
    FuncDef {
        span: Span,
        name: &'src str,
        params: Vec<&'src str>,
        body: Expr<'src>,
        doc: Option<String>,
    },
}

impl Decl<'_> {
    #[allow(
        dead_code,
        reason = "used by snapshot tests; later passes will use non-test"
    )]
    pub const fn span(&self) -> Span {
        match self {
            Self::TypeAnno { span, .. } | Self::FuncDef { span, .. } => *span,
        }
    }
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

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct Span {
    pub file: FileId,
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
    FloatLit(f64),
    StrLit(Vec<u8>),
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
        segments: Vec<&'src str>,
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
    ListLit(Vec<Expr<'src>>),
    MethodCall {
        receiver: Box<Expr<'src>>,
        method: &'src str,
        args: Vec<Expr<'src>>,
    },
    Is {
        expr: Box<Expr<'src>>,
        pattern: Pattern<'src>,
    },
}

#[derive(Debug, Clone)]
pub struct MatchArm<'src> {
    pub pattern: Pattern<'src>,
    pub guards: Vec<Expr<'src>>,
    pub body: Expr<'src>,
    pub is_return: bool,
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
    /// Guard clause: `if condition return value`
    /// If condition is true, return value from the enclosing function.
    Guard {
        condition: Expr<'src>,
        return_val: Expr<'src>,
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
    And,
    Or,
}

// Pattern utilities and free-variable collection live on `ast::Pattern`
// and `ast::free_names` now that all passes operate on `ast::Module`.
// The raw form only exists briefly between parse and resolve.
