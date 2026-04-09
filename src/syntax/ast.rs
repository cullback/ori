use std::collections::HashSet;

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

// ---- Pattern utilities ----

impl<'src> Pattern<'src> {
    /// Add all binding names introduced by this pattern to `bound`.
    pub fn bind_names(&self, bound: &mut HashSet<&'src str>) {
        match self {
            Pattern::Constructor { fields, .. } => {
                for f in fields {
                    f.bind_names(bound);
                }
            }
            Pattern::Record { fields } => {
                for (_, pat) in fields {
                    pat.bind_names(bound);
                }
            }
            Pattern::Tuple(elems) => {
                for e in elems {
                    e.bind_names(bound);
                }
            }
            Pattern::Binding(name) => {
                bound.insert(name);
            }
            Pattern::Wildcard => {}
        }
    }
}

// ---- Free variable collection ----

/// Collect free variable names in `expr`, respecting lexical scope.
///
/// A name is "free" if it's not in `bound`, `is_known` returns false,
/// and it hasn't already been added to `seen`. New names are added to
/// `seen` for dedup across calls.
pub fn free_names<'src>(
    expr: &Expr<'src>,
    bound: &HashSet<&'src str>,
    seen: &mut HashSet<&'src str>,
    is_known: &impl Fn(&str) -> bool,
) -> Vec<&'src str> {
    let mut out = Vec::new();
    free_names_inner(expr, bound, seen, is_known, &mut out);
    out
}

fn free_names_inner<'src>(
    expr: &Expr<'src>,
    bound: &HashSet<&'src str>,
    seen: &mut HashSet<&'src str>,
    is_known: &impl Fn(&str) -> bool,
    out: &mut Vec<&'src str>,
) {
    let check = |name: &'src str, seen: &mut HashSet<&'src str>, out: &mut Vec<&'src str>| {
        if !bound.contains(name) && !is_known(name) && seen.insert(name) {
            out.push(name);
        }
    };

    match &expr.kind {
        ExprKind::Name(name) => check(name, seen, out),
        ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) => {}
        ExprKind::BinOp { lhs, rhs, .. } => {
            free_names_inner(lhs, bound, seen, is_known, out);
            free_names_inner(rhs, bound, seen, is_known, out);
        }
        ExprKind::Call { func, args } => {
            check(func, seen, out);
            for a in args {
                free_names_inner(a, bound, seen, is_known, out);
            }
        }
        ExprKind::QualifiedCall { args, .. } => {
            for a in args {
                free_names_inner(a, bound, seen, is_known, out);
            }
        }
        ExprKind::Block(stmts, result) => {
            let mut inner = bound.clone();
            for stmt in stmts {
                match stmt {
                    Stmt::Let { name, val } => {
                        free_names_inner(val, &inner, seen, is_known, out);
                        inner.insert(name);
                    }
                    Stmt::Destructure { pattern, val } => {
                        free_names_inner(val, &inner, seen, is_known, out);
                        pattern.bind_names(&mut inner);
                    }
                    Stmt::Guard {
                        condition,
                        return_val,
                    } => {
                        free_names_inner(condition, &inner, seen, is_known, out);
                        free_names_inner(return_val, &inner, seen, is_known, out);
                    }
                    Stmt::TypeHint { .. } => {}
                }
            }
            free_names_inner(result, &inner, seen, is_known, out);
        }
        ExprKind::If {
            expr: scrutinee,
            arms,
            else_body,
        } => {
            free_names_inner(scrutinee, bound, seen, is_known, out);
            for arm in arms {
                let mut arm_bound = bound.clone();
                arm.pattern.bind_names(&mut arm_bound);
                for guard_expr in &arm.guards {
                    free_names_inner(guard_expr, &arm_bound, seen, is_known, out);
                }
                free_names_inner(&arm.body, &arm_bound, seen, is_known, out);
            }
            if let Some(eb) = else_body {
                free_names_inner(eb, bound, seen, is_known, out);
            }
        }
        ExprKind::Fold {
            expr: scrutinee,
            arms,
        } => {
            free_names_inner(scrutinee, bound, seen, is_known, out);
            for arm in arms {
                let mut arm_bound = bound.clone();
                arm.pattern.bind_names(&mut arm_bound);
                for guard_expr in &arm.guards {
                    free_names_inner(guard_expr, &arm_bound, seen, is_known, out);
                }
                free_names_inner(&arm.body, &arm_bound, seen, is_known, out);
            }
        }
        ExprKind::Record { fields } => {
            for (_, e) in fields {
                free_names_inner(e, bound, seen, is_known, out);
            }
        }
        ExprKind::FieldAccess { record, .. } => {
            free_names_inner(record, bound, seen, is_known, out);
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            free_names_inner(receiver, bound, seen, is_known, out);
            for a in args {
                free_names_inner(a, bound, seen, is_known, out);
            }
        }
        ExprKind::Lambda { params, body } => {
            let mut inner = bound.clone();
            for p in params {
                inner.insert(p);
            }
            free_names_inner(body, &inner, seen, is_known, out);
        }
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems {
                free_names_inner(e, bound, seen, is_known, out);
            }
        }
        ExprKind::Is { expr: inner, .. } => {
            free_names_inner(inner, bound, seen, is_known, out);
        }
    }
}
