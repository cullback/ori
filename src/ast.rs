//! Elaborated AST — consumed by every pass after `resolve`.
//!
//! Step 6b pushes [`SymbolId`] down into every binding site and every
//! name reference. Every function/method parameter, `let`-bound name,
//! lambda parameter, pattern binding, and `Name` reference carries a
//! stable [`SymbolId`] allocated during [`from_raw`]. Free function
//! calls also resolve to a [`SymbolId`] at that time, so later passes
//! never need to key off source strings for local lookups.
//!
//! Field names (`FieldAccess`, `Record`, `Pattern::Record`) still live
//! as borrowed `&'src str` — they become an interned `FieldSym` in
//! Step 6c.
//!
//! Conversion from `raw::Module` to `ast::Module` happens in
//! [`from_raw`], called at the end of `resolve_imports`. It walks the
//! raw AST with a scope stack (see [`Resolver`]), allocating fresh
//! [`SymbolId`]s for binding sites and rewriting every reference to
//! the [`SymbolId`] of its binding. `Span` is re-exported from
//! `syntax::raw` because it carries no borrowed strings.

use std::collections::{HashMap, HashSet};

use crate::symbol::{FieldInterner, FieldSym, SymbolId, SymbolKind, SymbolTable};
use crate::syntax::raw;
pub use crate::syntax::raw::Span;
use crate::types::engine::{Type, TypeVar};

// ---- Module ----

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

// ---- Declarations ----

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum Decl<'src> {
    TypeAnno {
        span: Span,
        /// Stable symbol identifier. Display name lives in `SymbolTable`.
        name: SymbolId,
        type_params: Vec<&'src str>,
        ty: TypeExpr<'src>,
        where_clause: Vec<ConstraintDecl<'src>>,
        methods: Vec<Decl<'src>>,
        kind: TypeDeclKind,
        doc: Option<String>,
    },
    FuncDef {
        span: Span,
        name: SymbolId,
        params: Vec<SymbolId>,
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

    #[allow(dead_code, reason = "used by topo, fold_lift, and later passes")]
    pub const fn name(&self) -> SymbolId {
        match self {
            Self::TypeAnno { name, .. } | Self::FuncDef { name, .. } => *name,
        }
    }
}

// ---- Type expressions ----

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum TypeExpr<'src> {
    Named(&'src str),
    App(&'src str, Vec<TypeExpr<'src>>),
    /// Tag union annotation. The trailing `bool` is `true` when the
    /// annotation ends with `..` (open row), `false` when closed.
    /// See `raw::TypeExpr::TagUnion` for the design rationale.
    TagUnion(Vec<TagDecl<'src>>, bool),
    Arrow(Vec<TypeExpr<'src>>, Box<TypeExpr<'src>>),
    Record(Vec<(FieldSym, TypeExpr<'src>)>),
    Tuple(Vec<TypeExpr<'src>>),
}

#[derive(Debug, Clone)]
pub struct TagDecl<'src> {
    pub name: &'src str,
    pub fields: Vec<TypeExpr<'src>>,
}

// ---- Expressions ----

#[derive(Debug, Clone)]
pub struct Expr<'src> {
    pub kind: ExprKind<'src>,
    pub span: Span,
    /// Placeholder until inference fills it in.
    pub ty: Type,
}

impl<'src> Expr<'src> {
    #[allow(dead_code, reason = "used by rewrite passes starting in Step 4")]
    pub const fn new(kind: ExprKind<'src>, span: Span) -> Self {
        Self {
            kind,
            span,
            ty: placeholder_type(),
        }
    }
}

/// The placeholder value used for `Expr::ty` before inference runs.
///
/// `TypeVar(0)` is a well-formed type; the engine will generate its own
/// fresh vars starting from 0 at the top of inference, which will
/// overwrite every placeholder during the final resolve walk.
const fn placeholder_type() -> Type {
    Type::Var(TypeVar(0))
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum ExprKind<'src> {
    IntLit(i64),
    FloatLit(f64),
    StrLit(Vec<u8>),
    /// Name reference. Resolved by [`from_raw`] to the `SymbolId` of
    /// its binding — either a local (let/param/pattern binding) or a
    /// top-level definition (function, constructor, type).
    Name(SymbolId),
    BinOp {
        op: BinOp,
        lhs: Box<Expr<'src>>,
        rhs: Box<Expr<'src>>,
    },
    /// Call to a function referenced by name. After [`from_raw`], the
    /// `target` is always a resolved `SymbolId` — local (higher-order
    /// variable used as a callee) or global (top-level function /
    /// constructor / method). Consumers dispatch based on the symbol's
    /// `SymbolKind`.
    Call {
        target: SymbolId,
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
        params: Vec<SymbolId>,
        body: Box<Expr<'src>>,
    },
    QualifiedCall {
        segments: Vec<&'src str>,
        args: Vec<Expr<'src>>,
        /// Mangled target name once inference resolves the call. `None`
        /// before inference runs. Still a string because methods are
        /// keyed by mangled `"Type.method"` strings in inference; migrating
        /// this to `SymbolId` is Step 7's problem when mono needs it.
        resolved: Option<String>,
    },
    Record {
        fields: Vec<(FieldSym, Expr<'src>)>,
    },
    FieldAccess {
        record: Box<Expr<'src>>,
        field: FieldSym,
    },
    Tuple(Vec<Expr<'src>>),
    ListLit(Vec<Expr<'src>>),
    MethodCall {
        receiver: Box<Expr<'src>>,
        method: &'src str,
        args: Vec<Expr<'src>>,
        /// Mangled target name once inference resolves the method. `None`
        /// before inference runs.
        resolved: Option<String>,
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
        fields: Vec<(FieldSym, Pattern<'src>)>,
    },
    Tuple(Vec<Pattern<'src>>),
    Wildcard,
    Binding(SymbolId),
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum Stmt<'src> {
    Let {
        name: SymbolId,
        val: Expr<'src>,
    },
    /// Type hint for the immediately-following `Let`. Carries the source
    /// name so inference can pair it with the `Let` by display name —
    /// the resolver doesn't bind anything for hints, since the `Let`
    /// itself introduces the `SymbolId`.
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

impl Pattern<'_> {
    /// Add every `SymbolId` introduced by this pattern to `bound`.
    pub fn bind_syms(&self, bound: &mut HashSet<SymbolId>) {
        match self {
            Pattern::Constructor { fields, .. } => {
                for f in fields {
                    f.bind_syms(bound);
                }
            }
            Pattern::Record { fields } => {
                for (_, pat) in fields {
                    pat.bind_syms(bound);
                }
            }
            Pattern::Tuple(elems) => {
                for e in elems {
                    e.bind_syms(bound);
                }
            }
            Pattern::Binding(sym) => {
                bound.insert(*sym);
            }
            Pattern::Wildcard => {}
        }
    }
}

// ---- Free variable collection ----

/// Collect free `SymbolId`s referenced in `expr`, respecting lexical scope.
///
/// A name is "free" if its `SymbolId` is not in `bound`, `is_known`
/// returns false, and it hasn't already been added to `seen`.
#[allow(dead_code, reason = "used by capture analysis in later rewrite passes")]
#[allow(clippy::impl_trait_in_params)]
pub fn free_names<F: Fn(SymbolId) -> bool>(
    expr: &Expr<'_>,
    bound: &HashSet<SymbolId>,
    seen: &mut HashSet<SymbolId>,
    is_known: &F,
) -> Vec<SymbolId> {
    let mut out = Vec::new();
    free_names_inner(expr, bound, seen, is_known, &mut out);
    out
}

#[allow(clippy::too_many_lines)]
fn free_names_inner<F: Fn(SymbolId) -> bool>(
    expr: &Expr<'_>,
    bound: &HashSet<SymbolId>,
    seen: &mut HashSet<SymbolId>,
    is_known: &F,
    out: &mut Vec<SymbolId>,
) {
    let check = |sym: SymbolId, seen: &mut HashSet<SymbolId>, out: &mut Vec<SymbolId>| {
        if !bound.contains(&sym) && !is_known(sym) && seen.insert(sym) {
            out.push(sym);
        }
    };

    match &expr.kind {
        ExprKind::Name(sym) => check(*sym, seen, out),
        ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) => {}
        ExprKind::BinOp { lhs, rhs, .. } => {
            free_names_inner(lhs, bound, seen, is_known, out);
            free_names_inner(rhs, bound, seen, is_known, out);
        }
        ExprKind::Call { target, args, .. } => {
            check(*target, seen, out);
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
                        inner.insert(*name);
                    }
                    Stmt::Destructure { pattern, val } => {
                        free_names_inner(val, &inner, seen, is_known, out);
                        pattern.bind_syms(&mut inner);
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
                arm.pattern.bind_syms(&mut arm_bound);
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
                arm.pattern.bind_syms(&mut arm_bound);
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
                inner.insert(*p);
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

// ---- Raw → elaborated conversion with name resolution ----

/// Convert a `raw::Module` (parser output) into an `ast::Module`
/// (elaborated form consumed by post-resolve passes).
///
/// Allocates a fresh [`SymbolId`] for every top-level declaration and
/// every nested method. Then walks every function body with a scope
/// stack ([`Resolver`]), allocating fresh [`SymbolId`]s for locals
/// (function parameters, `let`-bound names, lambda parameters, pattern
/// bindings) and rewriting every [`ExprKind::Name`] / [`ExprKind::Call`]
/// to carry the resolved [`SymbolId`] of its binding site. Also interns
/// every record field name seen in the AST into `fields`.
pub fn from_raw<'src>(
    module: raw::Module<'src>,
    symbols: &mut SymbolTable,
    fields: &mut FieldInterner,
) -> Module<'src> {
    // Pass 1: allocate SymbolIds for top-level decls (and TagUnion
    // constructors). Methods are allocated lazily in Pass 2 because
    // they live inside `TypeAnno.methods`.
    let mut top_level: HashMap<&'src str, SymbolId> = HashMap::new();
    for decl in &module.decls {
        match decl {
            raw::Decl::FuncDef { name, span, .. } => {
                let id = symbols.fresh(*name, *span, SymbolKind::Func);
                top_level.insert(name, id);
            }
            raw::Decl::TypeAnno { name, span, ty, .. } => {
                let id = symbols.fresh(*name, *span, SymbolKind::Type);
                top_level.insert(name, id);
                // Constructors of a tag-union also enter the top-level
                // namespace so `Call { func: "Ok" }` resolves correctly.
                if let raw::TypeExpr::TagUnion(tags, _) = ty {
                    for tag in tags {
                        let cid = symbols.fresh(tag.name, *span, SymbolKind::Constructor);
                        top_level.insert(tag.name, cid);
                    }
                }
            }
        }
    }

    // Pass 1.5: structural constructor collection. Walk every
    // expression and pattern in the module, and for every
    // uppercase-named reference that isn't already in `top_level`,
    // allocate a fresh `SymbolKind::Constructor`. This makes bare
    // references like `Red` resolvable even when no `TypeAnno`
    // declares them — the inference pass then produces an open
    // `Type::TagUnion` for them.
    collect_structural_constructors(&module, symbols, &mut top_level);

    // Pass 2: walk each decl with the resolver to fill in SymbolIds on
    // every binding site and reference. Each decl gets a fresh,
    // isolated scope stack — declarations don't share locals.
    let mut resolver = Resolver {
        symbols,
        fields,
        scope_stack: Vec::new(),
        top_level: &top_level,
    };
    let decls = module
        .decls
        .into_iter()
        .map(|d| resolver.resolve_decl(d))
        .collect();

    Module {
        exports: module.exports,
        imports: module
            .imports
            .into_iter()
            .map(|i| Import {
                module: i.module,
                exposing: i.exposing,
            })
            .collect(),
        decls,
    }
}

// ---- Structural constructor pre-pass ----

/// Check if a name looks like a constructor (starts with ASCII
/// uppercase). Mirrors `syntax::parse::is_constructor_name`.
fn is_con_name(s: &str) -> bool {
    s.starts_with(|c: char| c.is_ascii_uppercase())
}

/// Walk every expression and pattern in the module. For every
/// uppercase-named reference that isn't already bound in `top_level`,
/// allocate a fresh `SymbolKind::Constructor` and insert it. Called
/// after Pass 1 (which seeds `top_level` with declared names) and
/// before Pass 2 (which resolves references against it).
fn collect_structural_constructors<'src>(
    module: &raw::Module<'src>,
    symbols: &mut SymbolTable,
    top_level: &mut HashMap<&'src str, SymbolId>,
) {
    for decl in &module.decls {
        match decl {
            raw::Decl::FuncDef { body, span, .. } => {
                collect_in_expr(body, *span, symbols, top_level);
            }
            raw::Decl::TypeAnno {
                methods, span, ..
            } => {
                for method in methods {
                    if let raw::Decl::FuncDef { body, .. } = method {
                        collect_in_expr(body, *span, symbols, top_level);
                    }
                }
            }
        }
    }
}

fn maybe_register<'src>(
    name: &'src str,
    span: raw::Span,
    symbols: &mut SymbolTable,
    top_level: &mut HashMap<&'src str, SymbolId>,
) {
    if !is_con_name(name) {
        return;
    }
    if top_level.contains_key(name) {
        return;
    }
    let id = symbols.fresh(name, span, SymbolKind::Constructor);
    top_level.insert(name, id);
}

fn collect_in_expr<'src>(
    expr: &raw::Expr<'src>,
    span: raw::Span,
    symbols: &mut SymbolTable,
    top_level: &mut HashMap<&'src str, SymbolId>,
) {
    match &expr.kind {
        raw::ExprKind::IntLit(_)
        | raw::ExprKind::FloatLit(_)
        | raw::ExprKind::StrLit(_) => {}
        raw::ExprKind::Name(name) => {
            maybe_register(name, span, symbols, top_level);
        }
        raw::ExprKind::BinOp { lhs, rhs, .. } => {
            collect_in_expr(lhs, span, symbols, top_level);
            collect_in_expr(rhs, span, symbols, top_level);
        }
        raw::ExprKind::Call { func, args } => {
            maybe_register(func, span, symbols, top_level);
            for a in args {
                collect_in_expr(a, span, symbols, top_level);
            }
        }
        raw::ExprKind::QualifiedCall { args, .. } => {
            // Qualified calls like `Module.func(...)` never introduce
            // a bare structural constructor — the segments are a
            // module path, not a tag name.
            for a in args {
                collect_in_expr(a, span, symbols, top_level);
            }
        }
        raw::ExprKind::Block(stmts, result) => {
            for stmt in stmts {
                collect_in_stmt(stmt, span, symbols, top_level);
            }
            collect_in_expr(result, span, symbols, top_level);
        }
        raw::ExprKind::If {
            expr: scrutinee,
            arms,
            else_body,
        } => {
            collect_in_expr(scrutinee, span, symbols, top_level);
            for arm in arms {
                collect_in_pattern(&arm.pattern, span, symbols, top_level);
                for g in &arm.guards {
                    collect_in_expr(g, span, symbols, top_level);
                }
                collect_in_expr(&arm.body, span, symbols, top_level);
            }
            if let Some(eb) = else_body {
                collect_in_expr(eb, span, symbols, top_level);
            }
        }
        raw::ExprKind::Fold {
            expr: scrutinee,
            arms,
        } => {
            collect_in_expr(scrutinee, span, symbols, top_level);
            for arm in arms {
                collect_in_pattern(&arm.pattern, span, symbols, top_level);
                for g in &arm.guards {
                    collect_in_expr(g, span, symbols, top_level);
                }
                collect_in_expr(&arm.body, span, symbols, top_level);
            }
        }
        raw::ExprKind::Lambda { body, .. } => {
            collect_in_expr(body, span, symbols, top_level);
        }
        raw::ExprKind::Record { fields } => {
            for (_, e) in fields {
                collect_in_expr(e, span, symbols, top_level);
            }
        }
        raw::ExprKind::FieldAccess { record, .. } => {
            collect_in_expr(record, span, symbols, top_level);
        }
        raw::ExprKind::Tuple(elems) | raw::ExprKind::ListLit(elems) => {
            for e in elems {
                collect_in_expr(e, span, symbols, top_level);
            }
        }
        raw::ExprKind::MethodCall { receiver, args, .. } => {
            collect_in_expr(receiver, span, symbols, top_level);
            for a in args {
                collect_in_expr(a, span, symbols, top_level);
            }
        }
        raw::ExprKind::Is { expr: inner, pattern } => {
            collect_in_expr(inner, span, symbols, top_level);
            collect_in_pattern(pattern, span, symbols, top_level);
        }
    }
}

fn collect_in_stmt<'src>(
    stmt: &raw::Stmt<'src>,
    span: raw::Span,
    symbols: &mut SymbolTable,
    top_level: &mut HashMap<&'src str, SymbolId>,
) {
    match stmt {
        raw::Stmt::Let { val, .. } => collect_in_expr(val, span, symbols, top_level),
        raw::Stmt::Destructure { pattern, val } => {
            collect_in_pattern(pattern, span, symbols, top_level);
            collect_in_expr(val, span, symbols, top_level);
        }
        raw::Stmt::Guard {
            condition,
            return_val,
        } => {
            collect_in_expr(condition, span, symbols, top_level);
            collect_in_expr(return_val, span, symbols, top_level);
        }
        raw::Stmt::TypeHint { .. } => {}
    }
}

fn collect_in_pattern<'src>(
    pat: &raw::Pattern<'src>,
    span: raw::Span,
    symbols: &mut SymbolTable,
    top_level: &mut HashMap<&'src str, SymbolId>,
) {
    match pat {
        raw::Pattern::Constructor { name, fields } => {
            maybe_register(name, span, symbols, top_level);
            for f in fields {
                collect_in_pattern(f, span, symbols, top_level);
            }
        }
        raw::Pattern::Record { fields } => {
            for (_, f) in fields {
                collect_in_pattern(f, span, symbols, top_level);
            }
        }
        raw::Pattern::Tuple(elems) => {
            for e in elems {
                collect_in_pattern(e, span, symbols, top_level);
            }
        }
        raw::Pattern::Wildcard | raw::Pattern::Binding(_) => {}
    }
}

// ---- Resolver ----

/// Scope-tracking walk over the raw AST. Allocates fresh [`SymbolId`]s
/// for every local binding and rewrites every name reference to carry
/// the `SymbolId` of its binding site.
struct Resolver<'a, 'src> {
    symbols: &'a mut SymbolTable,
    fields: &'a mut FieldInterner,
    /// Innermost scope at the end of the vec. Each entry maps a
    /// source-level name to the `SymbolId` of its binding in that
    /// scope. Keys are owned `String`s so that `is`-bindings collected
    /// from a resolved expression (via `symbols.display(sym)`) can be
    /// inserted without lifetime gymnastics.
    scope_stack: Vec<HashMap<String, SymbolId>>,
    /// Top-level symbol table from Pass 1 of [`from_raw`]. Used as the
    /// fallback when scope lookup fails (for references to free
    /// functions, constructors, and imported names).
    top_level: &'a HashMap<&'src str, SymbolId>,
}

impl<'src> Resolver<'_, 'src> {
    fn push_scope(&mut self) {
        self.scope_stack.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.scope_stack.pop();
    }

    /// Allocate a fresh `SymbolId` with `SymbolKind::Local` and bind
    /// `name` to it in the innermost scope.
    fn bind_local(&mut self, name: &str, span: Span) -> SymbolId {
        let id = self.symbols.fresh(name, span, SymbolKind::Local);
        self.scope_stack
            .last_mut()
            .expect("bind_local called with empty scope stack")
            .insert(name.to_owned(), id);
        id
    }

    /// Insert a pre-allocated `(name, sym)` pair into the innermost
    /// scope. Used when an `is`-binding from a resolved subexpression
    /// needs to flow into a new scope (see `resolve_if_arms` and the
    /// `And`/`Guard` branches).
    fn insert_local(&mut self, name: String, sym: SymbolId) {
        self.scope_stack
            .last_mut()
            .expect("insert_local called with empty scope stack")
            .insert(name, sym);
    }

    /// Look up `name` in the innermost-first scope stack, then in the
    /// top-level table. Returns `None` if nothing matches.
    fn lookup(&self, name: &str) -> Option<SymbolId> {
        for scope in self.scope_stack.iter().rev() {
            if let Some(&id) = scope.get(name) {
                return Some(id);
            }
        }
        self.top_level.get(name).copied()
    }

    /// Resolve a reference. If nothing is in scope or at the top level,
    /// mint a placeholder `SymbolId` so the AST stays well-formed —
    /// inference will still report "undefined name" when it can't find
    /// a scheme for it.
    fn resolve_ref(&mut self, name: &'src str, span: Span) -> SymbolId {
        if let Some(id) = self.lookup(name) {
            id
        } else {
            self.symbols.fresh(name, span, SymbolKind::Local)
        }
    }

    // ---- Decl resolution ----

    fn resolve_decl(&mut self, decl: raw::Decl<'src>) -> Decl<'src> {
        match decl {
            raw::Decl::TypeAnno {
                span,
                name,
                type_params,
                ty,
                where_clause,
                methods,
                kind,
                doc,
            } => {
                let sym = self.top_level[name];
                let new_methods = methods
                    .into_iter()
                    .map(|m| self.resolve_method_decl(m))
                    .collect();
                Decl::TypeAnno {
                    span,
                    name: sym,
                    type_params,
                    ty: self.type_expr(ty),
                    where_clause: where_clause
                        .into_iter()
                        .map(|c| self.constraint(c))
                        .collect(),
                    methods: new_methods,
                    kind: type_decl_kind_from_raw(kind),
                    doc,
                }
            }
            raw::Decl::FuncDef {
                span,
                name,
                params,
                body,
                doc,
            } => {
                let sym = self.top_level[name];
                // Fresh scope for this function's parameters and body.
                self.push_scope();
                let param_syms: Vec<SymbolId> = params
                    .iter()
                    .map(|p| self.bind_local(p, span))
                    .collect();
                let body = self.resolve_expr(body);
                self.pop_scope();
                Decl::FuncDef {
                    span,
                    name: sym,
                    params: param_syms,
                    body,
                    doc,
                }
            }
        }
    }

    /// Methods live inside `TypeAnno.methods` and need their own
    /// `SymbolId` allocated here (they aren't in the top-level table).
    fn resolve_method_decl(&mut self, decl: raw::Decl<'src>) -> Decl<'src> {
        match decl {
            raw::Decl::FuncDef {
                span,
                name,
                params,
                body,
                doc,
            } => {
                let sym = self.symbols.fresh(name, span, SymbolKind::Method);
                self.push_scope();
                let param_syms: Vec<SymbolId> = params
                    .iter()
                    .map(|p| self.bind_local(p, span))
                    .collect();
                let body = self.resolve_expr(body);
                self.pop_scope();
                Decl::FuncDef {
                    span,
                    name: sym,
                    params: param_syms,
                    body,
                    doc,
                }
            }
            raw::Decl::TypeAnno {
                span,
                name,
                type_params,
                ty,
                where_clause,
                methods,
                kind,
                doc,
            } => {
                let sym = self.symbols.fresh(name, span, SymbolKind::Method);
                let new_methods = methods
                    .into_iter()
                    .map(|m| self.resolve_method_decl(m))
                    .collect();
                Decl::TypeAnno {
                    span,
                    name: sym,
                    type_params,
                    ty: self.type_expr(ty),
                    where_clause: where_clause
                        .into_iter()
                        .map(|c| self.constraint(c))
                        .collect(),
                    methods: new_methods,
                    kind: type_decl_kind_from_raw(kind),
                    doc,
                }
            }
        }
    }

    // ---- Expression resolution ----

    fn resolve_expr(&mut self, expr: raw::Expr<'src>) -> Expr<'src> {
        let span = expr.span;
        let kind = self.resolve_expr_kind(expr.kind, span);
        Expr {
            kind,
            span,
            ty: placeholder_type(),
        }
    }

    #[allow(clippy::too_many_lines)]
    fn resolve_expr_kind(&mut self, kind: raw::ExprKind<'src>, span: Span) -> ExprKind<'src> {
        match kind {
            raw::ExprKind::IntLit(n) => ExprKind::IntLit(n),
            raw::ExprKind::FloatLit(n) => ExprKind::FloatLit(n),
            raw::ExprKind::StrLit(bytes) => ExprKind::StrLit(bytes),
            raw::ExprKind::Name(name) => ExprKind::Name(self.resolve_ref(name, span)),
            raw::ExprKind::BinOp {
                op: raw::BinOp::And,
                lhs,
                rhs,
            } => {
                // `a and b`: any `is`-bindings introduced by `a` must be
                // in scope when resolving `b`. Resolve `a` first, walk
                // the resolved expression to find the pattern bindings,
                // then push a fresh scope with those bindings before
                // resolving `b`.
                let lhs_resolved = self.resolve_expr(*lhs);
                let mut is_binds: Vec<(String, SymbolId)> = Vec::new();
                collect_is_bindings(&lhs_resolved, self.symbols, &mut is_binds);
                self.push_scope();
                for (name, sym) in is_binds {
                    self.insert_local(name, sym);
                }
                let rhs_resolved = self.resolve_expr(*rhs);
                self.pop_scope();
                ExprKind::BinOp {
                    op: BinOp::And,
                    lhs: Box::new(lhs_resolved),
                    rhs: Box::new(rhs_resolved),
                }
            }
            raw::ExprKind::BinOp { op, lhs, rhs } => ExprKind::BinOp {
                op: bin_op_from_raw(op),
                lhs: Box::new(self.resolve_expr(*lhs)),
                rhs: Box::new(self.resolve_expr(*rhs)),
            },
            raw::ExprKind::Call { func, args } => {
                let target = self.resolve_ref(func, span);
                ExprKind::Call {
                    target,
                    args: args.into_iter().map(|a| self.resolve_expr(a)).collect(),
                }
            }
            raw::ExprKind::Block(stmts, result) => {
                self.push_scope();
                let new_stmts = stmts
                    .into_iter()
                    .map(|s| self.resolve_stmt(s))
                    .collect::<Vec<_>>();
                let new_result = Box::new(self.resolve_expr(*result));
                self.pop_scope();
                ExprKind::Block(new_stmts, new_result)
            }
            raw::ExprKind::If {
                expr,
                arms,
                else_body,
            } => {
                let scrutinee = Box::new(self.resolve_expr(*expr));
                let new_arms = self.resolve_if_arms(&scrutinee, arms);
                let new_else = else_body.map(|e| Box::new(self.resolve_expr(*e)));
                ExprKind::If {
                    expr: scrutinee,
                    arms: new_arms,
                    else_body: new_else,
                }
            }
            raw::ExprKind::Fold { expr, arms } => {
                let scrutinee = Box::new(self.resolve_expr(*expr));
                let new_arms = arms.into_iter().map(|a| self.resolve_arm(a)).collect();
                ExprKind::Fold {
                    expr: scrutinee,
                    arms: new_arms,
                }
            }
            raw::ExprKind::Lambda { params, body } => {
                self.push_scope();
                let param_syms: Vec<SymbolId> = params
                    .iter()
                    .map(|p| self.bind_local(p, span))
                    .collect();
                let new_body = Box::new(self.resolve_expr(*body));
                self.pop_scope();
                ExprKind::Lambda {
                    params: param_syms,
                    body: new_body,
                }
            }
            raw::ExprKind::QualifiedCall { segments, args } => ExprKind::QualifiedCall {
                segments,
                args: args.into_iter().map(|a| self.resolve_expr(a)).collect(),
                resolved: None,
            },
            raw::ExprKind::Record { fields } => ExprKind::Record {
                fields: fields
                    .into_iter()
                    .map(|(n, e)| {
                        let sym = self.fields.intern(n);
                        (sym, self.resolve_expr(e))
                    })
                    .collect(),
            },
            raw::ExprKind::FieldAccess { record, field } => ExprKind::FieldAccess {
                record: Box::new(self.resolve_expr(*record)),
                field: self.fields.intern(field),
            },
            raw::ExprKind::Tuple(elems) => {
                ExprKind::Tuple(elems.into_iter().map(|e| self.resolve_expr(e)).collect())
            }
            raw::ExprKind::ListLit(elems) => {
                ExprKind::ListLit(elems.into_iter().map(|e| self.resolve_expr(e)).collect())
            }
            raw::ExprKind::MethodCall {
                receiver,
                method,
                args,
            } => ExprKind::MethodCall {
                receiver: Box::new(self.resolve_expr(*receiver)),
                method,
                args: args.into_iter().map(|a| self.resolve_expr(a)).collect(),
                resolved: None,
            },
            raw::ExprKind::Is { expr, pattern } => {
                // Resolve the scrutinee first, then allocate SymbolIds
                // for any `Pattern::Binding` in the pattern. The
                // bindings don't enter any scope here — it's the job
                // of the enclosing `and`/`if`/`guard` to flow them
                // forward.
                let inner = Box::new(self.resolve_expr(*expr));
                let pat = self.resolve_pattern_alloc(pattern, span);
                ExprKind::Is { expr: inner, pattern: pat }
            }
        }
    }

    // ---- Statement resolution ----

    fn resolve_stmt(&mut self, stmt: raw::Stmt<'src>) -> Stmt<'src> {
        match stmt {
            raw::Stmt::Let { name, val } => {
                // Resolve `val` BEFORE binding `name` so that
                // `let x = x + 1` resolves the RHS `x` to the outer
                // binding (not the new one we're about to create).
                let val_span = val.span;
                let resolved_val = self.resolve_expr(val);
                let sym = self.bind_local(name, val_span);
                Stmt::Let {
                    name: sym,
                    val: resolved_val,
                }
            }
            raw::Stmt::TypeHint { name, ty } => Stmt::TypeHint {
                name,
                ty: self.type_expr(ty),
            },
            raw::Stmt::Destructure { pattern, val } => {
                // Same as Let: resolve RHS first, then walk the
                // pattern allocating fresh SymbolIds for every
                // `Pattern::Binding` and inserting each into the
                // enclosing block scope.
                let val_span = val.span;
                let resolved_val = self.resolve_expr(val);
                let pat = self.resolve_and_bind_pattern(pattern, val_span);
                Stmt::Destructure {
                    pattern: pat,
                    val: resolved_val,
                }
            }
            raw::Stmt::Guard {
                condition,
                return_val,
            } => {
                // `if cond return val` — any is-bindings introduced by
                // `cond` must be in scope for `val`.
                let resolved_cond = self.resolve_expr(condition);
                let mut is_binds: Vec<(String, SymbolId)> = Vec::new();
                collect_is_bindings(&resolved_cond, self.symbols, &mut is_binds);
                self.push_scope();
                for (name, sym) in is_binds {
                    self.insert_local(name, sym);
                }
                let resolved_ret = self.resolve_expr(return_val);
                self.pop_scope();
                Stmt::Guard {
                    condition: resolved_cond,
                    return_val: resolved_ret,
                }
            }
        }
    }

    // ---- Pattern resolution ----

    /// Walk a pattern, allocating fresh `SymbolId`s for every
    /// `Pattern::Binding`. Does NOT insert anything into the scope
    /// stack — the caller decides when and where the bindings become
    /// visible.
    fn resolve_pattern_alloc(
        &mut self,
        pat: raw::Pattern<'src>,
        span: Span,
    ) -> Pattern<'src> {
        match pat {
            raw::Pattern::Constructor { name, fields } => Pattern::Constructor {
                name,
                fields: fields
                    .into_iter()
                    .map(|p| self.resolve_pattern_alloc(p, span))
                    .collect(),
            },
            raw::Pattern::Record { fields } => Pattern::Record {
                fields: fields
                    .into_iter()
                    .map(|(n, p)| {
                        let sym = self.fields.intern(n);
                        (sym, self.resolve_pattern_alloc(p, span))
                    })
                    .collect(),
            },
            raw::Pattern::Tuple(elems) => Pattern::Tuple(
                elems
                    .into_iter()
                    .map(|p| self.resolve_pattern_alloc(p, span))
                    .collect(),
            ),
            raw::Pattern::Wildcard => Pattern::Wildcard,
            raw::Pattern::Binding(name) => {
                let id = self.symbols.fresh(name, span, SymbolKind::Local);
                Pattern::Binding(id)
            }
        }
    }

    // ---- If-arm resolution (scrutinee is-bindings flow into True arm) ----

    /// Resolve each arm of an `if` expression. Arms that match `True`
    /// have any `is`-bindings from the scrutinee in scope (mirror of
    /// infer's `collect_is_bindings` logic for bool ifs).
    fn resolve_if_arms(
        &mut self,
        scrutinee: &Expr<'src>,
        arms: Vec<raw::MatchArm<'src>>,
    ) -> Vec<MatchArm<'src>> {
        let mut out = Vec::with_capacity(arms.len());
        for arm in arms {
            let is_true_arm = matches!(
                &arm.pattern,
                raw::Pattern::Constructor { name: "True", .. }
            );
            if is_true_arm {
                // Collect is-bindings from the scrutinee and push them
                // into the arm's scope.
                let mut is_binds: Vec<(String, SymbolId)> = Vec::new();
                collect_is_bindings(scrutinee, self.symbols, &mut is_binds);
                self.push_scope();
                for (name, sym) in is_binds {
                    self.insert_local(name, sym);
                }
                // Pattern itself doesn't bind anything (constructor True
                // has no fields) but resolve it for consistency.
                let pat = self.resolve_pattern_alloc(arm.pattern, arm.body.span);
                let guards = arm
                    .guards
                    .into_iter()
                    .map(|g| self.resolve_expr(g))
                    .collect();
                let body = self.resolve_expr(arm.body);
                self.pop_scope();
                out.push(MatchArm {
                    pattern: pat,
                    guards,
                    body,
                    is_return: arm.is_return,
                });
            } else {
                out.push(self.resolve_arm(arm));
            }
        }
        out
    }

    /// Resolve a generic match arm (not the if-then-else True-arm
    /// case). Pattern bindings enter the arm's scope.
    fn resolve_arm(&mut self, arm: raw::MatchArm<'src>) -> MatchArm<'src> {
        self.push_scope();
        let pat = self.resolve_and_bind_pattern(arm.pattern, arm.body.span);
        // Guards may themselves contain `is` expressions; their
        // bindings need to flow into subsequent guards and the body.
        let mut guards_out: Vec<Expr<'src>> = Vec::with_capacity(arm.guards.len());
        for raw_guard in arm.guards {
            let g = self.resolve_expr(raw_guard);
            let mut is_binds: Vec<(String, SymbolId)> = Vec::new();
            collect_is_bindings(&g, self.symbols, &mut is_binds);
            for (name, sym) in is_binds {
                self.insert_local(name, sym);
            }
            guards_out.push(g);
        }
        let body = self.resolve_expr(arm.body);
        self.pop_scope();
        MatchArm {
            pattern: pat,
            guards: guards_out,
            body,
            is_return: arm.is_return,
        }
    }

    /// Walk a pattern, allocate fresh `SymbolId`s for every
    /// `Pattern::Binding`, AND insert each into the innermost scope.
    /// Used for match arms and `Destructure` where the bindings flow
    /// immediately into the enclosing scope.
    fn resolve_and_bind_pattern(
        &mut self,
        pat: raw::Pattern<'src>,
        span: Span,
    ) -> Pattern<'src> {
        match pat {
            raw::Pattern::Constructor { name, fields } => Pattern::Constructor {
                name,
                fields: fields
                    .into_iter()
                    .map(|p| self.resolve_and_bind_pattern(p, span))
                    .collect(),
            },
            raw::Pattern::Record { fields } => Pattern::Record {
                fields: fields
                    .into_iter()
                    .map(|(n, p)| {
                        let sym = self.fields.intern(n);
                        (sym, self.resolve_and_bind_pattern(p, span))
                    })
                    .collect(),
            },
            raw::Pattern::Tuple(elems) => Pattern::Tuple(
                elems
                    .into_iter()
                    .map(|p| self.resolve_and_bind_pattern(p, span))
                    .collect(),
            ),
            raw::Pattern::Wildcard => Pattern::Wildcard,
            raw::Pattern::Binding(name) => {
                let id = self.bind_local(name, span);
                Pattern::Binding(id)
            }
        }
    }
}

// ---- is-binding collection (for scope flow through `and` / guards / if-then) ----

/// Walk `expr` looking for `Is { pattern: Pattern::Binding(sym), .. }`
/// subexpressions inside an `And`-chain, and collect `(source_name,
/// SymbolId)` pairs. Used to flow `is`-bindings into the RHS of `and`,
/// the `then` branch of a boolean `if`, or the `return` value of a
/// guard clause.
fn collect_is_bindings(
    expr: &Expr<'_>,
    symbols: &SymbolTable,
    out: &mut Vec<(String, SymbolId)>,
) {
    match &expr.kind {
        ExprKind::Is { pattern, .. } => {
            collect_pattern_bindings(pattern, symbols, out);
        }
        ExprKind::BinOp {
            op: BinOp::And,
            lhs,
            rhs,
        } => {
            collect_is_bindings(lhs, symbols, out);
            collect_is_bindings(rhs, symbols, out);
        }
        _ => {}
    }
}

fn collect_pattern_bindings(
    pat: &Pattern<'_>,
    symbols: &SymbolTable,
    out: &mut Vec<(String, SymbolId)>,
) {
    match pat {
        Pattern::Binding(sym) => {
            out.push((symbols.display(*sym).to_owned(), *sym));
        }
        Pattern::Constructor { fields, .. } => {
            for f in fields {
                collect_pattern_bindings(f, symbols, out);
            }
        }
        Pattern::Record { fields } => {
            for (_, p) in fields {
                collect_pattern_bindings(p, symbols, out);
            }
        }
        Pattern::Tuple(elems) => {
            for e in elems {
                collect_pattern_bindings(e, symbols, out);
            }
        }
        Pattern::Wildcard => {}
    }
}

// ---- Raw-type conversion helpers (no names to resolve) ----

const fn type_decl_kind_from_raw(kind: raw::TypeDeclKind) -> TypeDeclKind {
    match kind {
        raw::TypeDeclKind::Alias => TypeDeclKind::Alias,
        raw::TypeDeclKind::Transparent => TypeDeclKind::Transparent,
        raw::TypeDeclKind::Opaque => TypeDeclKind::Opaque,
    }
}

impl<'src> Resolver<'_, 'src> {
    fn constraint(&mut self, c: raw::ConstraintDecl<'src>) -> ConstraintDecl<'src> {
        ConstraintDecl {
            type_var: c.type_var,
            method: c.method,
            method_type: c.method_type.map(|ty| self.type_expr(ty)),
        }
    }

    fn type_expr(&mut self, ty: raw::TypeExpr<'src>) -> TypeExpr<'src> {
        match ty {
            raw::TypeExpr::Named(name) => TypeExpr::Named(name),
            raw::TypeExpr::App(name, args) => TypeExpr::App(
                name,
                args.into_iter().map(|t| self.type_expr(t)).collect(),
            ),
            raw::TypeExpr::TagUnion(tags, open) => TypeExpr::TagUnion(
                tags.into_iter().map(|t| self.tag_decl(t)).collect(),
                open,
            ),
            raw::TypeExpr::Arrow(params, ret) => TypeExpr::Arrow(
                params.into_iter().map(|t| self.type_expr(t)).collect(),
                Box::new(self.type_expr(*ret)),
            ),
            raw::TypeExpr::Record(fields) => TypeExpr::Record(
                fields
                    .into_iter()
                    .map(|(n, t)| (self.fields.intern(n), self.type_expr(t)))
                    .collect(),
            ),
            raw::TypeExpr::Tuple(elems) => {
                TypeExpr::Tuple(elems.into_iter().map(|t| self.type_expr(t)).collect())
            }
        }
    }

    fn tag_decl(&mut self, tag: raw::TagDecl<'src>) -> TagDecl<'src> {
        TagDecl {
            name: tag.name,
            fields: tag.fields.into_iter().map(|t| self.type_expr(t)).collect(),
        }
    }
}

const fn bin_op_from_raw(op: raw::BinOp) -> BinOp {
    match op {
        raw::BinOp::Add => BinOp::Add,
        raw::BinOp::Sub => BinOp::Sub,
        raw::BinOp::Mul => BinOp::Mul,
        raw::BinOp::Div => BinOp::Div,
        raw::BinOp::Rem => BinOp::Rem,
        raw::BinOp::Eq => BinOp::Eq,
        raw::BinOp::Neq => BinOp::Neq,
        raw::BinOp::And => BinOp::And,
        raw::BinOp::Or => BinOp::Or,
    }
}
