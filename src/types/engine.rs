//! Pure Hindley-Milner type engine.
//!
//! `Type`, `TypeVar`, `Scheme`, substitution, unification, generalization, instantiation.
//! No knowledge of the Ori AST, source code, or spans.

use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeVar(pub usize);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Var(TypeVar),
    Con(String),
    App(String, Vec<Type>),
    Arrow(Vec<Type>, Box<Type>),
    /// Record type with named fields and an optional rest (open row variable).
    /// `rest: None` means a closed record; `rest: Some(Var(tv))` means open (row polymorphic).
    Record {
        fields: Vec<(String, Type)>,
        rest: Option<Box<Type>>,
    },
    /// Structural tag union with a list of tags (name + payload types) and
    /// an optional rest (open row variable). Symmetric to `Record`:
    /// `rest: None` means a closed union, `rest: Some(Var(tv))` means open
    /// (row polymorphic — the union may contain *at least* these tags).
    ///
    /// During inference, bare constructor references produce open rows
    /// (e.g. `Red` has inferred type `[Red, ..ρ]`). Rows close at match
    /// exhaustiveness, type annotations, and function-boundary
    /// generalization. By the time monomorphization runs, every tag
    /// union that reaches code generation is closed.
    TagUnion {
        tags: Vec<(String, Vec<Type>)>,
        rest: Option<Box<Type>>,
    },
    Tuple(Vec<Type>),
}

/// Flatten nested row chains for `Record` and `TagUnion`.
///
/// When a row variable is unified to a rest-shaped type (which happens
/// in `unify_records` and `unify_tag_unions`), the resolved shape ends
/// up nested: `{x | {y | None}}` instead of `{x, y | None}`. Resolving
/// through this helper folds the chain into a single flat row so that
/// downstream consumers (display, mono normalization, tests) see a
/// canonical form.
pub fn flatten_rows(ty: Type) -> Type {
    match ty {
        Type::TagUnion { mut tags, mut rest } => {
            loop {
                let Some(next) = rest.take() else {
                    break;
                };
                match *next {
                    Type::TagUnion {
                        tags: more,
                        rest: next_rest,
                    } => {
                        tags.extend(more);
                        rest = next_rest;
                    }
                    other => {
                        rest = Some(Box::new(other));
                        break;
                    }
                }
            }
            Type::TagUnion { tags, rest }
        }
        Type::Record { mut fields, mut rest } => {
            loop {
                let Some(next) = rest.take() else {
                    break;
                };
                match *next {
                    Type::Record {
                        fields: more,
                        rest: next_rest,
                    } => {
                        fields.extend(more);
                        rest = next_rest;
                    }
                    other => {
                        rest = Some(Box::new(other));
                        break;
                    }
                }
            }
            Type::Record { fields, rest }
        }
        other => other,
    }
}

impl Type {
    /// Apply a function to each direct child type, preserving structure.
    pub fn map_children<F: FnMut(&Self) -> Self>(&self, f: &mut F) -> Self {
        match self {
            Self::Var(_) | Self::Con(_) => self.clone(),
            Self::App(name, args) => Self::App(name.clone(), args.iter().map(&mut *f).collect()),
            Self::Arrow(params, ret) => {
                Self::Arrow(params.iter().map(&mut *f).collect(), Box::new(f(ret)))
            }
            Self::Record { fields, rest } => Self::Record {
                fields: fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), f(ty)))
                    .collect(),
                rest: rest.as_ref().map(|r| Box::new(f(r))),
            },
            Self::TagUnion { tags, rest } => Self::TagUnion {
                tags: tags
                    .iter()
                    .map(|(name, payloads)| {
                        (name.clone(), payloads.iter().map(&mut *f).collect())
                    })
                    .collect(),
                rest: rest.as_ref().map(|r| Box::new(f(r))),
            },
            Self::Tuple(elems) => Self::Tuple(elems.iter().map(f).collect()),
        }
    }
}

/// A structural constraint: a type variable must have a method with a given type.
#[derive(Debug, Clone)]
pub struct Constraint {
    pub type_var: TypeVar,
    pub method_name: String,
    pub method_type: Type,
}

#[derive(Debug, Clone)]
pub struct Scheme {
    pub vars: Vec<TypeVar>,
    pub constraints: Vec<Constraint>,
    pub ty: Type,
}

impl Scheme {
    pub const fn mono(ty: Type) -> Self {
        Self {
            vars: vec![],
            constraints: vec![],
            ty,
        }
    }
}

/// Generic HM type engine: substitution, unification, generalization, instantiation.
pub struct TypeEngine {
    pub next_var: usize,
    pub subst: HashMap<TypeVar, Type>,
    /// Accumulated constraints during inference.
    pub constraints: Vec<Constraint>,
    /// Nominal types currently transparent (name → underlying type).
    /// During method body inference, the nominal type unifies with its underlying type.
    pub transparent: HashMap<String, Type>,
}

impl TypeEngine {
    pub fn new() -> Self {
        Self {
            next_var: 0,
            subst: HashMap::new(),
            constraints: Vec::new(),
            transparent: HashMap::new(),
        }
    }

    #[expect(
        clippy::arithmetic_side_effects,
        clippy::missing_const_for_fn,
        reason = "type variable counter"
    )]
    pub fn fresh(&mut self) -> Type {
        let tv = TypeVar(self.next_var);
        self.next_var += 1;
        Type::Var(tv)
    }

    // ---- Substitution ----

    pub fn resolve(&self, ty: &Type) -> Type {
        if let Type::Var(tv) = ty {
            return self
                .subst
                .get(tv)
                .map_or_else(|| ty.clone(), |t| self.resolve(t));
        }
        let resolved = ty.map_children(&mut |child| self.resolve(child));
        flatten_rows(resolved)
    }

    pub fn occurs_in(&self, tv: TypeVar, ty: &Type) -> bool {
        let resolved = self.resolve(ty);
        match &resolved {
            Type::Var(v) => *v == tv,
            Type::Con(_) => false,
            Type::App(_, args) => args.iter().any(|a| self.occurs_in(tv, a)),
            Type::Arrow(params, ret) => {
                params.iter().any(|p| self.occurs_in(tv, p)) || self.occurs_in(tv, ret)
            }
            Type::Record { fields, rest } => {
                fields.iter().any(|(_, t)| self.occurs_in(tv, t))
                    || rest.as_ref().is_some_and(|r| self.occurs_in(tv, r))
            }
            Type::TagUnion { tags, rest } => {
                tags.iter()
                    .any(|(_, payloads)| payloads.iter().any(|p| self.occurs_in(tv, p)))
                    || rest.as_ref().is_some_and(|r| self.occurs_in(tv, r))
            }
            Type::Tuple(elems) => elems.iter().any(|e| self.occurs_in(tv, e)),
        }
    }

    // ---- Unification ----

    pub fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), String> {
        let lhs = self.resolve(t1);
        let rhs = self.resolve(t2);

        match (&lhs, &rhs) {
            (Type::Var(a), Type::Var(b)) if a == b => Ok(()),
            (Type::Var(a), _) => {
                if self.occurs_in(*a, &rhs) {
                    return Err(format!("infinite type: {a:?} occurs in {rhs:?}"));
                }
                self.subst.insert(*a, rhs);
                Ok(())
            }
            (_, Type::Var(_)) => self.unify(&rhs, &lhs),
            (Type::Con(a), Type::Con(b)) => self.unify_cons(a, b, &lhs, &rhs),
            (Type::App(n1, a1), Type::App(n2, a2)) => self.unify_apps(n1, a1, n2, a2),
            (Type::Arrow(p1, r1), Type::Arrow(p2, r2)) => self.unify_arrows(p1, r1, p2, r2),
            (Type::Tuple(a), Type::Tuple(b)) => self.unify_tuples(a, b),
            (
                Type::Record {
                    fields: f1,
                    rest: r1,
                },
                Type::Record {
                    fields: f2,
                    rest: r2,
                },
            ) => self.unify_records(f1, r1.as_deref(), f2, r2.as_deref()),
            (
                Type::TagUnion {
                    tags: t1,
                    rest: r1,
                },
                Type::TagUnion {
                    tags: t2,
                    rest: r2,
                },
            ) => self.unify_tag_unions(t1, r1.as_deref(), t2, r2.as_deref()),
            // Transparent nominal: Con vs non-Con (e.g. Str vs List(U8))
            (Type::Con(a), _) => {
                if let Some(underlying) = self.transparent.get(a).cloned() {
                    return self.unify(&underlying, &rhs);
                }
                Err(format!(
                    "cannot unify {} with {}",
                    self.display_type(&lhs),
                    self.display_type(&rhs)
                ))
            }
            (_, Type::Con(b)) => {
                if let Some(underlying) = self.transparent.get(b).cloned() {
                    return self.unify(&lhs, &underlying);
                }
                Err(format!(
                    "cannot unify {} with {}",
                    self.display_type(&lhs),
                    self.display_type(&rhs)
                ))
            }
            _ => Err(format!(
                "cannot unify {} with {}",
                self.display_type(&lhs),
                self.display_type(&rhs)
            )),
        }
    }

    // ---- Record unification ----

    /// Unify two record types. Matches fields by name, and handles open/closed rows.
    fn unify_records(
        &mut self,
        f1: &[(String, Type)],
        r1: Option<&Type>,
        f2: &[(String, Type)],
        r2: Option<&Type>,
    ) -> Result<(), String> {
        // Partition fields into: common (in both), only-in-lhs, only-in-rhs
        let names1: HashSet<&str> = f1.iter().map(|(n, _)| n.as_str()).collect();
        let names2: HashSet<&str> = f2.iter().map(|(n, _)| n.as_str()).collect();

        // Unify common fields
        for (name, ty1) in f1 {
            if let Some((_, ty2)) = f2.iter().find(|(n, _)| n == name) {
                self.unify(ty1, ty2)?;
            }
        }

        let only_lhs: Vec<(String, Type)> = f1
            .iter()
            .filter(|(n, _)| !names2.contains(n.as_str()))
            .cloned()
            .collect();
        let only_rhs: Vec<(String, Type)> = f2
            .iter()
            .filter(|(n, _)| !names1.contains(n.as_str()))
            .cloned()
            .collect();

        match (r1, r2) {
            // Both closed: all fields must match exactly
            (None, None) => {
                if !only_lhs.is_empty() || !only_rhs.is_empty() {
                    let extra: Vec<&str> = only_lhs
                        .iter()
                        .chain(only_rhs.iter())
                        .map(|(n, _)| n.as_str())
                        .collect();
                    return Err(format!("record field mismatch: extra fields {extra:?}"));
                }
                Ok(())
            }
            // LHS is open: extra RHS fields + common → constrain the LHS rest var
            (Some(rest_var), None) => {
                if !only_lhs.is_empty() {
                    return Err(format!("record has no field '{}'", only_lhs[0].0));
                }
                let tail = Type::Record {
                    fields: only_rhs,
                    rest: None,
                };
                self.unify(rest_var, &tail)
            }
            // RHS is open: symmetric case
            (None, Some(rest_var)) => {
                if !only_rhs.is_empty() {
                    return Err(format!("record has no field '{}'", only_rhs[0].0));
                }
                let tail = Type::Record {
                    fields: only_lhs,
                    rest: None,
                };
                self.unify(rest_var, &tail)
            }
            // Both open: unify rest vars with records of the other's extras
            (Some(rv1), Some(rv2)) => {
                let new_rest = self.fresh();
                let tail1 = Type::Record {
                    fields: only_rhs,
                    rest: Some(Box::new(new_rest.clone())),
                };
                let tail2 = Type::Record {
                    fields: only_lhs,
                    rest: Some(Box::new(new_rest)),
                };
                self.unify(rv1, &tail1)?;
                self.unify(rv2, &tail2)
            }
        }
    }

    fn unify_cons(&mut self, a: &str, b: &str, lhs: &Type, rhs: &Type) -> Result<(), String> {
        if a == b {
            return Ok(());
        }
        if let Some(underlying) = self.transparent.get(a).cloned() {
            return self.unify(&underlying, rhs);
        }
        if let Some(underlying) = self.transparent.get(b).cloned() {
            return self.unify(lhs, &underlying);
        }
        Err(format!("cannot unify {a} with {b}"))
    }

    fn unify_apps(
        &mut self,
        n1: &str,
        a1: &[Type],
        n2: &str,
        a2: &[Type],
    ) -> Result<(), String> {
        if n1 != n2 || a1.len() != a2.len() {
            return Err(format!("cannot unify {n1} with {n2}"));
        }
        for (x, y) in a1.iter().zip(a2.iter()) {
            self.unify(x, y)?;
        }
        Ok(())
    }

    fn unify_arrows(
        &mut self,
        p1: &[Type],
        r1: &Type,
        p2: &[Type],
        r2: &Type,
    ) -> Result<(), String> {
        if p1.len() != p2.len() {
            return Err(format!(
                "function arity mismatch: {} vs {}",
                p1.len(),
                p2.len()
            ));
        }
        for (x, y) in p1.iter().zip(p2.iter()) {
            self.unify(x, y)?;
        }
        self.unify(r1, r2)
    }

    fn unify_tuples(&mut self, a: &[Type], b: &[Type]) -> Result<(), String> {
        if a.len() != b.len() {
            return Err(format!("tuple length mismatch: {} vs {}", a.len(), b.len()));
        }
        for (x, y) in a.iter().zip(b.iter()) {
            self.unify(x, y)?;
        }
        Ok(())
    }

    // ---- Tag union unification ----

    /// Unify two tag union types. Matches tags by name (and arity);
    /// payloads for common tags must unify. Handles open/closed rows
    /// symmetrically to `unify_records`. A tag's payload arity is part
    /// of its identity — `Red` and `Red(I64)` fail to unify.
    fn unify_tag_unions(
        &mut self,
        t1: &[(String, Vec<Type>)],
        r1: Option<&Type>,
        t2: &[(String, Vec<Type>)],
        r2: Option<&Type>,
    ) -> Result<(), String> {
        let names1: HashSet<&str> = t1.iter().map(|(n, _)| n.as_str()).collect();
        let names2: HashSet<&str> = t2.iter().map(|(n, _)| n.as_str()).collect();

        // Common tags: unify payload arities and payload types.
        for (name, p1) in t1 {
            if let Some((_, p2)) = t2.iter().find(|(n, _)| n == name) {
                if p1.len() != p2.len() {
                    return Err(format!(
                        "tag '{name}' has {} payload(s) here but {} there",
                        p1.len(),
                        p2.len()
                    ));
                }
                for (x, y) in p1.iter().zip(p2.iter()) {
                    self.unify(x, y)?;
                }
            }
        }

        let only_lhs: Vec<(String, Vec<Type>)> = t1
            .iter()
            .filter(|(n, _)| !names2.contains(n.as_str()))
            .cloned()
            .collect();
        let only_rhs: Vec<(String, Vec<Type>)> = t2
            .iter()
            .filter(|(n, _)| !names1.contains(n.as_str()))
            .cloned()
            .collect();

        match (r1, r2) {
            // Both closed: every tag must match exactly.
            (None, None) => {
                if !only_lhs.is_empty() || !only_rhs.is_empty() {
                    let extra: Vec<&str> = only_lhs
                        .iter()
                        .chain(only_rhs.iter())
                        .map(|(n, _)| n.as_str())
                        .collect();
                    return Err(format!("tag union mismatch: extra tags {extra:?}"));
                }
                Ok(())
            }
            // LHS open: the row variable absorbs the RHS-only tags. LHS-only
            // tags are not allowed because RHS is closed and can't grow.
            (Some(rest_var), None) => {
                if !only_lhs.is_empty() {
                    return Err(format!(
                        "tag union has no tag '{}'",
                        only_lhs[0].0
                    ));
                }
                let tail = Type::TagUnion {
                    tags: only_rhs,
                    rest: None,
                };
                self.unify(rest_var, &tail)
            }
            // RHS open: symmetric.
            (None, Some(rest_var)) => {
                if !only_rhs.is_empty() {
                    return Err(format!(
                        "tag union has no tag '{}'",
                        only_rhs[0].0
                    ));
                }
                let tail = Type::TagUnion {
                    tags: only_lhs,
                    rest: None,
                };
                self.unify(rest_var, &tail)
            }
            // Both open: if there are no extras on either side, just
            // unify the two rest vars directly. Otherwise, unify each
            // rest var with a union of the other side's extras plus a
            // fresh shared row variable.
            (Some(rv1), Some(rv2)) => {
                if only_lhs.is_empty() && only_rhs.is_empty() {
                    return self.unify(rv1, rv2);
                }
                let new_rest = self.fresh();
                let tail1 = Type::TagUnion {
                    tags: only_rhs,
                    rest: Some(Box::new(new_rest.clone())),
                };
                let tail2 = Type::TagUnion {
                    tags: only_lhs,
                    rest: Some(Box::new(new_rest)),
                };
                self.unify(rv1, &tail1)?;
                self.unify(rv2, &tail2)
            }
        }
    }

    // ---- Generalization & Instantiation ----

    pub fn free_vars(&self, ty: &Type) -> HashSet<TypeVar> {
        let mut fvs = HashSet::new();
        self.collect_free_vars(ty, &mut fvs);
        fvs
    }

    fn collect_free_vars(&self, ty: &Type, fvs: &mut HashSet<TypeVar>) {
        let resolved = self.resolve(ty);
        match &resolved {
            Type::Var(v) => {
                fvs.insert(*v);
            }
            Type::Con(_) => {}
            Type::App(_, args) => {
                for a in args {
                    self.collect_free_vars(a, fvs);
                }
            }
            Type::Arrow(params, ret) => {
                for p in params {
                    self.collect_free_vars(p, fvs);
                }
                self.collect_free_vars(ret, fvs);
            }
            Type::Record { fields, rest } => {
                for (_, t) in fields {
                    self.collect_free_vars(t, fvs);
                }
                if let Some(r) = rest {
                    self.collect_free_vars(r, fvs);
                }
            }
            Type::TagUnion { tags, rest } => {
                for (_, payloads) in tags {
                    for p in payloads {
                        self.collect_free_vars(p, fvs);
                    }
                }
                if let Some(r) = rest {
                    self.collect_free_vars(r, fvs);
                }
            }
            Type::Tuple(elems) => {
                for e in elems {
                    self.collect_free_vars(e, fvs);
                }
            }
        }
    }

    pub fn free_vars_in_env(&self, env: &HashMap<String, Scheme>) -> HashSet<TypeVar> {
        env.values()
            .flat_map(|scheme| {
                let fvs = self.free_vars(&scheme.ty);
                let bound: HashSet<TypeVar> = scheme.vars.iter().copied().collect();
                fvs.into_iter().filter(move |v| !bound.contains(v))
            })
            .collect()
    }

    pub fn generalize(&self, ty: &Type, env: &HashMap<String, Scheme>) -> Scheme {
        let fvs = self.free_vars(ty);
        let env_fvs = self.free_vars_in_env(env);
        let vars: Vec<TypeVar> = fvs.into_iter().filter(|v| !env_fvs.contains(v)).collect();
        let var_set: HashSet<TypeVar> = vars.iter().copied().collect();
        // Bundle constraints that reference the generalized vars
        let constraints: Vec<Constraint> = self
            .constraints
            .iter()
            .filter(|c| {
                let resolved = self.resolve(&Type::Var(c.type_var));
                match resolved {
                    Type::Var(tv) => var_set.contains(&tv),
                    _ => false, // already resolved to concrete type, constraint was checked
                }
            })
            .cloned()
            .collect();
        Scheme {
            vars,
            constraints,
            ty: self.resolve(ty),
        }
    }

    pub fn instantiate(&mut self, scheme: &Scheme) -> Type {
        let mapping: HashMap<TypeVar, Type> =
            scheme.vars.iter().map(|&v| (v, self.fresh())).collect();
        // Re-add constraints with remapped type vars
        for c in &scheme.constraints {
            let Type::Var(new_tv) = Self::apply_mapping(&Type::Var(c.type_var), &mapping) else {
                continue;
            };
            self.constraints.push(Constraint {
                type_var: new_tv,
                method_name: c.method_name.clone(),
                method_type: Self::apply_mapping(&c.method_type, &mapping),
            });
        }
        Self::apply_mapping(&scheme.ty, &mapping)
    }

    pub fn apply_mapping(ty: &Type, mapping: &HashMap<TypeVar, Type>) -> Type {
        match ty {
            Type::Var(v) => mapping.get(v).cloned().unwrap_or_else(|| ty.clone()),
            _ => ty.map_children(&mut |child| Self::apply_mapping(child, mapping)),
        }
    }

    // ---- Structural equality (without unifying) ----

    pub fn types_match(&self, a: &Type, b: &Type) -> bool {
        let a_resolved = self.resolve(a);
        let b_resolved = self.resolve(b);
        match (&a_resolved, &b_resolved) {
            (Type::Var(x), Type::Var(y)) => x == y,
            (Type::Con(x), Type::Con(y)) => x == y,
            (Type::App(n1, a1), Type::App(n2, a2)) => {
                n1 == n2
                    && a1.len() == a2.len()
                    && a1
                        .iter()
                        .zip(a2.iter())
                        .all(|(x, y)| self.types_match(x, y))
            }
            _ => false,
        }
    }

    // ---- Display ----

    pub fn display_type(&self, ty: &Type) -> String {
        let resolved = self.resolve(ty);
        // Show the nominal name if this type matches a transparent underlying type
        #[expect(clippy::iter_over_hash_type, reason = "display order doesn't matter")]
        for (name, underlying) in &self.transparent {
            if self.types_match(&resolved, underlying) {
                return name.clone();
            }
        }
        match &resolved {
            Type::Var(tv) => format!("t{}", tv.0),
            Type::Con(name) => name.clone(),
            Type::App(name, args) => {
                let arg_strs: Vec<String> = args.iter().map(|a| self.display_type(a)).collect();
                format!("{name}({})", arg_strs.join(", "))
            }
            Type::Arrow(params, ret) => {
                let param_strs: Vec<String> = params.iter().map(|p| self.display_type(p)).collect();
                format!("{} -> {}", param_strs.join(", "), self.display_type(ret))
            }
            Type::Record { fields, rest } => {
                let mut field_strs: Vec<String> = fields
                    .iter()
                    .map(|(label, field_ty)| format!("{label}: {}", self.display_type(field_ty)))
                    .collect();
                if rest.is_some() {
                    field_strs.push("..".to_owned());
                }
                format!("{{ {} }}", field_strs.join(", "))
            }
            Type::TagUnion { tags, rest } => {
                let mut tag_strs: Vec<String> = tags
                    .iter()
                    .map(|(name, payloads)| {
                        if payloads.is_empty() {
                            name.clone()
                        } else {
                            let ps: Vec<String> =
                                payloads.iter().map(|p| self.display_type(p)).collect();
                            format!("{name}({})", ps.join(", "))
                        }
                    })
                    .collect();
                if rest.is_some() {
                    tag_strs.push("..".to_owned());
                }
                format!("[{}]", tag_strs.join(", "))
            }
            Type::Tuple(elems) => {
                let elem_strs: Vec<String> = elems.iter().map(|e| self.display_type(e)).collect();
                format!("({})", elem_strs.join(", "))
            }
        }
    }
}

// ---- Tag union unification tests ----

#[cfg(test)]
mod tag_union_tests {
    use super::*;

    fn i64_ty() -> Type {
        Type::Con("I64".to_owned())
    }

    fn closed(tags: Vec<(&str, Vec<Type>)>) -> Type {
        Type::TagUnion {
            tags: tags
                .into_iter()
                .map(|(n, p)| (n.to_owned(), p))
                .collect(),
            rest: None,
        }
    }

    fn open(engine: &mut TypeEngine, tags: Vec<(&str, Vec<Type>)>) -> Type {
        let rest = engine.fresh();
        Type::TagUnion {
            tags: tags
                .into_iter()
                .map(|(n, p)| (n.to_owned(), p))
                .collect(),
            rest: Some(Box::new(rest)),
        }
    }

    #[test]
    fn closed_closed_exact_match() {
        let mut e = TypeEngine::new();
        let a = closed(vec![("Red", vec![]), ("Green", vec![])]);
        let b = closed(vec![("Red", vec![]), ("Green", vec![])]);
        e.unify(&a, &b).expect("exact closed match should unify");
    }

    #[test]
    fn closed_closed_mismatch_errors() {
        let mut e = TypeEngine::new();
        let a = closed(vec![("Red", vec![]), ("Green", vec![])]);
        let b = closed(vec![("Red", vec![]), ("Blue", vec![])]);
        e.unify(&a, &b)
            .expect_err("closed unions with different tags should fail");
    }

    #[test]
    fn open_closed_widening() {
        // `[Red, ..ρ]` unifies with `[Red, Green, Blue]` by solving
        // ρ to `[Green, Blue]`.
        let mut e = TypeEngine::new();
        let a = open(&mut e, vec![("Red", vec![])]);
        let b = closed(vec![
            ("Red", vec![]),
            ("Green", vec![]),
            ("Blue", vec![]),
        ]);
        e.unify(&a, &b).expect("open should widen to closed");
        let resolved = e.resolve(&a);
        // After unification, `a` resolves to a closed union containing
        // all three tags. Order may depend on the impl; just check
        // membership.
        let Type::TagUnion { tags, rest } = resolved else {
            panic!("expected TagUnion after unify");
        };
        assert_eq!(rest, None, "row should be closed after widening");
        let names: HashSet<&str> = tags.iter().map(|(n, _)| n.as_str()).collect();
        assert!(names.contains("Red"));
        assert!(names.contains("Green"));
        assert!(names.contains("Blue"));
    }

    #[test]
    fn closed_open_narrowing_fails() {
        // A closed `[Red, Green]` cannot absorb an open `[Blue, ..ρ]`
        // because the closed side has no row variable to grow into.
        let mut e = TypeEngine::new();
        let a = closed(vec![("Red", vec![]), ("Green", vec![])]);
        let b = open(&mut e, vec![("Blue", vec![])]);
        e.unify(&a, &b)
            .expect_err("closed union can't grow to include Blue");
    }

    #[test]
    fn open_open_merges() {
        // `[Red, ..ρ1]` and `[Green, ..ρ2]` unify by sharing a common
        // open row. After unify, both resolve to unions containing at
        // least Red and Green.
        let mut e = TypeEngine::new();
        let a = open(&mut e, vec![("Red", vec![])]);
        let b = open(&mut e, vec![("Green", vec![])]);
        e.unify(&a, &b).expect("open-open merge should succeed");
        let resolved_a = e.resolve(&a);
        let resolved_b = e.resolve(&b);
        // Both resolved types should be unions containing at least Red
        // and Green. Their row variables unify through a shared fresh
        // variable, so the result shape is the same.
        let Type::TagUnion { tags: ta, .. } = resolved_a else {
            panic!("expected TagUnion");
        };
        let Type::TagUnion { tags: tb, .. } = resolved_b else {
            panic!("expected TagUnion");
        };
        let names_a: HashSet<&str> = ta.iter().map(|(n, _)| n.as_str()).collect();
        let names_b: HashSet<&str> = tb.iter().map(|(n, _)| n.as_str()).collect();
        assert!(names_a.contains("Red") && names_a.contains("Green"));
        assert!(names_b.contains("Red") && names_b.contains("Green"));
    }

    #[test]
    fn common_tag_payload_unifies() {
        let mut e = TypeEngine::new();
        let v = e.fresh();
        let a = closed(vec![("Ok", vec![v.clone()])]);
        let b = closed(vec![("Ok", vec![i64_ty()])]);
        e.unify(&a, &b).expect("payloads should unify");
        // After unify, the fresh var should resolve to I64.
        let resolved_v = e.resolve(&v);
        assert_eq!(resolved_v, i64_ty());
    }

    #[test]
    fn common_tag_payload_mismatch_fails() {
        let mut e = TypeEngine::new();
        let a = closed(vec![("Red", vec![i64_ty()])]);
        let b = closed(vec![("Red", vec![Type::Con("Str".to_owned())])]);
        e.unify(&a, &b)
            .expect_err("Red(I64) and Red(Str) should not unify");
    }

    #[test]
    fn tag_arity_mismatch_fails() {
        let mut e = TypeEngine::new();
        let a = closed(vec![("Red", vec![])]);
        let b = closed(vec![("Red", vec![i64_ty()])]);
        e.unify(&a, &b)
            .expect_err("nullary Red and Red(I64) should not unify");
    }

    #[test]
    fn open_extension_chains() {
        // Three-way: `[A, ..ρ1]`, then widen to `[A, B, ..ρ2]`, then
        // widen to `[A, B, C]`. Each step closes a bit more of the row.
        let mut e = TypeEngine::new();
        let a = open(&mut e, vec![("A", vec![])]);
        let b = open(&mut e, vec![("A", vec![]), ("B", vec![])]);
        e.unify(&a, &b).expect("first widening");
        let c = closed(vec![("A", vec![]), ("B", vec![]), ("C", vec![])]);
        e.unify(&a, &c).expect("second widening to closed");
        let resolved = e.resolve(&a);
        let Type::TagUnion { tags, rest } = resolved else {
            panic!("expected TagUnion");
        };
        assert_eq!(rest, None);
        assert_eq!(tags.len(), 3);
    }
}
