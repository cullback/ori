//! Pure Hindley-Milner type engine.
//!
//! `Type`, `TypeVar`, `Scheme`, substitution, unification, generalization, instantiation.
//! No knowledge of the Ori AST, source code, or spans.

use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeVar(pub usize);

#[derive(Debug, Clone, PartialEq)]
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
    Tuple(Vec<Type>),
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
        match ty {
            Type::Var(tv) => match self.subst.get(tv) {
                Some(t) => self.resolve(t),
                None => ty.clone(),
            },
            _ => ty.map_children(&mut |child| self.resolve(child)),
        }
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
            (Type::Con(a), Type::Con(b)) => {
                if a == b {
                    return Ok(());
                }
                // Check if one is a transparent nominal type
                if let Some(underlying) = self.transparent.get(a).cloned() {
                    return self.unify(&underlying, &rhs);
                }
                if let Some(underlying) = self.transparent.get(b).cloned() {
                    return self.unify(&lhs, &underlying);
                }
                Err(format!("cannot unify {a} with {b}"))
            }
            (Type::App(n1, a1), Type::App(n2, a2)) => {
                if n1 != n2 || a1.len() != a2.len() {
                    return Err(format!("cannot unify {n1} with {n2}"));
                }
                for (x, y) in a1.iter().zip(a2.iter()) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            (Type::Arrow(p1, r1), Type::Arrow(p2, r2)) => {
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
            (Type::Tuple(a), Type::Tuple(b)) => {
                if a.len() != b.len() {
                    return Err(format!("tuple length mismatch: {} vs {}", a.len(), b.len()));
                }
                for (x, y) in a.iter().zip(b.iter()) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
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
            Type::Tuple(elems) => {
                let elem_strs: Vec<String> = elems.iter().map(|e| self.display_type(e)).collect();
                format!("({})", elem_strs.join(", "))
            }
        }
    }
}
