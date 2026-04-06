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
    Record(Box<Type>),
    RowEmpty,
    RowExtend(String, Box<Type>, Box<Type>),
    Tuple(Vec<Type>),
}

impl Type {
    /// Apply a function to each direct child type, preserving structure.
    pub fn map_children<F: FnMut(&Self) -> Self>(&self, f: &mut F) -> Self {
        match self {
            Self::Var(_) | Self::Con(_) | Self::RowEmpty => self.clone(),
            Self::App(name, args) => Self::App(name.clone(), args.iter().map(&mut *f).collect()),
            Self::Arrow(params, ret) => {
                Self::Arrow(params.iter().map(&mut *f).collect(), Box::new(f(ret)))
            }
            Self::Record(row) => Self::Record(Box::new(f(row))),
            Self::RowExtend(label, field_ty, rest) => {
                Self::RowExtend(label.clone(), Box::new(f(field_ty)), Box::new(f(rest)))
            }
            Self::Tuple(elems) => Self::Tuple(elems.iter().map(f).collect()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Scheme {
    pub vars: Vec<TypeVar>,
    pub ty: Type,
}

impl Scheme {
    pub const fn mono(ty: Type) -> Self {
        Self { vars: vec![], ty }
    }
}

/// Generic HM type engine: substitution, unification, generalization, instantiation.
pub struct TypeEngine {
    pub next_var: usize,
    pub subst: HashMap<TypeVar, Type>,
}

impl TypeEngine {
    pub fn new() -> Self {
        Self {
            next_var: 0,
            subst: HashMap::new(),
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
        if let Type::Var(v) = &resolved {
            *v == tv
        } else {
            let mut found = false;
            resolved.map_children(&mut |child| {
                if self.occurs_in(tv, child) {
                    found = true;
                }
                child.clone()
            });
            found
        }
    }

    // ---- Unification ----

    pub fn unify(&mut self, t1: &Type, t2: &Type) {
        let lhs = self.resolve(t1);
        let rhs = self.resolve(t2);

        match (&lhs, &rhs) {
            (Type::Var(a), Type::Var(b)) if a == b => {}
            (Type::Var(a), _) => {
                assert!(
                    !self.occurs_in(*a, &rhs),
                    "infinite type: {a:?} occurs in {rhs:?}"
                );
                self.subst.insert(*a, rhs);
            }
            (_, Type::Var(_)) => self.unify(&rhs, &lhs),
            (Type::Con(a), Type::Con(b)) => {
                assert!(a == b, "type error: cannot unify {a} with {b}");
            }
            (Type::App(n1, a1), Type::App(n2, a2)) => {
                assert!(
                    n1 == n2 && a1.len() == a2.len(),
                    "type error: cannot unify {n1} with {n2}"
                );
                for (x, y) in a1.iter().zip(a2.iter()) {
                    self.unify(x, y);
                }
            }
            (Type::Arrow(p1, r1), Type::Arrow(p2, r2)) => {
                assert!(
                    p1.len() == p2.len(),
                    "type error: function arity mismatch: {} vs {}",
                    p1.len(),
                    p2.len()
                );
                for (x, y) in p1.iter().zip(p2.iter()) {
                    self.unify(x, y);
                }
                self.unify(r1, r2);
            }
            (Type::Tuple(a), Type::Tuple(b)) => {
                assert!(
                    a.len() == b.len(),
                    "type error: tuple length mismatch: {} vs {}",
                    a.len(),
                    b.len()
                );
                for (x, y) in a.iter().zip(b.iter()) {
                    self.unify(x, y);
                }
            }
            (Type::Record(r1), Type::Record(r2)) => self.unify(r1, r2),
            (Type::RowEmpty, Type::RowEmpty) => {}
            (Type::RowExtend(label, ty, rest), _) => {
                let (other_ty, other_rest) = self.rewrite_row(&rhs, label);
                self.unify(ty, &other_ty);
                self.unify(rest, &other_rest);
            }
            (_, Type::RowExtend(..)) => self.unify(&rhs, &lhs),
            _ => {
                panic!(
                    "type error: cannot unify {} with {}",
                    self.display_type(&lhs),
                    self.display_type(&rhs)
                );
            }
        }
    }

    // ---- Row rewriting ----

    pub fn rewrite_row(&mut self, row: &Type, label: &str) -> (Type, Type) {
        let resolved = self.resolve(row);
        match resolved {
            Type::RowEmpty => panic!("type error: record has no field '{label}'"),
            Type::RowExtend(l, ty, rest) if l == label => (*ty, *rest),
            Type::RowExtend(l, ty, rest) => {
                let (field_ty, new_rest) = self.rewrite_row(&rest, label);
                (field_ty, Type::RowExtend(l, ty, Box::new(new_rest)))
            }
            Type::Var(tv) => {
                let field_ty = self.fresh();
                let new_rest = self.fresh();
                let new_row = Type::RowExtend(
                    label.to_owned(),
                    Box::new(field_ty.clone()),
                    Box::new(new_rest.clone()),
                );
                assert!(!self.occurs_in(tv, &new_row), "infinite row type");
                self.subst.insert(tv, new_row);
                (field_ty, new_rest)
            }
            _ => panic!(
                "type error: expected row, got {}",
                self.display_type(&resolved)
            ),
        }
    }

    // ---- Generalization & Instantiation ----

    pub fn free_vars(&self, ty: &Type) -> HashSet<TypeVar> {
        let resolved = self.resolve(ty);
        if let Type::Var(v) = &resolved {
            HashSet::from([*v])
        } else {
            let mut fvs = HashSet::new();
            resolved.map_children(&mut |child| {
                fvs.extend(self.free_vars(child));
                child.clone()
            });
            fvs
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
        Scheme {
            vars,
            ty: self.resolve(ty),
        }
    }

    pub fn instantiate(&mut self, scheme: &Scheme) -> Type {
        let mapping: HashMap<TypeVar, Type> =
            scheme.vars.iter().map(|&v| (v, self.fresh())).collect();
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
            Type::Record(row) => {
                let mut field_strs = Vec::new();
                let mut current = self.resolve(row);
                loop {
                    match current {
                        Type::RowExtend(label, field_ty, rest) => {
                            field_strs.push(format!("{label}: {}", self.display_type(&field_ty)));
                            current = self.resolve(&rest);
                        }
                        Type::RowEmpty => break,
                        _ => {
                            field_strs.push("..".to_owned());
                            break;
                        }
                    }
                }
                format!("{{ {} }}", field_strs.join(", "))
            }
            Type::RowEmpty => "{}".to_owned(),
            Type::RowExtend(label, field_ty, rest) => {
                format!(
                    "{{ {label}: {} | {} }}",
                    self.display_type(field_ty),
                    self.display_type(rest)
                )
            }
            Type::Tuple(elems) => {
                let elem_strs: Vec<String> = elems.iter().map(|e| self.display_type(e)).collect();
                format!("({})", elem_strs.join(", "))
            }
        }
    }
}
