use std::collections::HashMap;

macro_rules! define_id {
    ($name:ident) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $name(usize);

        impl $name {
            pub const fn new(index: usize) -> Self {
                Self(index)
            }
        }
    };
}

define_id!(VarId);
define_id!(FuncId);
define_id!(TypeId);

/// Optional debug names for all three ID types.
#[derive(Debug, Default)]
pub struct DebugNames {
    pub vars: HashMap<VarId, String>,
    pub funcs: HashMap<FuncId, String>,
    #[allow(dead_code)]
    pub types: HashMap<TypeId, String>,
}

impl DebugNames {
    pub fn var_name(&self, id: VarId) -> &str {
        self.vars.get(&id).map_or("?", String::as_str)
    }

    pub fn func_name(&self, id: FuncId) -> &str {
        self.funcs.get(&id).map_or("?", String::as_str)
    }
}

#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub enum Builtin {
    Add,
    Sub,
    Mul,
    Rem,
    Max,
    Eq { true_con: FuncId, false_con: FuncId },
}

#[derive(Debug, Clone, PartialEq)]
#[allow(dead_code)]
pub enum NumVal {
    U64(u64),
    I64(i64),
    F64(f64),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Num(NumVal),
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum Pattern {
    Constructor { tag: FuncId, fields: Vec<VarId> },
}

#[allow(dead_code)]
impl Pattern {
    pub const fn con(tag: FuncId, fields: Vec<VarId>) -> Self {
        Self::Constructor { tag, fields }
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct FoldArm {
    pub pattern: Pattern,
    pub rec_binds: Vec<VarId>,
    pub body: Core,
}

#[allow(dead_code)]
impl FoldArm {
    pub const fn new(tag: FuncId, fields: Vec<VarId>, rec_binds: Vec<VarId>, body: Core) -> Self {
        Self {
            pattern: Pattern::con(tag, fields),
            rec_binds,
            body,
        }
    }
}

/// Six-term core IR.
///
/// Match arms bind constructor fields.
/// Fold arms bind constructor fields plus one recursive result per recursive field.
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum Core {
    Var(VarId),
    Lit(Literal),
    App {
        func: FuncId,
        args: Vec<Core>,
    },
    Let {
        name: VarId,
        val: Box<Core>,
        body: Box<Core>,
    },
    Match {
        expr: Box<Core>,
        arms: Vec<(Pattern, Core)>,
    },
    Fold {
        expr: Box<Core>,
        arms: Vec<FoldArm>,
    },
    Record {
        fields: Vec<(String, Core)>,
    },
    FieldAccess {
        record: Box<Core>,
        field: String,
    },
}

#[allow(dead_code)]
impl Core {
    pub const fn var(name: VarId) -> Self {
        Self::Var(name)
    }

    pub const fn u64(n: u64) -> Self {
        Self::Lit(Literal::Num(NumVal::U64(n)))
    }

    pub const fn i64(n: i64) -> Self {
        Self::Lit(Literal::Num(NumVal::I64(n)))
    }

    pub const fn app(func: FuncId, args: Vec<Self>) -> Self {
        Self::App { func, args }
    }

    pub fn let_(name: VarId, val: Self, body: Self) -> Self {
        Self::Let {
            name,
            val: Box::new(val),
            body: Box::new(body),
        }
    }

    pub fn match_(expr: Self, arms: Vec<(Pattern, Self)>) -> Self {
        Self::Match {
            expr: Box::new(expr),
            arms,
        }
    }

    pub fn fold(expr: Self, arms: Vec<FoldArm>) -> Self {
        Self::Fold {
            expr: Box::new(expr),
            arms,
        }
    }

    pub const fn record(fields: Vec<(String, Self)>) -> Self {
        Self::Record { fields }
    }

    pub fn field_access(record: Self, field: String) -> Self {
        Self::FieldAccess {
            record: Box::new(record),
            field,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
#[allow(clippy::enum_variant_names)]
pub enum Value {
    VNum(NumVal),
    VConstruct { tag: FuncId, fields: Vec<Value> },
    VRecord { fields: Vec<(String, Value)> },
}

/// Marks whether a constructor field refers back to the enclosing type.
#[derive(Debug, Clone)]
pub struct FieldDef {
    pub recursive: bool,
}

#[derive(Debug, Clone)]
pub struct ConstructorDef {
    pub tag: FuncId,
    pub fields: Vec<FieldDef>,
}

#[derive(Debug, Clone)]
pub struct TypeDef {
    #[allow(dead_code)]
    pub name: TypeId,
    pub constructors: Vec<ConstructorDef>,
}

#[derive(Debug, Clone)]
pub struct FuncDef {
    pub name: FuncId,
    pub params: Vec<VarId>,
    pub body: Core,
}

#[derive(Debug)]
pub struct Program {
    pub types: Vec<TypeDef>,
    pub funcs: Vec<FuncDef>,
    pub builtins: HashMap<FuncId, Builtin>,
    pub main: Core,
    pub debug_names: DebugNames,
}
