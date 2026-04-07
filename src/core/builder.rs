use std::collections::HashMap;

use crate::core::{
    Builtin, ConstructorDef, Core, DebugNames, FuncDef, FuncId, Program, TypeDef, TypeId, VarId,
};

#[derive(Debug, Default)]
pub struct Builder {
    next_var: usize,
    next_func: usize,
    next_type: usize,
    types: Vec<TypeDef>,
    funcs: Vec<FuncDef>,
    builtins: HashMap<FuncId, Builtin>,
    debug_names: DebugNames,
}

#[expect(
    clippy::arithmetic_side_effects,
    clippy::missing_const_for_fn,
    reason = "ID counters increment monotonically; const fn with HashMap ops is not stable"
)]
impl Builder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn var(&mut self) -> VarId {
        let id = VarId::new(self.next_var);
        self.next_var += 1;
        id
    }

    pub fn func(&mut self) -> FuncId {
        let id = FuncId::new(self.next_func);
        self.next_func += 1;
        id
    }

    #[allow(dead_code)]
    pub fn type_id(&mut self) -> TypeId {
        let id = TypeId::new(self.next_type);
        self.next_type += 1;
        id
    }

    pub fn debug_name_func(&mut self, id: FuncId, name: String) {
        self.debug_names.funcs.insert(id, name);
    }

    pub fn builtin(&mut self, op: Builtin) -> FuncId {
        let id = self.func();
        self.builtins.insert(id, op);
        id
    }

    /// Register a type. Auto-generates the `TypeId`.
    #[allow(dead_code)]
    pub fn add_type(&mut self, constructors: Vec<ConstructorDef>) {
        let name = self.type_id();
        self.types.push(TypeDef { name, constructors });
    }

    #[allow(dead_code)]
    pub fn add_func(&mut self, funcdef: FuncDef) {
        self.funcs.push(funcdef);
    }

    pub fn build(self, main: Core) -> Program {
        Program {
            types: self.types,
            funcs: self.funcs,
            builtins: self.builtins,
            main,
            debug_names: self.debug_names,
        }
    }
}
