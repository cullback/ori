use std::collections::HashMap;

use crate::core::{
    Builtin, ConstructorDef, Core, DebugNames, FuncDef, FuncId, MonoType, Program, TypeDef, TypeId,
    VarId,
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
    var_types: HashMap<VarId, MonoType>,
    constructor_schemes: HashMap<FuncId, crate::types::engine::Scheme>,
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

    /// Update the `mono_type` for each field of a constructor after instantiation scanning.
    pub fn update_constructor_field_types(&mut self, tag: FuncId, mono_types: &[MonoType]) {
        for type_def in &mut self.types {
            for con in &mut type_def.constructors {
                if con.tag == tag {
                    for (field, mono) in con.fields.iter_mut().zip(mono_types.iter()) {
                        field.mono_type = Some(mono.clone());
                    }
                    return;
                }
            }
        }
    }

    pub fn set_var_type(&mut self, id: VarId, mono: MonoType) {
        self.var_types.insert(id, mono);
    }

    pub fn get_var_type(&self, id: VarId) -> Option<&MonoType> {
        self.var_types.get(&id)
    }

    pub fn set_constructor_scheme(&mut self, tag: FuncId, scheme: crate::types::engine::Scheme) {
        self.constructor_schemes.insert(tag, scheme);
    }

    pub fn build(self, main: Core) -> Program {
        Program {
            types: self.types,
            funcs: self.funcs,
            builtins: self.builtins,
            main,
            debug_names: self.debug_names,
            var_types: self.var_types,
            constructor_schemes: self.constructor_schemes,
        }
    }
}
