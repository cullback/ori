//! Lowering for `==` / `!=` and the generated per-type equality
//! functions. Instead of inlining equality SSA at every `==` site,
//! we generate one named function per concrete type the first time
//! we see it, then the `BinOp::Eq` dispatch just calls it. Cached
//! in `eq_func_cache` so each type gets exactly one function.

use crate::ssa::Value;
use crate::ssa::instruction::{BinaryOp, ScalarType};
use crate::types::engine::Type;

use super::LowerCtx;

impl<'a, 'src> LowerCtx<'a, 'src> {
    pub(super) fn lower_eq(&mut self, lhs: Value, rhs: Value, negate: bool) -> Value {
        let cmp = self.builder.binop(BinaryOp::Eq, lhs, rhs, ScalarType::U8);
        self.lower_bool_from_cmp_neg(cmp, negate)
    }

    /// True for types where `==` is a single scalar comparison.
    pub(super) fn is_scalar_eq_type(&self, ty: &Type) -> bool {
        match ty {
            Type::Con(name) => {
                crate::numeric::NumericType::from_name(name).is_some()
                    || self.decls.fieldless_tags.contains_key(name.as_str())
            }
            Type::TagUnion { tags, .. } => tags.iter().all(|(_, fs)| fs.is_empty()),
            _ => false,
        }
    }

    // ---- Generated equality functions ----
    //
    // Instead of inlining equality SSA at every `==` site, generate
    // one named function per concrete type. The BinOp::Eq dispatch
    // just calls it. Cached in `eq_func_cache` so each type gets
    // one function.


    /// For a nominal type like Result or Step, find the slot count
    /// (1 + max_fields) by looking up its constructors.
    fn nominal_slot_count(&self, type_name: &str) -> Option<usize> {
        for (con_name, scheme) in &self.infer.constructor_schemes {
            let ret_ty = match &scheme.ty {
                Type::Arrow(_, ret) => ret.as_ref(),
                other => other,
            };
            if let Type::App(ret_name, _) = ret_ty {
                if ret_name == type_name {
                    if let Some(meta) = self.decls.constructors.get(con_name) {
                        if meta.max_fields > 0 && 1 + meta.max_fields <= 8 {
                            return Some(1 + meta.max_fields);
                        }
                    }
                }
            }
        }
        None
    }

    pub(super) fn mangle_type(ty: &Type) -> String {
        match ty {
            Type::Con(n) => n.clone(),
            Type::App(n, args) => {
                let inner: Vec<String> = args.iter().map(Self::mangle_type).collect();
                format!("{n}({})", inner.join(","))
            }
            Type::Tuple(elems) => {
                let inner: Vec<String> = elems.iter().map(Self::mangle_type).collect();
                format!("({})", inner.join(","))
            }
            Type::Record { fields, .. } => {
                let mut sorted: Vec<(&str, &Type)> =
                    fields.iter().map(|(n, t)| (n.as_str(), t)).collect();
                sorted.sort_by_key(|(n, _)| *n);
                let inner: Vec<String> = sorted
                    .iter()
                    .map(|(n, t)| format!("{n}:{}", Self::mangle_type(t)))
                    .collect();
                format!("{{{}}}", inner.join(","))
            }
            Type::TagUnion { tags, .. } => {
                let inner: Vec<String> = tags
                    .iter()
                    .map(|(n, fs)| {
                        if fs.is_empty() {
                            n.clone()
                        } else {
                            let fstrs: Vec<String> = fs.iter().map(Self::mangle_type).collect();
                            format!("{n}({})", fstrs.join(","))
                        }
                    })
                    .collect();
                format!("[{}]", inner.join(","))
            }
            _ => format!("{ty:?}"),
        }
    }

    pub(super) fn ensure_eq_func(&mut self, ty: &Type) -> String {
        let name = format!("__eq__{}", Self::mangle_type(ty));
        if self.eq_func_cache.contains(&name) {
            return name;
        }
        // Mark as generated BEFORE emitting body (handles recursive types).
        self.eq_func_cache.insert(name.clone());

        let saved_vars = std::mem::take(&mut self.vars);
        let saved_func = std::mem::replace(
            &mut self.builder.func,
            crate::ssa::builder::FuncBuilder::new(),
        );
        let saved_current = self.builder.current_block.take();

        let param_ty = self.scalar_type(ty);
        let lhs = self.builder.add_func_param(param_ty);
        let rhs = self.builder.add_func_param(param_ty);
        self.builder.set_return_type(ScalarType::U8);

        let entry = self.builder.create_block();
        self.builder.switch_to(entry);
        let result = self.emit_eq_body(lhs, rhs, ty);
        self.builder.ret(result);
        self.builder.finish_function(&name, ScalarType::U8);

        self.builder.func = saved_func;
        self.builder.current_block = saved_current;
        self.vars = saved_vars;

        name
    }

    pub(super) fn emit_eq_body(&mut self, lhs: Value, rhs: Value, ty: &Type) -> Value {
        let resolved = self.resolve_transparent(ty);
        let ty = &resolved;
        match ty {
            Type::Record { fields, .. } => {
                let mut sorted: Vec<(&str, &Type)> =
                    fields.iter().map(|(n, t)| (n.as_str(), t)).collect();
                sorted.sort_by_key(|(n, _)| *n);
                let field_types: Vec<&Type> = sorted.iter().map(|(_, t)| *t).collect();
                self.emit_fields_eq(lhs, rhs, &field_types)
            }
            Type::Tuple(elems) => {
                let field_types: Vec<&Type> = elems.iter().collect();
                self.emit_fields_eq(lhs, rhs, &field_types)
            }
            Type::TagUnion { tags, .. } => {
                let max_fields = tags.iter().map(|(_, fs)| fs.len()).max().unwrap_or(0);
                // Tag + payload slots — compare all as U64.
                let n = 1 + max_fields;
                self.emit_slots_eq(lhs, rhs, n)
            }
            Type::App(name, args) if name == "List" => {
                let elem_ty = args.first();
                self.emit_list_eq(lhs, rhs, elem_ty)
            }
            Type::App(name, _) | Type::Con(name) => {
                // Nominal types (Result, Step, etc.): find the
                // constructor slot count and compare structurally.
                if let Some(n) = self.nominal_slot_count(name) {
                    self.emit_slots_eq(lhs, rhs, n)
                } else {
                    self.builder.binop(BinaryOp::Eq, lhs, rhs, ScalarType::U8)
                }
            }
            _ => self.builder.binop(BinaryOp::Eq, lhs, rhs, ScalarType::U8),
        }
    }

    /// Compare a fixed number of typed fields, recursing into sub-types.
    pub(super) fn emit_fields_eq(&mut self, lhs: Value, rhs: Value, field_types: &[&Type]) -> Value {
        if field_types.is_empty() {
            return self.builder.const_u8(1);
        }
        let false_block = self.builder.create_block();
        let true_block = self.builder.create_block();
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, ScalarType::U8);

        for (slot, field_ty) in field_types.iter().enumerate() {
            let sty = self.scalar_type(field_ty);
            let l = self.builder.load(lhs, slot * 8, sty);
            let r = self.builder.load(rhs, slot * 8, sty);
            let field_eq = if self.is_scalar_eq_type(field_ty) {
                self.builder.binop(BinaryOp::Eq, l, r, ScalarType::U8)
            } else {
                let sub_eq = self.ensure_eq_func(field_ty);
                self.builder.call(&sub_eq, vec![l, r], ScalarType::U8)
            };
            let next = if slot + 1 < field_types.len() {
                self.builder.create_block()
            } else {
                true_block
            };
            self.builder.branch(field_eq, next, vec![], false_block, vec![]);
            if slot + 1 < field_types.len() {
                self.builder.switch_to(next);
            }
        }

        self.builder.switch_to(true_block);
        let t = self.builder.const_u8(1);
        self.builder.jump(merge, vec![t]);
        self.builder.switch_to(false_block);
        let f = self.builder.const_u8(0);
        self.builder.jump(merge, vec![f]);
        self.builder.switch_to(merge);
        merge_param
    }

    /// Compare n slots as raw U64 values (for packed tag unions / Agg).
    pub(super) fn emit_slots_eq(&mut self, lhs: Value, rhs: Value, n: usize) -> Value {
        if n == 0 {
            return self.builder.const_u8(1);
        }
        let false_block = self.builder.create_block();
        let true_block = self.builder.create_block();
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, ScalarType::U8);

        for slot in 0..n {
            let l = self.builder.load(lhs, slot * 8, ScalarType::U64);
            let r = self.builder.load(rhs, slot * 8, ScalarType::U64);
            let eq = self.builder.binop(BinaryOp::Eq, l, r, ScalarType::U8);
            let next = if slot + 1 < n { self.builder.create_block() } else { true_block };
            self.builder.branch(eq, next, vec![], false_block, vec![]);
            if slot + 1 < n { self.builder.switch_to(next); }
        }

        self.builder.switch_to(true_block);
        let t = self.builder.const_u8(1);
        self.builder.jump(merge, vec![t]);
        self.builder.switch_to(false_block);
        let f = self.builder.const_u8(0);
        self.builder.jump(merge, vec![f]);
        self.builder.switch_to(merge);
        merge_param
    }

    /// List equality: compare lengths, then element-by-element.
    pub(super) fn emit_list_eq(&mut self, lhs: Value, rhs: Value, elem_ty: Option<&Type>) -> Value {
        let len_a = self.builder.load(lhs, 0, ScalarType::U64);
        let len_b = self.builder.load(rhs, 0, ScalarType::U64);
        let len_eq = self.builder.binop(BinaryOp::Eq, len_a, len_b, ScalarType::U8);

        let check_elems = self.builder.create_block();
        let check_len_param = self.builder.add_block_param(check_elems, ScalarType::U64);
        let false_block = self.builder.create_block();
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, ScalarType::U8);
        self.builder.branch(len_eq, check_elems, vec![len_a], false_block, vec![]);

        self.builder.switch_to(check_elems);
        let header = self.builder.create_block();
        let i_param = self.builder.add_block_param(header, ScalarType::U64);
        let header_len_param = self.builder.add_block_param(header, ScalarType::U64);
        let body = self.builder.create_block();
        let body_i_param = self.builder.add_block_param(body, ScalarType::U64);
        let body_len_param = self.builder.add_block_param(body, ScalarType::U64);
        let zero = self.builder.const_u64(0);
        self.builder.jump(header, vec![zero, check_len_param]);

        self.builder.switch_to(header);
        let done = self.builder.binop(BinaryOp::Eq, i_param, header_len_param, ScalarType::U8);
        let true_val = self.builder.const_u8(1);
        self.builder.branch(done, merge, vec![true_val], body, vec![i_param, header_len_param]);

        self.builder.switch_to(body);
        // Borrow-only read for element comparison — no rc_inc needed,
        // the elements aren't retained past the comparison.
        let data_a = self.builder.load(lhs, 16, ScalarType::RcPtr);
        let data_b = self.builder.load(rhs, 16, ScalarType::RcPtr);
        let elem_a = self.builder.load_dyn(data_a, body_i_param, ScalarType::RcPtr);
        let elem_b = self.builder.load_dyn(data_b, body_i_param, ScalarType::RcPtr);
        let elem_eq = if let Some(et) = elem_ty {
            if self.is_scalar_eq_type(et) {
                self.builder.binop(BinaryOp::Eq, elem_a, elem_b, ScalarType::U8)
            } else {
                let sub_eq = self.ensure_eq_func(et);
                self.builder.call(&sub_eq, vec![elem_a, elem_b], ScalarType::U8)
            }
        } else {
            self.builder.binop(BinaryOp::Eq, elem_a, elem_b, ScalarType::U8)
        };
        let one = self.builder.const_u64(1);
        let next_i = self.builder.binop(BinaryOp::Add, body_i_param, one, ScalarType::U64);
        self.builder.branch(elem_eq, header, vec![next_i, body_len_param], false_block, vec![]);

        self.builder.switch_to(false_block);
        let false_val = self.builder.const_u8(0);
        self.builder.jump(merge, vec![false_val]);

        self.builder.switch_to(merge);
        merge_param
    }
}
