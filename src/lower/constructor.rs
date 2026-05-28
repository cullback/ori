//! Tag-union constructor lowering. Each constructor call becomes
//! either a fieldless discriminant constant or a heap allocation
//! shaped as `[tag, field0, field1, ...]`.
//!
//! Two flavors of constructors share this code:
//! - Declared constructors come from `TypeAnno` declarations and
//!   have a stored `ConstructorMeta` (in decl_info).
//! - Structural constructors are conjured by the AST pre-pass for
//!   uppercase names not in any declaration; their layout is
//!   computed from the inferred TagUnion context via
//!   `structural_con_layout`.

use std::collections::HashMap;

use crate::passes::decl_info::resolve_scalar_type;
use crate::ssa::Value;
use crate::ssa::instruction::ScalarType;
use crate::types::engine::Type;

use super::LowerCtx;

impl<'a, 'src> LowerCtx<'a, 'src> {
    pub(super) fn specialize_con_fields(&self, con_name: &str, ctx_ty: &Type) -> Option<Vec<ScalarType>> {
        let scheme = self.decls.constructor_schemes.get(con_name)?;
        let Type::Arrow(params, ret) = &scheme.ty else {
            return None;
        };
        let resolved_ctx = self.resolve_transparent(ctx_ty);
        let (scheme_args, ctx_args) = match (ret.as_ref(), &resolved_ctx) {
            (Type::App(sn, sa), Type::App(cn, ca)) if sn == cn && sa.len() == ca.len() => {
                (sa, ca)
            }
            (Type::Con(sn), Type::Con(cn)) if sn == cn => {
                return Some(
                    params.iter().map(|p| self.scalar_type(p)).collect(),
                );
            }
            // Scheme's return is a bare TagUnion (unusual) or shapes
            // don't line up — punt to the caller's fallback.
            _ => return None,
        };
        let mut specialized_params: Vec<Type> = params.to_vec();
        for (sa, ca) in scheme_args.iter().zip(ctx_args) {
            if let Type::Var(v) = sa {
                specialized_params = specialized_params
                    .iter()
                    .map(|p| super::substitute_type_var(p, *v, ca))
                    .collect();
            }
        }
        Some(specialized_params.iter().map(|p| self.scalar_type(p)).collect())
    }

    pub(super) fn con_layout(
        &self,
        name: &str,
        ctx_ty: Option<&Type>,
    ) -> (u64, usize, Vec<ScalarType>) {
        // Field types stored in `decl_info.constructors` come from the
        // polymorphic declared scheme, so a generic parameter like `ok`
        // in `Ok : ok -> Result(ok, err)` resolves to `Ptr`. The
        // monomorphized call site knows the concrete payload types via
        // `ctx_ty`; use them to override, while keeping the declared
        // meta's tag_index (declaration order) and max_fields.
        let specialized = ctx_ty.and_then(|ty| self.specialize_con_fields(name, ty));
        if let Some(meta) = self.decls.constructors.get(name) {
            let fields = specialized.unwrap_or_else(|| meta.field_types.clone());
            return (meta.tag_index, meta.max_fields, fields);
        }
        let ty = ctx_ty.unwrap_or_else(|| {
            panic!("structural constructor '{name}' without context type")
        });
        structural_con_layout(ty, name, &self.decls.fieldless_tags)
    }

    // ---- Constructor call emission ----

    /// Emit a constructor call. `ctx_ty` is the type of the
    /// enclosing expression — used to compute layout for
    /// structural constructors (which don't have entries in
    /// `decl_info.constructors`). For declared constructors the
    /// `ctx_ty` is ignored and `ConstructorMeta` is used directly.
    pub(super) fn lower_constructor_call(
        &mut self,
        name: &str,
        args: &[Value],
        ctx_ty: Option<&Type>,
    ) -> Value {
        let lv = self.lower_constructor_call_lv(name, args, ctx_ty);
        let ty = ctx_ty.cloned().unwrap_or_else(|| {
            // Best-effort: caller didn't supply a context type. Use
            // a placeholder; only the materialize fallback uses this.
            crate::types::engine::Type::Con("__none".to_owned())
        });
        self.materialize_lv(lv, &ty)
    }

    /// LV-returning variant. Non-fieldless tag unions decompose to
    /// `Multi(tag, payload_ptr)`: the tag lives in a register and the
    /// payload heap object holds only the variant-specific fields
    /// (no tag slot inside). Void variants in a non-fieldless union
    /// use a null payload pointer. Fieldless unions stay as a bare
    /// discriminant integer.
    pub(super) fn lower_constructor_call_lv(
        &mut self,
        name: &str,
        args: &[Value],
        ctx_ty: Option<&Type>,
    ) -> super::lowered_value::LoweredValue {
        let (tag_index, max_fields, _field_types) = self.con_layout(name, ctx_ty);
        if max_fields == 0 {
            let disc_ty = ctx_ty
                .map(|t| self.scalar_type(t))
                .unwrap_or(ScalarType::U8);
            return super::lowered_value::LoweredValue::single(
                self.const_tag(tag_index, disc_ty),
            );
        }
        // Phase E: single-variant tag unions skip both the tag and
        // the payload heap object — the variant is implicit and
        // fields flow as parallel SSA Values. Closures with captures
        // land here.
        if let Some(ty) = ctx_ty {
            if self.is_single_variant_tag_union(ty) {
                return super::lowered_value::LoweredValue::Multi(args.to_vec());
            }
        }
        // D2 multi-variant: tag in register, fields in payload heap.
        let tag = self.builder.const_u64(tag_index);
        let payload = if args.is_empty() {
            self.builder.const_ptr_null()
        } else {
            let payload_ptr = self.builder.alloc(args.len() * 8);
            for (i, &arg) in args.iter().enumerate() {
                self.builder.store(payload_ptr, i * 8, arg);
            }
            payload_ptr
        };
        super::lowered_value::LoweredValue::Multi(vec![tag, payload])
    }
}

/// `Type::TagUnion` context. Returns `(tag_index, max_fields,
/// field_scalar_types)`. Tag index is the constructor's position in
/// the tag list sorted by name (dense, 0..N). Max fields is the
/// maximum payload arity across all tags in the union. Payload scalar
/// types are computed from the constructor's payload types in the
/// sorted union.
///
/// Panics if `ty` isn't a closed `Type::TagUnion` or if `con_name`
/// isn't present among its tags — both are bugs in earlier passes
/// that should have been caught by inference/mono.
pub fn structural_con_layout(
    ty: &Type,
    con_name: &str,
    fieldless: &HashMap<String, ScalarType>,
) -> (u64, usize, Vec<ScalarType>) {
    let Type::TagUnion { tags, rest } = ty else {
        panic!(
            "structural constructor '{con_name}' expected TagUnion context, got {ty:?}"
        );
    };
    assert!(
        rest.is_none(),
        "structural constructor '{con_name}' context has open row — mono should have closed it"
    );
    let mut sorted: Vec<(String, Vec<Type>)> = tags.clone();
    sorted.sort_by(|a, b| a.0.cmp(&b.0));
    let max_fields = sorted.iter().map(|(_, p)| p.len()).max().unwrap_or(0);
    let idx = sorted
        .iter()
        .position(|(n, _)| n == con_name)
        .unwrap_or_else(|| {
            panic!("structural constructor '{con_name}' not in union {tags:?}")
        });
    #[allow(clippy::cast_possible_truncation, reason = "tag count fits in u64")]
    let tag_index = idx as u64;
    let field_types: Vec<ScalarType> = sorted[idx]
        .1
        .iter()
        .map(|t| resolve_scalar_type(t, fieldless))
        .collect();
    (tag_index, max_fields, field_types)
}
