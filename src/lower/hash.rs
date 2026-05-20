//! Lowering for hash / to_str / string-literal / string-concat
//! operations. These are "derived" operations on user types that
//! the compiler generates SSA for at use sites (rather than as
//! per-type named functions, the way `eq.rs` does).

use crate::ssa::Value;
use crate::ssa::instruction::{BinaryOp, ScalarType};
use crate::types::engine::Type;

use super::LowerCtx;

impl<'a, 'src> LowerCtx<'a, 'src> {
    pub(super) fn emit_scalar_hash(&mut self, value: Value) -> Value {
        let bits = if value.ty == ScalarType::F64 {
            self.builder.bitcast(value, ScalarType::U64)
        } else if value.ty == ScalarType::U64 {
            value
        } else {
            self.builder.cast(value, ScalarType::U64)
        };
        #[expect(clippy::unreadable_literal)]
        let offset = self.builder.const_u64(14695981039346656037);
        let xord = self
            .builder
            .binop(BinaryOp::Xor, offset, bits, ScalarType::U64);
        #[expect(clippy::unreadable_literal)]
        let prime = self.builder.const_u64(1099511628211);
        self.builder.binop(BinaryOp::Mul, xord, prime, ScalarType::U64)
    }

    /// Record hash: FNV-1a over each field in sorted order.
    pub(super) fn lower_record_hash(&mut self, recv: Value, ty: &Type) -> Value {
        let Type::Record { fields, .. } = ty else {
            panic!("lower_record_hash called on non-record type");
        };
        let mut sorted: Vec<(&str, &Type)> = fields.iter().map(|(n, t)| (n.as_str(), t)).collect();
        sorted.sort_by_key(|(n, _)| *n);

        // FNV-1a offset basis
        #[expect(clippy::unreadable_literal)]
        let mut hash = self.builder.const_u64(14695981039346656037);

        for (slot, (_name, field_ty)) in sorted.iter().enumerate() {
            let field_val = self.builder.load(recv, slot * 8, self.scalar_type(field_ty));
            let field_hash = if let Type::Record { .. } = field_ty {
                self.lower_record_hash(field_val, field_ty)
            } else {
                self.emit_scalar_hash(field_val)
            };
            // hash = (hash XOR field_hash) * FNV prime
            hash = self
                .builder
                .binop(BinaryOp::Xor, hash, field_hash, ScalarType::U64);
            #[expect(clippy::unreadable_literal)]
            let prime = self.builder.const_u64(1099511628211);
            hash = self
                .builder
                .binop(BinaryOp::Mul, hash, prime, ScalarType::U64);
        }
        hash
    }

    /// Tuple hash: FNV-1a over each element in order.
    pub(super) fn lower_tuple_hash(&mut self, recv: Value, ty: &Type) -> Value {
        let Type::Tuple(elem_types) = ty else {
            panic!("lower_tuple_hash called on non-tuple type");
        };

        #[expect(clippy::unreadable_literal)]
        let mut hash = self.builder.const_u64(14695981039346656037);

        for (slot, elem_ty) in elem_types.iter().enumerate() {
            let elem_val = self.builder.load(recv, slot * 8, self.scalar_type(elem_ty));
            let elem_hash = if let Type::Record { .. } = elem_ty {
                self.lower_record_hash(elem_val, elem_ty)
            } else if let Type::Tuple(_) = elem_ty {
                self.lower_tuple_hash(elem_val, elem_ty)
            } else {
                self.emit_scalar_hash(elem_val)
            };
            hash = self
                .builder
                .binop(BinaryOp::Xor, hash, elem_hash, ScalarType::U64);
            #[expect(clippy::unreadable_literal)]
            let prime = self.builder.const_u64(1099511628211);
            hash = self
                .builder
                .binop(BinaryOp::Mul, hash, prime, ScalarType::U64);
        }
        hash
    }

    /// Tag union hash: hash the tag index, then the payload fields.
    pub(super) fn lower_tag_hash(&mut self, recv: Value, _ty: &Type) -> Value {
        // Hash the tag index (slot 0) plus the payload (slot 1).
        // This is a simplified version — we treat the payload as
        // an opaque Ptr and hash its address. For full structural
        // hashing of payloads, we'd need to know the payload type
        // per-tag at this point.
        #[expect(clippy::unreadable_literal)]
        let mut hash = self.builder.const_u64(14695981039346656037);

        // Hash the tag index.
        let tag = self.builder.load(recv, 0, ScalarType::U64);
        let tag_hash = self.emit_scalar_hash(tag);
        hash = self
            .builder
            .binop(BinaryOp::Xor, hash, tag_hash, ScalarType::U64);
        #[expect(clippy::unreadable_literal)]
        let prime = self.builder.const_u64(1099511628211);
        hash = self
            .builder
            .binop(BinaryOp::Mul, hash, prime, ScalarType::U64);

        // Hash the payload (slot 1, byte offset 8) — treat as raw value.
        let payload = self.builder.load(recv, 8, ScalarType::RcPtr);
        let payload_hash = self.emit_scalar_hash(payload);
        hash = self
            .builder
            .binop(BinaryOp::Xor, hash, payload_hash, ScalarType::U64);
        #[expect(clippy::unreadable_literal)]
        let prime2 = self.builder.const_u64(1099511628211);
        self.builder
            .binop(BinaryOp::Mul, hash, prime2, ScalarType::U64)
    }

    /// Record to_str: produces `"{ field1: val1, field2: val2 }"`.
    pub(super) fn lower_record_to_str(&mut self, recv: Value, ty: &Type) -> Value {
        let Type::Record { fields, .. } = ty else {
            panic!("lower_record_to_str called on non-record type");
        };
        let mut sorted: Vec<(String, Type)> = fields
            .iter()
            .map(|(n, t)| (n.clone(), t.clone()))
            .collect();
        sorted.sort_by(|(a, _), (b, _)| a.cmp(b));

        // Start with "{ "
        let mut acc = self.lower_str_literal(b"{ ");
        for (i, (name, field_ty)) in sorted.iter().enumerate() {
            if i > 0 {
                let sep = self.lower_str_literal(b", ");
                acc = self.lower_str_concat(acc, sep);
            }
            // "fieldname: "
            let label = format!("{name}: ");
            let label_val = self.lower_str_literal(label.as_bytes());
            acc = self.lower_str_concat(acc, label_val);
            // value.to_str()
            let field_val = self.builder.load(recv, i * 8, self.scalar_type(&field_ty));
            let val_str = if let Type::Record { .. } = &field_ty {
                self.lower_record_to_str(field_val, &field_ty)
            } else if let Type::Con(name) = &field_ty {
                // Dispatch through the type's stdlib `to_str` method.
                let mangled = format!("{name}.to_str");
                self.builder.call(&mangled, vec![field_val], ScalarType::RcPtr)
            } else {
                // Fallback for unhandled cases. Should be unreachable
                // post-mono for primitive-typed record fields.
                self.builder.call("__num_to_str", vec![field_val], ScalarType::RcPtr)
            };
            acc = self.lower_str_concat(acc, val_str);
        }
        // " }"
        let close = self.lower_str_literal(b" }");
        self.lower_str_concat(acc, close)
    }

    /// Helper: emit a string literal as a List(U8) header.
    pub(super) fn lower_str_literal(&mut self, bytes: &[u8]) -> Value {
        let len = bytes.len();
        let data = self.builder.alloc(len * 8);
        for (i, &b) in bytes.iter().enumerate() {
            let val = self.builder.const_u8(b);
            self.builder.store(data, i * 8, val);
        }
        let header = self.builder.alloc(24);
        let len_val = self.builder.const_u64(len as u64);
        self.builder.store(header, 0, len_val);
        self.builder.store(header, 8, len_val);
        self.builder.store(header, 16, data);
        header
    }

    /// Inline string concatenation. Strings are `List(U8)` headers,
    /// so the shape is the same as list append: load len + data from
    /// both sides, alloc a fresh buffer of `a_len + b_len`, byte-copy
    /// each side in, build a new header.
    pub(super) fn lower_str_concat(&mut self, a: Value, b: Value) -> Value {
        let a_len = self.builder.load(a, 0, ScalarType::U64);
        let a_data = self.builder.load(a, 16, ScalarType::RcPtr);
        let b_len = self.builder.load(b, 0, ScalarType::U64);
        let b_data = self.builder.load(b, 16, ScalarType::RcPtr);
        let total = self
            .builder
            .binop(BinaryOp::Add, a_len, b_len, ScalarType::U64);
        let eight = self.builder.const_u64(8);
        let byte_total = self
            .builder
            .binop(BinaryOp::Mul, total, eight, ScalarType::U64);
        let new_data = self.builder.alloc_dyn(byte_total);

        // First copy: new_data[0..a_len] := a_data[0..a_len]
        self.builder.copy_loop(new_data, a_data, a_len, ScalarType::U8);

        // Second copy: new_data[a_len..a_len+b_len] := b_data[0..b_len]
        // Manual loop because dst_idx = a_len + i.
        let header = self.builder.create_block();
        let body = self.builder.create_block();
        let exit = self.builder.create_block();
        let header_i = self.builder.add_block_param(header, ScalarType::U64);
        let body_i = self.builder.add_block_param(body, ScalarType::U64);

        let zero = self.builder.const_u64(0);
        self.builder.jump(header, vec![zero]);

        self.builder.switch_to(header);
        let cond = self
            .builder
            .binop(BinaryOp::Lt, header_i, b_len, ScalarType::U8);
        self.builder.branch(cond, body, vec![header_i], exit, vec![]);

        self.builder.switch_to(body);
        let elem = self.builder.load_dyn(b_data, body_i, ScalarType::U8);
        let dst_idx = self
            .builder
            .binop(BinaryOp::Add, a_len, body_i, ScalarType::U64);
        self.builder.store_dyn(new_data, dst_idx, elem);
        let one = self.builder.const_u64(1);
        let next_i = self
            .builder
            .binop(BinaryOp::Add, body_i, one, ScalarType::U64);
        self.builder.jump(header, vec![next_i]);

        self.builder.switch_to(exit);
        let new_list = self.builder.alloc(24);
        self.builder.store(new_list, 0, total);
        self.builder.store(new_list, 8, total);
        self.builder.store(new_list, 16, new_data);
        new_list
    }
}
