//! Built-in `List` operation lowering. Each function emits the
//! SSA-level primitives that realize the high-level builtin
//! (`append`, `set`, `reverse`, `sublist`, `repeat`, `range`,
//! `get`, `len`). Pure free functions over `Builder` — no
//! `LowerCtx` state needed beyond the builder itself.
//!
//! All loops use 8-byte stride for data buffers (matching the
//! lowering's uniform element representation). Per-Ptr `RcInc` is
//! emitted around element loads when the element type is `Ptr`
//! so the heap refcounts match the eventual cascade.

use crate::ssa::Value;
use crate::ssa::builder::Builder;
use crate::ssa::instruction::{BinaryOp, ScalarType};

pub fn emit_list_builtin_call(
    builder: &mut Builder,
    name: &str,
    args: Vec<Value>,
    elem_ty: ScalarType,
) -> Value {
    if name.ends_with(".len") || name == "List.len" {
        builder.load(args[0], 0, ScalarType::U64)
    } else if name.ends_with(".get") || name == "List.get" {
        emit_list_get_checked(builder, args)
    } else if name.ends_with(".append") || name == "List.append" {
        emit_list_append(builder, args, elem_ty)
    } else if name.ends_with(".range") || name == "List.range" {
        emit_list_range(builder, args)
    } else if name.ends_with(".repeat") || name == "List.repeat" {
        emit_list_repeat(builder, args, elem_ty)
    } else if name.ends_with(".reverse") || name == "List.reverse" {
        emit_list_reverse(builder, args, elem_ty)
    } else if name.ends_with(".sublist") || name == "List.sublist" {
        emit_list_sublist(builder, args, elem_ty)
    } else if name.ends_with(".set") || name == "List.set" {
        emit_list_set(builder, args, elem_ty)
    } else {
        panic!("unknown list builtin: {name}");
    }
}

/// Lower `list.append(val)` as SSA-level primitives: load len + data
/// pointer, alloc new data buffer, copy old elements (with per-Ptr
/// rc_inc when the element type is `Ptr`), store the new element,
/// alloc new header, fill it. All visible to ownership analysis —
/// when the input list is Unique, the new header alloc pairs with
/// the old header for in-place reuse.
fn emit_list_append(builder: &mut Builder, args: Vec<Value>, elem_ty: ScalarType) -> Value {
    use crate::ssa::instruction::BinaryOp;
    let list = args[0];
    let val = args[1];

    let len = builder.load(list, 0, ScalarType::U64);
    let data = builder.load(list, 16, ScalarType::RcPtr);
    let one = builder.const_u64(1);
    let new_len = builder.binop(BinaryOp::Add, len, one, ScalarType::U64);

    // AllocDyn needs total byte count; data buffers use 8-byte stride.
    let elem_size = builder.const_u64(8);
    let new_byte_len = builder.binop(BinaryOp::Mul, new_len, elem_size, ScalarType::U64);
    let new_data = builder.alloc_dyn(new_byte_len);
    builder.copy_loop(new_data, data, len, elem_ty);
    builder.store_dyn(new_data, len, val);

    let new_list = builder.alloc(24);
    builder.store(new_list, 0, new_len);
    builder.store(new_list, 8, new_len);
    builder.store(new_list, 16, new_data);
    new_list
}

/// Lower `xs.set(idx, val)` as FBIP: in-place mutation when xs is
/// unique, copy-on-write otherwise. Runtime decides via `rc == 1`
/// checks inside `ReuseOrClone`/`ReuseOrCloneDyn`.
///
/// The dance:
///   1. `reuse_or_clone(list, 24)` — get a header we own (rc=1).
///      In-place if `list.rc == 1`, fresh clone otherwise.
///   2. Move the data ptr out of the (now-unique) header's slot 16
///      by storing null over it — this prevents the eventual
///      cascade-free of the header from decrementing the data
///      buffer that we're about to mutate.
///   3. `reuse_or_clone_dyn(old_data, len*8)` — get a data buffer
///      we own (rc=1). In-place if data was unique.
///   4. Mutate slot `idx` of the new buffer.
///   5. Store the new buffer back into the header's slot 16.
///
/// When both the list and its data buffer are unique at runtime,
/// this is zero heap allocations: every `reuse_or_clone` takes the
/// in-place path. When either is shared, the runtime clones —
/// correct copy-on-write semantics.
fn emit_list_set(builder: &mut Builder, args: Vec<Value>, _elem_ty: ScalarType) -> Value {
    use crate::ssa::instruction::BinaryOp;
    let list = args[0];
    let idx = args[1];
    let new_val = args[2];

    // Step 1: header — reuse if unique, clone otherwise.
    let new_list = builder.reuse_or_clone(list, 24);

    let len = builder.load(new_list, 0, ScalarType::U64);
    // Step 2: take the data ptr out of the header so reuse_or_clone_dyn
    // sees rc=1 in the in-place path (slot 16's claim transfers to
    // old_data; slot 16 is left null so it won't double-drop).
    let old_data = builder.move_out(new_list, 16, ScalarType::RcPtr);

    // Step 3: data buffer — reuse if unique, clone otherwise.
    let eight = builder.const_u64(8);
    let byte_len = builder.binop(BinaryOp::Mul, len, eight, ScalarType::U64);
    let new_data = builder.reuse_or_clone_dyn(old_data, byte_len);

    // Step 4: replace slot `idx`. StoreDyn auto-releases the previous
    // occupant and auto-claims new_val (for RcPtr-typed slots).
    builder.store_dyn(new_data, idx, new_val);

    // Step 5: install the new buffer in the header.
    builder.store(new_list, 16, new_data);
    new_list
}

/// Lower `xs.reverse()`: builds a new list with elements in reverse
/// order. Loop loads from `i` and stores at `len - 1 - i`, with
/// per-Ptr `RcInc` on each loaded element.
fn emit_list_reverse(builder: &mut Builder, args: Vec<Value>, elem_ty: ScalarType) -> Value {
    use crate::ssa::instruction::BinaryOp;
    let list = args[0];

    let len = builder.load(list, 0, ScalarType::U64);
    let old_data = builder.load(list, 16, ScalarType::RcPtr);
    let eight = builder.const_u64(8);
    let byte_len = builder.binop(BinaryOp::Mul, len, eight, ScalarType::U64);
    let new_data = builder.alloc_dyn(byte_len);

    let header = builder.create_block();
    let body = builder.create_block();
    let exit = builder.create_block();
    let header_i = builder.add_block_param(header, ScalarType::U64);
    let body_i = builder.add_block_param(body, ScalarType::U64);

    let zero = builder.const_u64(0);
    builder.jump(header, vec![zero]);

    builder.switch_to(header);
    let cond = builder.binop(BinaryOp::Lt, header_i, len, ScalarType::U8);
    builder.branch(cond, body, vec![header_i], exit, vec![]);

    builder.switch_to(body);
    // RcPtr-typed loads auto-rc_inc, so the loaded elem is owning.
    let elem = builder.load_dyn(old_data, body_i, elem_ty);
    // dst_idx = len - 1 - i
    let one = builder.const_u64(1);
    let len_minus_one = builder.binop(BinaryOp::Sub, len, one, ScalarType::U64);
    let dst_idx = builder.binop(BinaryOp::Sub, len_minus_one, body_i, ScalarType::U64);
    builder.store_dyn(new_data, dst_idx, elem);
    let next_i = builder.binop(BinaryOp::Add, body_i, one, ScalarType::U64);
    builder.jump(header, vec![next_i]);

    builder.switch_to(exit);
    let new_list = builder.alloc(24);
    builder.store(new_list, 0, len);
    builder.store(new_list, 8, len);
    builder.store(new_list, 16, new_data);
    new_list
}

/// Lower `xs.sublist(start, count)`: copies a contiguous range out of
/// `xs`. Loop loads from `start + i` and stores at `i`, with per-Ptr
/// `RcInc` on each loaded element.
fn emit_list_sublist(builder: &mut Builder, args: Vec<Value>, elem_ty: ScalarType) -> Value {
    use crate::ssa::instruction::BinaryOp;
    let list = args[0];
    let start = args[1];
    let count = args[2];

    let old_data = builder.load(list, 16, ScalarType::RcPtr);
    let eight = builder.const_u64(8);
    let byte_len = builder.binop(BinaryOp::Mul, count, eight, ScalarType::U64);
    let new_data = builder.alloc_dyn(byte_len);

    let header = builder.create_block();
    let body = builder.create_block();
    let exit = builder.create_block();
    let header_i = builder.add_block_param(header, ScalarType::U64);
    let body_i = builder.add_block_param(body, ScalarType::U64);

    let zero = builder.const_u64(0);
    builder.jump(header, vec![zero]);

    builder.switch_to(header);
    let cond = builder.binop(BinaryOp::Lt, header_i, count, ScalarType::U8);
    builder.branch(cond, body, vec![header_i], exit, vec![]);

    builder.switch_to(body);
    let src_idx = builder.binop(BinaryOp::Add, start, body_i, ScalarType::U64);
    // RcPtr-typed loads auto-rc_inc, so the loaded elem is owning.
    let elem = builder.load_dyn(old_data, src_idx, elem_ty);
    builder.store_dyn(new_data, body_i, elem);
    let one = builder.const_u64(1);
    let next_i = builder.binop(BinaryOp::Add, body_i, one, ScalarType::U64);
    builder.jump(header, vec![next_i]);

    builder.switch_to(exit);
    let new_list = builder.alloc(24);
    builder.store(new_list, 0, count);
    builder.store(new_list, 8, count);
    builder.store(new_list, 16, new_data);
    new_list
}

/// Lower `List.repeat(val, count)`: builds a length-`count` list with
/// every slot equal to `val`. For `Ptr` elements, emits an `RcInc`
/// per iteration so the heap refcounts match the eventual cascade.
fn emit_list_repeat(builder: &mut Builder, args: Vec<Value>, elem_ty: ScalarType) -> Value {
    use crate::ssa::instruction::BinaryOp;
    let val = args[0];
    let count = args[1];

    // Allocate the data buffer: count * 8 bytes (uniform stride).
    let eight = builder.const_u64(8);
    let byte_len = builder.binop(BinaryOp::Mul, count, eight, ScalarType::U64);
    let data = builder.alloc_dyn(byte_len);

    // Fill loop.
    let header = builder.create_block();
    let body = builder.create_block();
    let exit = builder.create_block();
    let header_i = builder.add_block_param(header, ScalarType::U64);
    let body_i = builder.add_block_param(body, ScalarType::U64);

    let zero = builder.const_u64(0);
    builder.jump(header, vec![zero]);

    builder.switch_to(header);
    let cond = builder.binop(BinaryOp::Lt, header_i, count, ScalarType::U8);
    builder.branch(cond, body, vec![header_i], exit, vec![]);

    builder.switch_to(body);
    // store_dyn auto-rc_incs val (when val is RcPtr), so the buffer
    // ends up with N owning claims and the caller's local stays valid.
    builder.store_dyn(data, body_i, val);
    let one = builder.const_u64(1);
    let next_i = builder.binop(BinaryOp::Add, body_i, one, ScalarType::U64);
    builder.jump(header, vec![next_i]);

    builder.switch_to(exit);
    let list = builder.alloc(24);
    builder.store(list, 0, count);
    builder.store(list, 8, count);
    builder.store(list, 16, data);
    list
}

/// Lower `List.range(start, end)`: builds a U64 list containing
/// `[start, start+1, ..., end-1]`. Empty when `start >= end`.
///
/// SSA shape: clamp count to zero on underflow via a branch, alloc
/// the data buffer, fill it with a counter loop, alloc the header.
fn emit_list_range(builder: &mut Builder, args: Vec<Value>) -> Value {
    use crate::ssa::instruction::BinaryOp;
    let start = args[0];
    let end = args[1];

    // count = (end > start) ? end - start : 0
    let nonempty = builder.binop(BinaryOp::Gt, end, start, ScalarType::U8);
    let then_block = builder.create_block();
    let else_block = builder.create_block();
    let count_merge = builder.create_block();
    let count = builder.add_block_param(count_merge, ScalarType::U64);
    builder.branch(nonempty, then_block, vec![], else_block, vec![]);

    builder.switch_to(then_block);
    let diff = builder.binop(BinaryOp::Sub, end, start, ScalarType::U64);
    builder.jump(count_merge, vec![diff]);

    builder.switch_to(else_block);
    let zero = builder.const_u64(0);
    builder.jump(count_merge, vec![zero]);

    builder.switch_to(count_merge);
    // data buffer: count * 8 bytes
    let eight = builder.const_u64(8);
    let byte_len = builder.binop(BinaryOp::Mul, count, eight, ScalarType::U64);
    let data = builder.alloc_dyn(byte_len);

    // Fill loop: for i in 0..count: data[i] = start + i.
    let header = builder.create_block();
    let body = builder.create_block();
    let exit = builder.create_block();
    let header_i = builder.add_block_param(header, ScalarType::U64);
    let body_i = builder.add_block_param(body, ScalarType::U64);

    let zero2 = builder.const_u64(0);
    builder.jump(header, vec![zero2]);

    builder.switch_to(header);
    let cond = builder.binop(BinaryOp::Lt, header_i, count, ScalarType::U8);
    builder.branch(cond, body, vec![header_i], exit, vec![]);

    builder.switch_to(body);
    let val = builder.binop(BinaryOp::Add, start, body_i, ScalarType::U64);
    builder.store_dyn(data, body_i, val);
    let one = builder.const_u64(1);
    let next_i = builder.binop(BinaryOp::Add, body_i, one, ScalarType::U64);
    builder.jump(header, vec![next_i]);

    builder.switch_to(exit);
    let list = builder.alloc(24);
    builder.store(list, 0, count);
    builder.store(list, 8, count);
    builder.store(list, 16, data);
    list
}

/// Emit a bounds-checked List.get that returns Result(a, [OutOfBounds]).
/// SSA: load len, compare, branch to Ok(element) or Err(OutOfBounds).
fn emit_list_get_checked(builder: &mut Builder, args: Vec<Value>) -> Value {
    use crate::ssa::instruction::BinaryOp;
    let list = args[0];
    let idx = args[1];

    let len = builder.load(list, 0, ScalarType::U64);
    let in_bounds = builder.binop(BinaryOp::Lt, idx, len, ScalarType::U8);

    let ok_block = builder.create_block();
    let err_block = builder.create_block();
    let merge = builder.create_block();
    let merge_param = builder.add_block_param(merge, ScalarType::RcPtr);

    builder.branch(in_bounds, ok_block, vec![], err_block, vec![]);

    // Ok path: get element, wrap in Ok(elem) = [tag=0, elem]
    builder.switch_to(ok_block);
    let data = builder.load(list, 16, ScalarType::RcPtr);
    // RcPtr load auto-rc_incs, so elem is an owning local that
    // outlives the source list.
    let elem = builder.load_dyn(data, idx, ScalarType::RcPtr);
    let ok_result = builder.alloc(16);
    let ok_tag = builder.const_u64(0);
    builder.store(ok_result, 0, ok_tag);
    builder.store(ok_result, 8, elem);
    builder.jump(merge, vec![ok_result]);

    // Err path: Err(OutOfBounds) = [tag=1, OutOfBounds=tag0]
    builder.switch_to(err_block);
    let err_result = builder.alloc(16);
    let err_tag = builder.const_u64(1);
    builder.store(err_result, 0, err_tag);
    let oob_tag = builder.const_u8(0);
    builder.store(err_result, 8, oob_tag);
    builder.jump(merge, vec![err_result]);

    builder.switch_to(merge);
    merge_param
}
