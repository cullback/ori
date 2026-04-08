use crate::core::Program;
use crate::ssa::Module;

/// Lower a Core Program to a low-level SSA Module.
///
/// This is where representation decisions happen:
/// - Tag unions → tag byte + payload at known offsets
/// - Records → flat struct layout
/// - Lists → (len, cap, data_ptr) buffers
/// - Reference counting inserted
pub fn lower(_program: &Program, _input_vars: &[crate::core::VarId]) -> Module {
    todo!("Core → low-level SSA lowering (needs type layout computation)")
}
