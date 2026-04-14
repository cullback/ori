// Compiler passes, in pipeline order:
//
//   1. syntax::parse     (not here — defines the raw AST too)
//   2. resolve           — resolve imports, build elaborated AST
//   3. fold_lift         — eliminate fold by lifting to top-level helpers
//   4. flatten_patterns  — flatten nested patterns into shallow match chains
//   5. topo              — topological sort, detect cycles (System T)
//   6. types::infer      (not here — lives with the type engine)
//   7. mono              — monomorphize polymorphic functions
//   8. lambda_lift       — lift lambdas to top-level functions
//   9. lambda_solve      — 0-CFA: compute which closures flow where
//  10. lambda_specialize — replace closures with constructors + dispatch
//  11. decl_info         — build metadata tables for lowering
//  12. reachable         — prune unreachable declarations
//  13. ssa::lower        (not here — lives with the SSA IR)

pub mod decl_info;
pub mod flatten_patterns;
pub mod fold_lift;
pub mod lambda_lift;
pub mod lambda_solve;
pub mod lambda_specialize;
pub mod mono;
pub mod reachable;
pub mod resolve;
pub mod topo;
