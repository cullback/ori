// Compiler passes, in pipeline order:
//
//   1. syntax::parse     (not here — defines the raw AST too)
//   2. resolve           — resolve imports, build elaborated AST
//   3. fold_lift         — eliminate fold by lifting to top-level helpers
//   4. flatten_patterns  — flatten nested patterns into shallow match chains
//   5. topo              — topological sort, detect cycles (System T)
//   6. types::infer      (not here — lives with the type engine)
//   7. mono              — monomorphize polymorphic functions
//   8. lambda::*         — defunctionalize closures (4-pass sub-pipeline):
//                          lift → solve → specialize → narrow
//                          See `lambda/README.md` for the model and rationale.
//   9. decl_info         — build metadata tables for lowering
//  10. reachable         — prune unreachable declarations
//  11. ssa::lower        (not here — lives with the SSA IR)

pub mod decl_info;
pub mod flatten_patterns;
pub mod fold_lift;
pub mod lambda;
pub mod mono;
pub mod reachable;
pub mod resolve;
pub mod topo;
