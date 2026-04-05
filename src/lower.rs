use std::collections::HashMap;

use crate::ast::{BinOp, Decl, Expr, Module, Stmt};
use crate::builder::Builder;
use crate::ir::{Builtin, Core, FuncId, Program, VarId};

/// Lower a parsed AST module into a Core IR program.
///
/// Returns the program and the `VarId` of `main`'s input parameter
/// (a free variable that the runtime must bind before evaluation).
pub fn lower(module: Module) -> (Program, VarId) {
    let mut ctx = LowerCtx::new();

    // Find the main function definition
    let mut main_def = None;
    for decl in module.decls {
        match decl {
            Decl::TypeAnno { .. } => {} // ignored for v0.1
            Decl::FuncDef { name, params, body } => {
                if name == "main" {
                    main_def = Some((params, body));
                }
            }
        }
    }

    let (params, body) = main_def.expect("no 'main' function defined");
    assert!(
        params.len() == 1,
        "main must take exactly one parameter, got {}",
        params.len()
    );

    // Create the input variable for main's parameter
    let input_var = ctx.builder.var();
    ctx.vars.insert(params[0].clone(), input_var);

    // Lower the body — it becomes program.main with input_var as a free variable
    let main_core = ctx.lower_expr(&body);
    let program = ctx.builder.build(main_core);
    (program, input_var)
}

struct LowerCtx {
    builder: Builder,
    vars: HashMap<String, VarId>,
    funcs: HashMap<String, FuncId>,
    binops: HashMap<BinOp, FuncId>,
}

impl LowerCtx {
    fn new() -> Self {
        let mut builder = Builder::new();
        let mut binops = HashMap::new();

        binops.insert(BinOp::Add, builder.builtin(Builtin::Add));
        binops.insert(BinOp::Sub, builder.builtin(Builtin::Sub));
        binops.insert(BinOp::Mul, builder.builtin(Builtin::Mul));
        binops.insert(BinOp::Div, builder.builtin(Builtin::Mul)); // TODO: add Div builtin
        binops.insert(BinOp::Rem, builder.builtin(Builtin::Rem));

        Self {
            builder,
            vars: HashMap::new(),
            funcs: HashMap::new(),
            binops,
        }
    }

    fn lower_expr(&mut self, expr: &Expr) -> Core {
        match expr {
            Expr::IntLit(n) => Core::i64(*n),

            Expr::Var(name) => {
                let var_id = *self
                    .vars
                    .get(name)
                    .unwrap_or_else(|| panic!("undefined variable: {name}"));
                Core::var(var_id)
            }

            Expr::BinOp { op, lhs, rhs } => {
                let func_id = self.binops[op];
                Core::app(func_id, vec![self.lower_expr(lhs), self.lower_expr(rhs)])
            }

            Expr::Call { func, args } => {
                let func_id = *self
                    .funcs
                    .get(func)
                    .unwrap_or_else(|| panic!("undefined function: {func}"));
                let arg_cores: Vec<Core> = args.iter().map(|a| self.lower_expr(a)).collect();
                Core::app(func_id, arg_cores)
            }

            Expr::Block(stmts, result) => {
                let mut bindings = Vec::new();
                for stmt in stmts {
                    let Stmt::Let { name, val } = stmt;
                    let val_core = self.lower_expr(val);
                    let var_id = self.builder.var();
                    self.vars.insert(name.clone(), var_id);
                    bindings.push((var_id, val_core));
                }

                let mut result_core = self.lower_expr(result);
                for (var_id, val_core) in bindings.into_iter().rev() {
                    result_core = Core::let_(var_id, val_core, result_core);
                }

                result_core
            }
        }
    }
}
