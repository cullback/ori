use std::collections::HashMap;

use crate::ast::{self, BinOp, Decl, Expr, Module, Stmt, TypeExpr};
use crate::builder::Builder;
use crate::ir::{
    Builtin, ConstructorDef, Core, FieldDef, FuncDef, FuncId, Pattern, Program, VarId,
};

/// Lower a parsed AST module into a Core IR program.
///
/// Returns the program and the `VarId` of `main`'s input parameter
/// (a free variable that the runtime must bind before evaluation).
pub fn lower(module: Module) -> (Program, VarId) {
    let mut ctx = LowerCtx::new();

    // Pass 1: register type declarations (introduces constructors) and function names
    for decl in &module.decls {
        match decl {
            Decl::TypeAnno {
                ty: TypeExpr::TagUnion(tags),
                ..
            } => {
                ctx.register_tag_union(tags);
            }
            Decl::TypeAnno { .. } => {}
            Decl::FuncDef { name, .. } => {
                let func_id = ctx.builder.func();
                ctx.funcs.insert(name.clone(), func_id);
            }
        }
    }

    // Pass 2: lower all function bodies
    let mut main_params = None;
    let mut main_body = None;

    for decl in module.decls {
        let Decl::FuncDef { name, params, body } = decl else {
            continue;
        };

        if name == "main" {
            main_params = Some(params);
            main_body = Some(body);
            continue;
        }

        let func_id = ctx.funcs[&name];
        let param_vars: Vec<VarId> = params
            .iter()
            .map(|p| {
                let v = ctx.builder.var();
                ctx.vars.insert(p.clone(), v);
                v
            })
            .collect();
        let body_core = ctx.lower_expr(&body);
        for p in &params {
            ctx.vars.remove(p);
        }
        ctx.builder.add_func(FuncDef {
            name: func_id,
            params: param_vars,
            body: body_core,
        });
    }

    // Lower main
    let params = main_params.expect("no 'main' function defined");
    let body = main_body.unwrap();
    assert!(
        params.len() == 1,
        "main must take exactly one parameter, got {}",
        params.len()
    );

    let input_var = ctx.builder.var();
    ctx.vars.insert(params[0].clone(), input_var);
    let main_core = ctx.lower_expr(&body);
    let program = ctx.builder.build(main_core);
    (program, input_var)
}

struct LowerCtx {
    builder: Builder,
    vars: HashMap<String, VarId>,
    funcs: HashMap<String, FuncId>,
    constructors: HashMap<String, FuncId>,
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
            constructors: HashMap::new(),
            binops,
        }
    }

    fn register_tag_union(&mut self, tags: &[ast::TagDecl]) {
        let mut con_defs = Vec::new();
        for tag in tags {
            let con_id = self.builder.func();
            self.constructors.insert(tag.name.clone(), con_id);
            con_defs.push(ConstructorDef {
                tag: con_id,
                fields: tag
                    .fields
                    .iter()
                    .map(|_| FieldDef { recursive: false })
                    .collect(),
            });
        }
        self.builder.add_type(con_defs);
    }

    fn lower_expr(&mut self, expr: &Expr) -> Core {
        match expr {
            Expr::IntLit(n) => Core::i64(*n),

            Expr::Name(name) => {
                if let Some(&var_id) = self.vars.get(name) {
                    return Core::var(var_id);
                }
                if let Some(&con_id) = self.constructors.get(name) {
                    return Core::app(con_id, vec![]);
                }
                panic!("undefined name: {name}");
            }

            Expr::BinOp { op, lhs, rhs } => {
                let func_id = self.binops[op];
                Core::app(func_id, vec![self.lower_expr(lhs), self.lower_expr(rhs)])
            }

            Expr::Call { func, args } => {
                let func_id = if let Some(&con_id) = self.constructors.get(func) {
                    con_id
                } else if let Some(&fn_id) = self.funcs.get(func) {
                    fn_id
                } else {
                    panic!("undefined function or constructor: {func}");
                };
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

            Expr::If {
                expr: scrutinee_expr,
                arms,
                ..
            } => {
                let scrutinee = self.lower_expr(scrutinee_expr);
                let core_arms: Vec<(Pattern, Core)> = arms
                    .iter()
                    .map(|arm| {
                        let (pat, var_bindings) = self.lower_pattern(&arm.pattern);
                        for (name, var_id) in &var_bindings {
                            self.vars.insert(name.clone(), *var_id);
                        }
                        let body = self.lower_expr(&arm.body);
                        for (name, _) in &var_bindings {
                            self.vars.remove(name);
                        }
                        (pat, body)
                    })
                    .collect();
                Core::match_(scrutinee, core_arms)
            }
        }
    }

    fn lower_pattern(&mut self, pat: &ast::Pattern) -> (Pattern, Vec<(String, VarId)>) {
        match pat {
            ast::Pattern::Constructor { name, fields } => {
                let con_id = *self
                    .constructors
                    .get(name)
                    .unwrap_or_else(|| panic!("unknown constructor in pattern: {name}"));
                let mut field_vars = Vec::new();
                let mut bindings = Vec::new();
                for field_pat in fields {
                    match field_pat {
                        ast::Pattern::Binding(binding_name) => {
                            let var_id = self.builder.var();
                            field_vars.push(var_id);
                            bindings.push((binding_name.clone(), var_id));
                        }
                        ast::Pattern::Wildcard => {
                            let var_id = self.builder.var();
                            field_vars.push(var_id);
                        }
                        ast::Pattern::Constructor { .. } => {
                            panic!("nested constructor patterns not yet supported");
                        }
                    }
                }
                (Pattern::con(con_id, field_vars), bindings)
            }
            ast::Pattern::Wildcard | ast::Pattern::Binding(_) => {
                panic!("top-level wildcard/binding patterns not yet supported in match arms");
            }
        }
    }
}
