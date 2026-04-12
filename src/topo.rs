//! Topological sort of the top-level function call graph.
//!
//! Runs after `fold_lift` and before inference. Builds a call graph
//! keyed by mangled function name (free functions by bare name,
//! methods by `Type.method`), detects multi-node cycles as System T
//! violations, and reorders `module.decls` so free-function `FuncDef`s
//! appear in dependency order (callees before callers).
//!
//! ## Cycle policy
//!
//! System T forbids user recursion — every loop must come from `fold`
//! or `List.walk*`. The cycle check errors on any cycle with two or
//! more distinct nodes. **Self-cycles** (a function calling itself)
//! are deliberately *not* reported, because `fold_lift` synthesizes
//! recursive helpers like `__fold_N` that call themselves by
//! construction. Detecting user self-recursion cleanly would require
//! distinguishing synthesized helpers from user code, which is a
//! bigger concern for a later step.
//!
//! ## Scope
//!
//! Only free-function `FuncDef`s at the top level are reordered.
//! Methods inside `TypeAnno` blocks and `TypeAnno` decls themselves
//! stay in their original positions — they're set up in inference's
//! registration pass, which doesn't depend on the free-function order.
//!
//! The topo order isn't yet *consumed* by any pass (inference still
//! uses its own two-pass forward-declaration scheme). Step 5 will
//! rework inference to walk in topo order; until then this pass
//! exists for determinism, cycle detection, and as a forcing function
//! for snapshot tests.

use std::collections::{HashMap, HashSet};

use crate::ast::{self, Decl, Expr, ExprKind, Stmt};
use crate::error::CompileError;
use crate::symbol::SymbolTable;

/// Reorder `module.decls` so free-function `FuncDef`s appear in
/// dependency order. Returns `Err` with a "System T violation" message
/// if any non-self cycle is detected.
pub fn compute(module: &mut ast::Module<'_>, symbols: &SymbolTable) -> Result<(), CompileError> {
    let (free_fn_indices, free_fn_names) = collect_free_fns(&module.decls, symbols);
    let graph = build_call_graph(&module.decls, &free_fn_names, symbols);
    detect_cycles(&graph, &free_fn_names)?;
    let order = topo_sort(&graph, &free_fn_names);
    reorder_decls(&mut module.decls, &free_fn_indices, &order, symbols);
    Ok(())
}

// ---- Gathering free functions ----

/// Return (indices, name-set) of free `FuncDef`s in `decls`. The
/// indices are stable positions in `decls`; the name set is used for
/// cheap membership tests when scanning bodies.
fn collect_free_fns(decls: &[Decl<'_>], symbols: &SymbolTable) -> (Vec<usize>, HashSet<String>) {
    let mut indices = Vec::new();
    let mut names = HashSet::new();
    for (i, d) in decls.iter().enumerate() {
        if let Decl::FuncDef { name, .. } = d {
            indices.push(i);
            names.insert(symbols.display(*name).to_owned());
        }
    }
    (indices, names)
}

// ---- Building the call graph ----

/// Build an adjacency map: function name → set of callee names. Only
/// edges whose *target* is a known free function are recorded, so the
/// graph restricts to the free-function subgraph we want to topo-sort.
fn build_call_graph(
    decls: &[Decl<'_>],
    free_fns: &HashSet<String>,
    symbols: &SymbolTable,
) -> HashMap<String, HashSet<String>> {
    // Initialize by walking decls (deterministic order) rather than
    // iterating the HashSet — clippy correctly flags hash iteration
    // but we also want stable graph construction.
    let mut graph: HashMap<String, HashSet<String>> = HashMap::new();
    for d in decls {
        if let Decl::FuncDef { name, .. } = d {
            graph.insert(symbols.display(*name).to_owned(), HashSet::new());
        }
    }
    for d in decls {
        if let Decl::FuncDef { name, body, .. } = d {
            let mut callees = HashSet::new();
            collect_callees(body, &mut callees, symbols);
            // Restrict to free-function targets only.
            callees.retain(|c| free_fns.contains(c));
            let name_str = symbols.display(*name);
            if let Some(edges) = graph.get_mut(name_str) {
                edges.extend(callees);
            }
        }
    }
    graph
}

/// Walk `expr` and push every name that *could* be a function target.
/// Conservative: includes `Call.target`, `QualifiedCall` segments (both
/// the literal join and the resolved name if set), `MethodCall.resolved`
/// if set, and bare `Name` references. Pre-inference `MethodCall`s
/// without a resolution contribute no edges.
fn collect_callees(expr: &Expr<'_>, out: &mut HashSet<String>, symbols: &SymbolTable) {
    match &expr.kind {
        ExprKind::Call { target, args, .. } => {
            out.insert(symbols.display(*target).to_owned());
            for a in args {
                collect_callees(a, out, symbols);
            }
        }
        ExprKind::QualifiedCall {
            segments,
            args,
            resolved,
        } => {
            out.insert(segments.join("."));
            if let Some(r) = resolved {
                out.insert(r.clone());
            }
            // Also push the last segment so imports-via-alias reach the
            // underlying free function. For `math.double(x)`, the raw
            // name is `math.double` which isn't a free-function name,
            // but the imported function itself is declared as `double`.
            // Without this edge, topo-sort would miss the dependency
            // from the caller to `double` and potentially reorder them.
            if let Some(last) = segments.last() {
                out.insert((*last).to_owned());
            }
            for a in args {
                collect_callees(a, out, symbols);
            }
        }
        ExprKind::MethodCall {
            receiver,
            args,
            resolved,
            ..
        } => {
            collect_callees(receiver, out, symbols);
            if let Some(r) = resolved {
                out.insert(r.clone());
            }
            for a in args {
                collect_callees(a, out, symbols);
            }
        }
        ExprKind::Name(sym) => {
            out.insert(symbols.display(*sym).to_owned());
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            collect_callees(lhs, out, symbols);
            collect_callees(rhs, out, symbols);
        }
        ExprKind::Block(stmts, result) => {
            for s in stmts {
                collect_callees_stmt(s, out, symbols);
            }
            collect_callees(result, out, symbols);
        }
        ExprKind::If {
            expr: scrutinee,
            arms,
            else_body,
        } => {
            collect_callees(scrutinee, out, symbols);
            for arm in arms {
                for g in &arm.guards {
                    collect_callees(g, out, symbols);
                }
                collect_callees(&arm.body, out, symbols);
            }
            if let Some(eb) = else_body {
                collect_callees(eb, out, symbols);
            }
        }
        ExprKind::Fold {
            expr: scrutinee,
            arms,
        } => {
            // Present only if topo runs before fold_lift; harmless
            // otherwise because the fold body is still walked.
            collect_callees(scrutinee, out, symbols);
            for arm in arms {
                for g in &arm.guards {
                    collect_callees(g, out, symbols);
                }
                collect_callees(&arm.body, out, symbols);
            }
        }
        ExprKind::Lambda { body, .. } => collect_callees(body, out, symbols),
        ExprKind::Record { fields } => {
            for (_, e) in fields {
                collect_callees(e, out, symbols);
            }
        }
        ExprKind::FieldAccess { record, .. } => collect_callees(record, out, symbols),
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems {
                collect_callees(e, out, symbols);
            }
        }
        ExprKind::Is { expr: inner, .. } => collect_callees(inner, out, symbols),
        ExprKind::RecordUpdate { base, updates } => {
            collect_callees(base, out, symbols);
            for (_, e) in updates {
                collect_callees(e, out, symbols);
            }
        }
        ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) => {}
    }
}

fn collect_callees_stmt(stmt: &Stmt<'_>, out: &mut HashSet<String>, symbols: &SymbolTable) {
    match stmt {
        Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => {
            collect_callees(val, out, symbols);
        }
        Stmt::Guard {
            condition,
            return_val,
        } => {
            collect_callees(condition, out, symbols);
            collect_callees(return_val, out, symbols);
        }
        Stmt::TypeHint { .. } => {}
    }
}

// ---- Cycle detection ----

/// Report the first multi-node cycle found in `graph` as a compile
/// error. Self-loops are ignored (see module docs). Uses iterative DFS
/// with white/gray/black coloring; when a back-edge to a gray node is
/// found, walks the DFS stack to extract the cycle path.
fn detect_cycles(
    graph: &HashMap<String, HashSet<String>>,
    free_fns: &HashSet<String>,
) -> Result<(), CompileError> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Color {
        White,
        Gray,
        Black,
    }

    // Sort names for deterministic traversal order (HashSet iteration
    // is non-deterministic, which would make cycle error messages
    // vary between runs).
    let mut sorted_fns: Vec<&str> = free_fns.iter().map(String::as_str).collect();
    sorted_fns.sort_unstable();

    let mut color: HashMap<&str, Color> = sorted_fns.iter().map(|n| (*n, Color::White)).collect();
    let mut stack: Vec<(&str, Vec<&str>)> = Vec::new();

    for &start in &sorted_fns {
        if color[start] != Color::White {
            continue;
        }
        // `successors` must be sorted for deterministic cycle reports.
        let mut dfs: Vec<(&str, Vec<&str>)> = vec![(start, sorted_children(graph, start))];
        color.insert(start, Color::Gray);
        stack.push((start, Vec::new()));

        while let Some((node, successors)) = dfs.last_mut() {
            let node_name = *node;
            if let Some(next) = successors.pop() {
                if next == node_name {
                    // Self-loop: skip silently.
                    continue;
                }
                match color.get(next).copied().unwrap_or(Color::Black) {
                    Color::White => {
                        color.insert(next, Color::Gray);
                        stack.push((next, Vec::new()));
                        let children = sorted_children(graph, next);
                        dfs.push((next, children));
                    }
                    Color::Gray => {
                        // Found a back-edge `node_name -> next`. Extract
                        // the cycle from the DFS stack.
                        let cycle_start = stack.iter().position(|(n, _)| *n == next).unwrap();
                        let cycle: Vec<&str> =
                            stack[cycle_start..].iter().map(|(n, _)| *n).collect();
                        let chain = cycle.join(" -> ");
                        return Err(CompileError::new(format!(
                            "System T violation: recursive cycle through {chain} -> {next}"
                        )));
                    }
                    Color::Black => {}
                }
            } else {
                color.insert(node_name, Color::Black);
                stack.pop();
                dfs.pop();
            }
        }
    }
    Ok(())
}

/// Return the children of `node` as a sorted vector of `&str`. Sorted
/// order is important for deterministic cycle-report paths.
fn sorted_children<'a>(graph: &'a HashMap<String, HashSet<String>>, node: &str) -> Vec<&'a str> {
    let mut v: Vec<&str> = graph
        .get(node)
        .map(|s| s.iter().map(String::as_str).collect())
        .unwrap_or_default();
    v.sort_unstable();
    // DFS pops from the end, so reverse to visit in alphabetical order.
    v.reverse();
    v
}

// ---- Topological sort ----

/// Return a topological order of `free_fns`. Uses iterative DFS
/// post-order: callees are emitted before callers. Self-loops are
/// treated as absent. Assumes `detect_cycles` already ran so there
/// are no non-self cycles.
fn topo_sort(graph: &HashMap<String, HashSet<String>>, free_fns: &HashSet<String>) -> Vec<String> {
    let mut visited: HashSet<&str> = HashSet::new();
    let mut order: Vec<String> = Vec::new();
    // Sort starts deterministically for stable output across runs.
    let mut starts: Vec<&str> = free_fns.iter().map(String::as_str).collect();
    starts.sort_unstable();
    for start in starts {
        if visited.contains(start) {
            continue;
        }
        dfs_post(start, graph, &mut visited, &mut order);
    }
    order
}

fn dfs_post<'a>(
    node: &'a str,
    graph: &'a HashMap<String, HashSet<String>>,
    visited: &mut HashSet<&'a str>,
    order: &mut Vec<String>,
) {
    if !visited.insert(node) {
        return;
    }
    if let Some(edges) = graph.get(node) {
        let mut sorted: Vec<&str> = edges.iter().map(String::as_str).collect();
        sorted.sort_unstable();
        for next in sorted {
            if next != node {
                dfs_post(next, graph, visited, order);
            }
        }
    }
    order.push(node.to_owned());
}

// ---- Reordering the decl list ----

/// Rewrite `decls` so the free-function `FuncDef`s appear in `order`
/// (with any leftovers appended), while preserving the relative
/// positions of every other decl kind.
///
/// Example: if `decls = [TypeAnno A, FuncDef foo, TypeAnno B, FuncDef bar, FuncDef main]`
/// and `order = ["bar", "foo", "main"]`, the result is
/// `[TypeAnno A, FuncDef bar, TypeAnno B, FuncDef foo, FuncDef main]`.
/// Free-function slots are filled in topo order; every other slot
/// stays where it was.
fn reorder_decls<'src>(
    decls: &mut [Decl<'src>],
    free_fn_indices: &[usize],
    order: &[String],
    symbols: &SymbolTable,
) {
    if free_fn_indices.is_empty() {
        return;
    }
    // Pull out the free FuncDefs into a map from name to decl.
    let mut slot_contents: HashMap<String, Decl<'src>> = HashMap::new();
    for &idx in free_fn_indices {
        let name = if let Decl::FuncDef { name, .. } = &decls[idx] {
            symbols.display(*name).to_owned()
        } else {
            unreachable!("collect_free_fns only records FuncDef indices");
        };
        // Replace with a placeholder; we'll overwrite every slot below.
        let placeholder = std::mem::replace(&mut decls[idx], placeholder_decl());
        slot_contents.insert(name, placeholder);
    }

    // Assemble the ordered list: known names from `order` first, then
    // anything not listed (e.g. unreachable functions that weren't
    // discovered from main). Iterate the leftover map in sorted order
    // for determinism.
    let mut ordered: Vec<Decl<'src>> = Vec::with_capacity(free_fn_indices.len());
    for name in order {
        if let Some(decl) = slot_contents.remove(name) {
            ordered.push(decl);
        }
    }
    let mut leftovers: Vec<(String, Decl<'src>)> = slot_contents.into_iter().collect();
    leftovers.sort_by(|a, b| a.0.cmp(&b.0));
    for (_, decl) in leftovers {
        ordered.push(decl);
    }

    // Write each ordered decl back into its corresponding slot.
    for (slot_idx, decl) in free_fn_indices.iter().zip(ordered) {
        decls[*slot_idx] = decl;
    }
}

/// A dummy decl used while rotating slots during [`reorder_decls`].
/// Never observed from outside the function.
const fn placeholder_decl<'src>() -> Decl<'src> {
    let dummy_span = ast::Span {
        file: crate::source::FileId(0),
        start: 0,
        end: 0,
    };
    Decl::FuncDef {
        span: dummy_span,
        // `SymbolId(u32::MAX)` is a sentinel — `placeholder_decl` is
        // only ever observed inside `reorder_decls` while slots rotate,
        // so this value never escapes back to any consumer.
        name: crate::symbol::SymbolId(u32::MAX),
        params: Vec::new(),
        body: ast::Expr::new(ast::ExprKind::IntLit(0), dummy_span),
        doc: None,
    }
}
