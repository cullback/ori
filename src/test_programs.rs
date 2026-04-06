use std::collections::HashMap;

use crate::ir::builder::Builder;
use crate::ir::core::{
    Builtin, ConstructorDef, Core, FieldDef, FoldArm, FuncDef, FuncId, NumVal, Pattern, Program,
    Value,
};
use crate::ir::eval::eval;

// -- Test-only helpers --

fn nat(zero: FuncId, succ: FuncId, n: u64) -> Core {
    let mut result = Core::app(zero, vec![]);
    for _ in 0..n {
        result = Core::app(succ, vec![result]);
    }
    result
}

fn list(nil: FuncId, cons: FuncId, items: Vec<Core>) -> Core {
    let mut result = Core::app(nil, vec![]);
    for item in items.into_iter().rev() {
        result = Core::app(cons, vec![item, result]);
    }
    result
}

fn vnum(n: u64) -> Value {
    Value::VNum(NumVal::U64(n))
}

fn vcon(tag: FuncId, fields: Vec<Value>) -> Value {
    Value::VConstruct { tag, fields }
}

fn run(program: &Program) -> Value {
    eval(&HashMap::new(), program, &program.main)
}

// -- Shared type registration helpers --

fn add_nat_type(b: &mut Builder) -> (FuncId, FuncId) {
    let zero = b.func();
    let succ = b.func();
    b.add_type(vec![
        ConstructorDef {
            tag: zero,
            fields: vec![],
        },
        ConstructorDef {
            tag: succ,
            fields: vec![FieldDef { recursive: true }],
        },
    ]);
    (zero, succ)
}

fn add_pair_type(b: &mut Builder) -> FuncId {
    let pair = b.func();
    b.add_type(vec![ConstructorDef {
        tag: pair,
        fields: vec![FieldDef { recursive: false }, FieldDef { recursive: false }],
    }]);
    pair
}

fn add_list_type(b: &mut Builder) -> (FuncId, FuncId) {
    let nil = b.func();
    let cons = b.func();
    b.add_type(vec![
        ConstructorDef {
            tag: nil,
            fields: vec![],
        },
        ConstructorDef {
            tag: cons,
            fields: vec![FieldDef { recursive: false }, FieldDef { recursive: true }],
        },
    ]);
    (nil, cons)
}

fn add_bool_type(b: &mut Builder) -> (FuncId, FuncId) {
    let true_ = b.func();
    let false_ = b.func();
    b.add_type(vec![
        ConstructorDef {
            tag: true_,
            fields: vec![],
        },
        ConstructorDef {
            tag: false_,
            fields: vec![],
        },
    ]);
    (true_, false_)
}

fn add_tree_type(b: &mut Builder) -> (FuncId, FuncId) {
    let leaf = b.func();
    let branch = b.func();
    b.add_type(vec![
        ConstructorDef {
            tag: leaf,
            fields: vec![FieldDef { recursive: false }],
        },
        ConstructorDef {
            tag: branch,
            fields: vec![FieldDef { recursive: true }, FieldDef { recursive: true }],
        },
    ]);
    (leaf, branch)
}

// ============================================================
// Test programs
// ============================================================

/// factorial(5) = 120
#[test]
fn factorial() {
    let mut b = Builder::new();
    let (zero, succ) = add_nat_type(&mut b);
    let pair = add_pair_type(&mut b);
    let add = b.builtin(Builtin::Add);
    let mul = b.builtin(Builtin::Mul);

    let n = b.var();
    let pred = b.var();
    let rec = b.var();
    let idx = b.var();
    let f = b.var();
    let next_i = b.var();
    let result_v = b.var();
    let underscore = b.var();

    let main = Core::let_(
        n,
        nat(zero, succ, 5),
        Core::let_(
            result_v,
            Core::fold(
                Core::var(n),
                vec![
                    FoldArm::new(
                        zero,
                        vec![],
                        vec![],
                        Core::app(pair, vec![Core::u64(0), Core::u64(1)]),
                    ),
                    FoldArm::new(
                        succ,
                        vec![pred],
                        vec![rec],
                        Core::match_(
                            Core::var(rec),
                            vec![(
                                Pattern::con(pair, vec![idx, f]),
                                Core::let_(
                                    next_i,
                                    Core::app(add, vec![Core::var(idx), Core::u64(1)]),
                                    Core::app(
                                        pair,
                                        vec![
                                            Core::var(next_i),
                                            Core::app(mul, vec![Core::var(next_i), Core::var(f)]),
                                        ],
                                    ),
                                ),
                            )],
                        ),
                    ),
                ],
            ),
            Core::match_(
                Core::var(result_v),
                vec![(Pattern::con(pair, vec![underscore, f]), Core::var(f))],
            ),
        ),
    );
    assert_eq!(run(&b.build(main)), vnum(120));
}

/// fib(10) = 55
#[test]
fn fibonacci() {
    let mut b = Builder::new();
    let (zero, succ) = add_nat_type(&mut b);
    let pair = add_pair_type(&mut b);
    let add = b.builtin(Builtin::Add);

    let n = b.var();
    let pred = b.var();
    let rec = b.var();
    let a = b.var();
    let bv = b.var();
    let result_v = b.var();
    let underscore = b.var();

    let main = Core::let_(
        n,
        nat(zero, succ, 10),
        Core::let_(
            result_v,
            Core::fold(
                Core::var(n),
                vec![
                    FoldArm::new(
                        zero,
                        vec![],
                        vec![],
                        Core::app(pair, vec![Core::u64(0), Core::u64(1)]),
                    ),
                    FoldArm::new(
                        succ,
                        vec![pred],
                        vec![rec],
                        Core::match_(
                            Core::var(rec),
                            vec![(
                                Pattern::con(pair, vec![a, bv]),
                                Core::app(
                                    pair,
                                    vec![
                                        Core::var(bv),
                                        Core::app(add, vec![Core::var(a), Core::var(bv)]),
                                    ],
                                ),
                            )],
                        ),
                    ),
                ],
            ),
            Core::match_(
                Core::var(result_v),
                vec![(Pattern::con(pair, vec![a, underscore]), Core::var(a))],
            ),
        ),
    );
    assert_eq!(run(&b.build(main)), vnum(55));
}

/// sum [1,2,3,4,5] = 15
#[test]
fn list_sum() {
    let mut b = Builder::new();
    let (nil, cons) = add_list_type(&mut b);
    let add = b.builtin(Builtin::Add);
    let xs = b.var();
    let hd = b.var();
    let tl = b.var();
    let rec = b.var();

    let main = Core::let_(
        xs,
        list(
            nil,
            cons,
            vec![
                Core::u64(1),
                Core::u64(2),
                Core::u64(3),
                Core::u64(4),
                Core::u64(5),
            ],
        ),
        Core::fold(
            Core::var(xs),
            vec![
                FoldArm::new(nil, vec![], vec![], Core::u64(0)),
                FoldArm::new(
                    cons,
                    vec![hd, tl],
                    vec![rec],
                    Core::app(add, vec![Core::var(hd), Core::var(rec)]),
                ),
            ],
        ),
    );
    assert_eq!(run(&b.build(main)), vnum(15));
}

/// length [1,2,3,4,5] = 5
#[test]
fn list_length() {
    let mut b = Builder::new();
    let (nil, cons) = add_list_type(&mut b);
    let add = b.builtin(Builtin::Add);
    let xs = b.var();
    let hd = b.var();
    let tl = b.var();
    let rec = b.var();

    let main = Core::let_(
        xs,
        list(
            nil,
            cons,
            vec![
                Core::u64(1),
                Core::u64(2),
                Core::u64(3),
                Core::u64(4),
                Core::u64(5),
            ],
        ),
        Core::fold(
            Core::var(xs),
            vec![
                FoldArm::new(nil, vec![], vec![], Core::u64(0)),
                FoldArm::new(
                    cons,
                    vec![hd, tl],
                    vec![rec],
                    Core::app(add, vec![Core::var(rec), Core::u64(1)]),
                ),
            ],
        ),
    );
    assert_eq!(run(&b.build(main)), vnum(5));
}

/// map (+1) [1,2,3] = [2,3,4]
#[test]
fn list_map_inc() {
    let mut b = Builder::new();
    let (nil, cons) = add_list_type(&mut b);
    let add = b.builtin(Builtin::Add);
    let xs = b.var();
    let hd = b.var();
    let tl = b.var();
    let rec = b.var();

    let main = Core::let_(
        xs,
        list(nil, cons, vec![Core::u64(1), Core::u64(2), Core::u64(3)]),
        Core::fold(
            Core::var(xs),
            vec![
                FoldArm::new(nil, vec![], vec![], Core::app(nil, vec![])),
                FoldArm::new(
                    cons,
                    vec![hd, tl],
                    vec![rec],
                    Core::app(
                        cons,
                        vec![
                            Core::app(add, vec![Core::var(hd), Core::u64(1)]),
                            Core::var(rec),
                        ],
                    ),
                ),
            ],
        ),
    );
    let expected = vcon(
        cons,
        vec![
            vnum(2),
            vcon(
                cons,
                vec![vnum(3), vcon(cons, vec![vnum(4), vcon(nil, vec![])])],
            ),
        ],
    );
    assert_eq!(run(&b.build(main)), expected);
}

/// reverse [1,2,3] = [3,2,1]
#[test]
fn list_reverse() {
    let mut b = Builder::new();
    let (nil, cons) = add_list_type(&mut b);
    let append = b.func();

    let xs_p = b.var();
    let x_p = b.var();
    let h2 = b.var();
    let t2 = b.var();
    let r2 = b.var();
    b.add_func(FuncDef {
        name: append,
        params: vec![xs_p, x_p],
        body: Core::fold(
            Core::var(xs_p),
            vec![
                FoldArm::new(
                    nil,
                    vec![],
                    vec![],
                    Core::app(cons, vec![Core::var(x_p), Core::app(nil, vec![])]),
                ),
                FoldArm::new(
                    cons,
                    vec![h2, t2],
                    vec![r2],
                    Core::app(cons, vec![Core::var(h2), Core::var(r2)]),
                ),
            ],
        ),
    });

    let xs = b.var();
    let hd = b.var();
    let tl = b.var();
    let rec = b.var();

    let main = Core::let_(
        xs,
        list(nil, cons, vec![Core::u64(1), Core::u64(2), Core::u64(3)]),
        Core::fold(
            Core::var(xs),
            vec![
                FoldArm::new(nil, vec![], vec![], Core::app(nil, vec![])),
                FoldArm::new(
                    cons,
                    vec![hd, tl],
                    vec![rec],
                    Core::app(append, vec![Core::var(rec), Core::var(hd)]),
                ),
            ],
        ),
    );
    let expected = vcon(
        cons,
        vec![
            vnum(3),
            vcon(
                cons,
                vec![vnum(2), vcon(cons, vec![vnum(1), vcon(nil, vec![])])],
            ),
        ],
    );
    assert_eq!(run(&b.build(main)), expected);
}

/// sum(Branch(Branch(Leaf(1), Leaf(2)), Leaf(3))) = 6
#[test]
fn tree_sum() {
    let mut b = Builder::new();
    let (leaf, branch) = add_tree_type(&mut b);
    let add = b.builtin(Builtin::Add);

    let t = b.var();
    let val = b.var();
    let left = b.var();
    let right = b.var();
    let lr = b.var();
    let rr = b.var();

    let main = Core::let_(
        t,
        Core::app(
            branch,
            vec![
                Core::app(
                    branch,
                    vec![
                        Core::app(leaf, vec![Core::u64(1)]),
                        Core::app(leaf, vec![Core::u64(2)]),
                    ],
                ),
                Core::app(leaf, vec![Core::u64(3)]),
            ],
        ),
        Core::fold(
            Core::var(t),
            vec![
                FoldArm::new(leaf, vec![val], vec![], Core::var(val)),
                FoldArm::new(
                    branch,
                    vec![left, right],
                    vec![lr, rr],
                    Core::app(add, vec![Core::var(lr), Core::var(rr)]),
                ),
            ],
        ),
    );
    assert_eq!(run(&b.build(main)), vnum(6));
}

/// depth(Branch(Branch(Leaf(1), Leaf(2)), Leaf(3))) = 3
#[test]
fn tree_depth() {
    let mut b = Builder::new();
    let (leaf, branch) = add_tree_type(&mut b);
    let add = b.builtin(Builtin::Add);
    let max = b.builtin(Builtin::Max);

    let t = b.var();
    let val = b.var();
    let left = b.var();
    let right = b.var();
    let lr = b.var();
    let rr = b.var();

    let main = Core::let_(
        t,
        Core::app(
            branch,
            vec![
                Core::app(
                    branch,
                    vec![
                        Core::app(leaf, vec![Core::u64(1)]),
                        Core::app(leaf, vec![Core::u64(2)]),
                    ],
                ),
                Core::app(leaf, vec![Core::u64(3)]),
            ],
        ),
        Core::fold(
            Core::var(t),
            vec![
                FoldArm::new(leaf, vec![val], vec![], Core::u64(1)),
                FoldArm::new(
                    branch,
                    vec![left, right],
                    vec![lr, rr],
                    Core::app(
                        add,
                        vec![
                            Core::app(max, vec![Core::var(lr), Core::var(rr)]),
                            Core::u64(1),
                        ],
                    ),
                ),
            ],
        ),
    );
    assert_eq!(run(&b.build(main)), vnum(3));
}

/// is_prime via trial division.
fn is_prime_program(n: u64) -> (Program, FuncId, FuncId) {
    let mut b = Builder::new();
    let (zero, succ) = add_nat_type(&mut b);
    let pair = add_pair_type(&mut b);
    let (true_, false_) = add_bool_type(&mut b);
    let add = b.builtin(Builtin::Add);
    let rem = b.builtin(Builtin::Rem);
    let eq = b.builtin(Builtin::Eq {
        true_con: true_,
        false_con: false_,
    });

    let n_val = b.var();
    let range = b.var();
    let pred = b.var();
    let rec = b.var();
    let d = b.var();
    let p = b.var();
    let next_d = b.var();
    let divisible = b.var();
    let result_v = b.var();
    let underscore = b.var();

    let main = Core::let_(
        n_val,
        Core::u64(n),
        Core::let_(
            range,
            nat(zero, succ, n.saturating_sub(2)),
            Core::let_(
                result_v,
                Core::fold(
                    Core::var(range),
                    vec![
                        FoldArm::new(
                            zero,
                            vec![],
                            vec![],
                            Core::app(pair, vec![Core::u64(2), Core::app(true_, vec![])]),
                        ),
                        FoldArm::new(
                            succ,
                            vec![pred],
                            vec![rec],
                            Core::match_(
                                Core::var(rec),
                                vec![(
                                    Pattern::con(pair, vec![d, p]),
                                    Core::let_(
                                        next_d,
                                        Core::app(add, vec![Core::var(d), Core::u64(1)]),
                                        Core::match_(
                                            Core::var(p),
                                            vec![
                                                (
                                                    Pattern::con(false_, vec![]),
                                                    Core::app(
                                                        pair,
                                                        vec![
                                                            Core::var(next_d),
                                                            Core::app(false_, vec![]),
                                                        ],
                                                    ),
                                                ),
                                                (
                                                    Pattern::con(true_, vec![]),
                                                    Core::let_(
                                                        divisible,
                                                        Core::app(
                                                            eq,
                                                            vec![
                                                                Core::app(
                                                                    rem,
                                                                    vec![
                                                                        Core::var(n_val),
                                                                        Core::var(d),
                                                                    ],
                                                                ),
                                                                Core::u64(0),
                                                            ],
                                                        ),
                                                        Core::match_(
                                                            Core::var(divisible),
                                                            vec![
                                                                (
                                                                    Pattern::con(true_, vec![]),
                                                                    Core::app(
                                                                        pair,
                                                                        vec![
                                                                            Core::var(next_d),
                                                                            Core::app(
                                                                                false_,
                                                                                vec![],
                                                                            ),
                                                                        ],
                                                                    ),
                                                                ),
                                                                (
                                                                    Pattern::con(false_, vec![]),
                                                                    Core::app(
                                                                        pair,
                                                                        vec![
                                                                            Core::var(next_d),
                                                                            Core::app(
                                                                                true_,
                                                                                vec![],
                                                                            ),
                                                                        ],
                                                                    ),
                                                                ),
                                                            ],
                                                        ),
                                                    ),
                                                ),
                                            ],
                                        ),
                                    ),
                                )],
                            ),
                        ),
                    ],
                ),
                Core::match_(
                    Core::var(result_v),
                    vec![(Pattern::con(pair, vec![underscore, p]), Core::var(p))],
                ),
            ),
        ),
    );
    (b.build(main), true_, false_)
}

#[test]
fn is_prime() {
    let check = |n: u64, expected: bool| {
        let (program, true_con, false_con) = is_prime_program(n);
        let expected_tag = if expected { true_con } else { false_con };
        assert_eq!(
            run(&program),
            Value::VConstruct {
                tag: expected_tag,
                fields: vec![]
            },
            "is_prime({n}) should be {expected}"
        );
    };
    check(2, true);
    check(3, true);
    check(4, false);
    check(7, true);
    check(9, false);
    check(11, true);
    check(12, false);
}
