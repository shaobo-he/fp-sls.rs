//! The expression evaluator. Port of `data/eval.rkt`.
//!
//! Evaluates a (let-/var-containing) term against an [`Assignment`]. Variable
//! resolution goes through `env` (a stack of `let` bindings) and then the
//! assignment, mirroring the Racket evaluator whose `env` is seeded from the
//! whole assignment.
//!
//! NOTE: the Racket `eval^`'s `let` case called `eval` with two arguments
//! instead of three — an arity bug that crashes whenever a `let` survives inside
//! a term operand. This port implements the obviously-intended behaviour.

use crate::data::bitvec::BitVec;
use crate::data::fp::FloatingPoint;
use crate::data::value::{Assignment, Value};
use crate::sexp::Sexp;
use rug::Integer;

/// `(get-value assignment sym)`.
pub fn get_value<'a>(asn: &'a Assignment, sym: &str) -> &'a Value {
    asn.get(sym)
        .unwrap_or_else(|| panic!("symbol not found: {sym}"))
}

fn lookup(sym: &str, asn: &Assignment, env: &[(String, Value)]) -> Value {
    for (k, v) in env.iter().rev() {
        if k == sym {
            return v.clone();
        }
    }
    match asn.get(sym) {
        Some(v) => v.clone(),
        None => panic!("symbol not found during evaluation! {sym}"),
    }
}

fn as_bv(v: Value) -> BitVec {
    match v {
        Value::BV(b) => b,
        Value::FP(_) => panic!("expected a bit-vector operand"),
    }
}
fn as_fp(v: Value) -> FloatingPoint {
    match v {
        Value::FP(f) => f,
        Value::BV(_) => panic!("expected a floating-point operand"),
    }
}

/// Evaluate `be` under `asn` with `let`-binding stack `env`.
pub fn eval(be: &Sexp, asn: &Assignment, env: &[(String, Value)]) -> Value {
    match be {
        Sexp::BV(b) => Value::BV(b.clone()),
        Sexp::FP(f) => Value::FP(f.clone()),
        Sexp::Sym(s) => lookup(s, asn, env),
        Sexp::Int(_) => panic!("cannot evaluate a bare numeral"),
        Sexp::List(items) => eval_list(items, asn, env),
    }
}

fn eval_list(items: &[Sexp], asn: &Assignment, env: &[(String, Value)]) -> Value {
    // `let`: extend the environment, then evaluate the body.
    if items[0].is_sym("let") {
        let bindings = items[1].as_list().expect("let bindings");
        let mut new_env: Vec<(String, Value)> = env.to_vec();
        for b in bindings {
            let pair = b.as_list().expect("binding pair");
            let name = pair[0].as_sym().expect("binding name").to_string();
            let val = eval(&pair[1], asn, &new_env);
            new_env.push((name, val));
        }
        return eval(&items[2], asn, &new_env);
    }

    // Indexed identifier head: `((_ to_fp ne ns) rm op)` — FP→FP conversion.
    if let Sexp::List(h) = &items[0] {
        if h.len() == 4 && h[0].is_sym("_") && h[1].is_sym("to_fp") && items.len() == 3 {
            let ne = h[2].as_u32().expect("to_fp exp width");
            let ns = h[3].as_u32().expect("to_fp sig width");
            let op = as_fp(eval(&items[2], asn, env));
            return Value::FP(op.fpconv(ne, ns));
        }
        panic!("unsupported operation: {}", Sexp::List(items.to_vec()));
    }

    let head = items[0].as_sym().expect("operator symbol");
    let bv = |i: usize| as_bv(eval(&items[i], asn, env));
    let fp = |i: usize| as_fp(eval(&items[i], asn, env));

    match head {
        // bit-vector arithmetic / bitwise
        "bvneg" => Value::BV(bv(1).bvneg()),
        "bvadd" => Value::BV(bv(1).bvadd(&bv(2))),
        "bvsub" => Value::BV(bv(1).bvsub(&bv(2))),
        "bvmul" => Value::BV(bv(1).bvmul(&bv(2))),
        "bvudiv" => Value::BV(bv(1).bvudiv(&bv(2))),
        "bvurem" => Value::BV(bv(1).bvurem(&bv(2))),
        "bvnot" => Value::BV(bv(1).bvnot()),
        "bvand" => Value::BV(bv(1).bvand(&bv(2))),
        "bvor" => Value::BV(bv(1).bvor(&bv(2))),

        // bit-vector constant `(_ bvN w)`
        "_" => {
            let name = items[1].as_sym().expect("bv constant name");
            let n = Integer::from_str_radix(&name[2..], 10).expect("bv numeral");
            let w = items[2].as_u32().expect("bv width");
            Value::BV(BitVec::new(w, n))
        }

        // floating-point arithmetic — first operand of binops is the rounding mode
        "fp.add" => Value::FP(fp(2).fpadd(&fp(3))),
        "fp.sub" => Value::FP(fp(2).fpsub(&fp(3))),
        "fp.mul" => Value::FP(fp(2).fpmul(&fp(3))),
        "fp.div" => Value::FP(fp(2).fpdiv(&fp(3))),
        "fp.neg" => Value::FP(fp(1).fpneg()),
        "fp.sqrt" => Value::FP(fp(2).fpsqrt()),

        // floating-point predicates (yield width-1 bit-vectors)
        "fp.isNormal" => Value::BV(BitVec::from_bool(fp(1).is_normal())),
        "fp.isSubnormal" => Value::BV(BitVec::from_bool(fp(1).is_subnormal())),
        "fp.isZero" => Value::BV(BitVec::from_bool(fp(1).is_zero())),
        "fp.isPositive" => Value::BV(BitVec::from_bool(fp(1).is_positive())),
        "fp.isNaN" => Value::BV(BitVec::from_bool(fp(1).is_nan())),
        "fp.isInfinite" => Value::BV(BitVec::from_bool(fp(1).is_infinity())),

        _ => panic!("unsupported operation: {}", Sexp::List(items.to_vec())),
    }
}
