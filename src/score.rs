//! Scoring. Port of `score.rkt`.
//!
//! The score of a formula under an assignment is a value in `[0, 1]`, equal to
//! 1 exactly when the formula is satisfied. Following the paper, conjunctions
//! average and disjunctions take the maximum; (in)equalities degrade smoothly
//! with a distance metric scaled by the constant `c`.
//!
//! All scores are exact rationals (`rug::Rational`) — this realizes the Racket
//! TODO "add types to score functions (they should be rational rather than
//! floating point)".
//!
//! Two fixes relative to the Racket original:
//!   * positive `fp.gt` now threads `env` (the Racket `score` clause dropped it,
//!     an arity bug that crashed on any un-negated `fp.gt`);
//!   * scores are exact rationals rather than inexact flonums.

// The FP predicate scores below deliberately keep each paper case clause
// separate even when two clauses return the same constant (e.g. NaN ⇒ 1 and
// `≥` holds ⇒ 1), mirroring the case analysis in score.rkt.
#![allow(clippy::if_same_then_else)]

use crate::data::bitvec::{two_pow, BitVec};
use crate::data::eval::eval;
use crate::data::fp::FloatingPoint;
use crate::data::value::{Assignment, Value};
use crate::sexp::Sexp;
use rug::{Integer, Rational};

type R = Rational;

fn one() -> R {
    R::from(1)
}
fn zero() -> R {
    R::from(0)
}
fn rmax(a: R, b: R) -> R {
    if a >= b {
        a
    } else {
        b
    }
}

// ---------- distance-based scores ----------

/// `c · (1 - dist/2^width)`, with `dist = |v1 - v2| + [eq]`.
fn bv_dist_score(c: &R, bv1: &BitVec, bv2: &BitVec, eq: bool) -> R {
    let mut dist = Integer::from(&bv1.value - &bv2.value).abs();
    if eq {
        dist += 1;
    }
    c * (one() - R::from((dist, two_pow(bv1.width))))
}

/// `(Hamming-distance …)`-based equality score for bit-vectors.
fn score_bv_eq(c: &R, bv1: &BitVec, bv2: &BitVec) -> R {
    if bv1.bv_eq(bv2) {
        one()
    } else {
        let h = bv1.hamming_distance(bv2);
        c * (one() - R::from((Integer::from(h), Integer::from(bv1.width))))
    }
}

fn score_bv_ne(bv1: &BitVec, bv2: &BitVec) -> R {
    if bv1.bv_eq(bv2) {
        zero()
    } else {
        one()
    }
}

/// `(get/fp-pos fp)` — a signed-magnitude position used for FP distances.
fn get_fp_pos(fp: &FloatingPoint) -> Integer {
    let bv = fp.to_bitvec().value;
    if fp.is_positive() {
        bv
    } else {
        let half = two_pow(fp.exp_width + fp.sig_width - 1);
        -(bv - half)
    }
}

fn fp_dist_score(c: &R, fp1: &FloatingPoint, fp2: &FloatingPoint, eq: bool) -> R {
    let mut dist = (get_fp_pos(fp1) - get_fp_pos(fp2)).abs();
    if eq {
        dist += 1;
    }
    let den = two_pow(fp1.exp_width + fp2.sig_width);
    c * (one() - R::from((dist, den)))
}

// ---------- equality / inequality ----------

fn score_fp_eq_raw(c: &R, fp1: &FloatingPoint, fp2: &FloatingPoint) -> R {
    if fp1.is_nan() && fp2.is_nan() {
        one()
    } else if fp1.is_nan() || fp2.is_nan() {
        zero()
    } else if fp1.to_bitvec().bv_eq(&fp2.to_bitvec()) {
        one()
    } else {
        fp_dist_score(c, fp1, fp2, false)
    }
}

fn score_fp_ne_raw(fp1: &FloatingPoint, fp2: &FloatingPoint) -> R {
    if fp1.is_nan() && fp2.is_nan() {
        zero()
    } else if fp1.is_nan() || fp2.is_nan() {
        one()
    } else {
        score_bv_ne(&fp1.to_bitvec(), &fp2.to_bitvec())
    }
}

fn score_eq(c: &R, v1: &Value, v2: &Value) -> R {
    match (v1, v2) {
        (Value::BV(a), Value::BV(b)) => score_bv_eq(c, a, b),
        (Value::FP(a), Value::FP(b)) => score_fp_eq_raw(c, a, b),
        _ => panic!("type mismatch in ="),
    }
}

fn score_ne(v1: &Value, v2: &Value) -> R {
    match (v1, v2) {
        (Value::BV(a), Value::BV(b)) => score_bv_ne(a, b),
        (Value::FP(a), Value::FP(b)) => score_fp_ne_raw(a, b),
        _ => panic!("type mismatch in ≠"),
    }
}

// `fp.eq` / `¬fp.eq`: IEEE equality, which makes ±0 equal and any-NaN unequal.
fn score_fpeq(c: &R, fp1: &FloatingPoint, fp2: &FloatingPoint) -> R {
    if fp1.is_nan() || fp2.is_nan() {
        zero()
    } else if fp1.is_zero() && fp2.is_zero() {
        one()
    } else {
        score_fp_eq_raw(c, fp1, fp2)
    }
}

fn score_fp_not_eq(fp1: &FloatingPoint, fp2: &FloatingPoint) -> R {
    if fp1.is_nan() || fp2.is_nan() {
        one()
    } else if fp1.is_zero() && fp2.is_zero() {
        zero()
    } else {
        score_bv_ne(&fp1.to_bitvec(), &fp2.to_bitvec())
    }
}

// ---------- bit-vector ordering ----------

fn score_bv_lt(c: &R, bv1: &BitVec, bv2: &BitVec) -> R {
    if bv1.bv_lt(bv2) {
        one()
    } else {
        bv_dist_score(c, bv1, bv2, true)
    }
}

fn score_bv_ge(c: &R, bv1: &BitVec, bv2: &BitVec) -> R {
    if bv1.bv_ge(bv2) {
        one()
    } else {
        bv_dist_score(c, bv1, bv2, false)
    }
}

// ---------- floating-point ordering ----------
// Each predicate has a score and a score for its negation; NaN makes the
// predicate fail (score 0) and its negation hold (score 1).

fn score_fplt(c: &R, a: &FloatingPoint, b: &FloatingPoint) -> R {
    if a.is_nan() || b.is_nan() {
        zero()
    } else if a.fp_lt(b) {
        one()
    } else {
        fp_dist_score(c, a, b, true)
    }
}
fn score_fp_not_lt(c: &R, a: &FloatingPoint, b: &FloatingPoint) -> R {
    if a.is_nan() || b.is_nan() {
        one()
    } else if a.fp_ge(b) {
        one()
    } else {
        fp_dist_score(c, a, b, false)
    }
}
fn score_fpleq(c: &R, a: &FloatingPoint, b: &FloatingPoint) -> R {
    if a.is_nan() || b.is_nan() {
        zero()
    } else if a.fp_le(b) {
        one()
    } else {
        fp_dist_score(c, a, b, false)
    }
}
fn score_fp_not_leq(c: &R, a: &FloatingPoint, b: &FloatingPoint) -> R {
    if a.is_nan() || b.is_nan() {
        one()
    } else if a.fp_gt(b) {
        one()
    } else {
        fp_dist_score(c, a, b, true)
    }
}
fn score_fpgt(c: &R, a: &FloatingPoint, b: &FloatingPoint) -> R {
    if a.is_nan() || b.is_nan() {
        zero()
    } else if a.fp_gt(b) {
        one()
    } else {
        fp_dist_score(c, a, b, true)
    }
}
fn score_fp_not_gt(c: &R, a: &FloatingPoint, b: &FloatingPoint) -> R {
    if a.is_nan() || b.is_nan() {
        one()
    } else if a.fp_le(b) {
        one()
    } else {
        fp_dist_score(c, a, b, false)
    }
}
fn score_fpgeq(c: &R, a: &FloatingPoint, b: &FloatingPoint) -> R {
    if a.is_nan() || b.is_nan() {
        zero()
    } else if a.fp_ge(b) {
        one()
    } else {
        fp_dist_score(c, a, b, false)
    }
}
fn score_fp_not_geq(c: &R, a: &FloatingPoint, b: &FloatingPoint) -> R {
    if a.is_nan() || b.is_nan() {
        one()
    } else if a.fp_lt(b) {
        one()
    } else {
        fp_dist_score(c, a, b, true)
    }
}

// ---------- booleans ----------

/// `(eval/id v)` as a rational (a boolean is a width-1 bit-vector).
fn score_bool(v: &Value) -> R {
    R::from(v.as_bv().eval_id().clone())
}
fn score_bool_neg(v: &Value) -> R {
    one() - score_bool(v)
}

// ---------- the recursive scorer ----------

fn ev(t: &Sexp, asn: &Assignment, env: &[(String, Value)]) -> Value {
    eval(t, asn, env)
}

/// `((score c assignment env) formula)`.
pub fn score(c: &R, asn: &Assignment, env: &[(String, Value)], formula: &Sexp) -> R {
    match formula {
        Sexp::Sym(s) if s == "⊤" => return one(),
        Sexp::Sym(s) if s == "⊥" => return zero(),
        _ => {}
    }

    let items = match formula {
        Sexp::List(v) => v,
        // A bare boolean atom (symbol / predicate result).
        _ => return score_bool(&ev(formula, asn, env)),
    };

    match items[0].as_sym() {
        Some("let") => {
            let bindings = items[1].as_list().expect("let bindings");
            let mut new_env: Vec<(String, Value)> = env.to_vec();
            for b in bindings {
                let pair = b.as_list().expect("binding pair");
                let name = pair[0].as_sym().expect("binding name").to_string();
                let val = eval(&pair[1], asn, &new_env);
                new_env.push((name, val));
            }
            score(c, asn, &new_env, &items[2])
        }
        Some("∨") => {
            let mut m = zero();
            for arg in &items[1..] {
                m = rmax(m, score(c, asn, env, arg));
            }
            m
        }
        Some("∧") => {
            let args = &items[1..];
            if args.is_empty() {
                return one();
            }
            let mut sum = zero();
            for arg in args {
                sum += score(c, asn, env, arg);
            }
            sum / R::from(args.len() as u32)
        }
        Some("¬") => score_negation(c, asn, env, &items[1]),
        Some("=") => score_eq(c, &ev(&items[1], asn, env), &ev(&items[2], asn, env)),
        Some("bvult") => score_bv_lt(
            c,
            ev(&items[1], asn, env).as_bv(),
            ev(&items[2], asn, env).as_bv(),
        ),
        Some("fp.lt") => score_fplt(
            c,
            ev(&items[1], asn, env).as_fp(),
            ev(&items[2], asn, env).as_fp(),
        ),
        Some("fp.leq") => score_fpleq(
            c,
            ev(&items[1], asn, env).as_fp(),
            ev(&items[2], asn, env).as_fp(),
        ),
        // FIX: the Racket clause for positive `fp.gt` dropped `env`.
        Some("fp.gt") => score_fpgt(
            c,
            ev(&items[1], asn, env).as_fp(),
            ev(&items[2], asn, env).as_fp(),
        ),
        Some("fp.geq") => score_fpgeq(
            c,
            ev(&items[1], asn, env).as_fp(),
            ev(&items[2], asn, env).as_fp(),
        ),
        Some("fp.eq") => score_fpeq(
            c,
            ev(&items[1], asn, env).as_fp(),
            ev(&items[2], asn, env).as_fp(),
        ),
        // Any other atom is a boolean expression.
        _ => score_bool(&ev(formula, asn, env)),
    }
}

/// Score a binary atom `(head v1 v2)` (or its negation) directly from the
/// operand *values*. Used by the DAG scorer so it reuses the exact same case
/// analysis as the recursive `score` above. `head` is the atom's operator
/// symbol (`=`, `bvult`, `fp.lt`, …).
pub(crate) fn score_atom(c: &R, head: &str, neg: bool, v1: &Value, v2: &Value) -> R {
    if !neg {
        match head {
            "=" => score_eq(c, v1, v2),
            "bvult" => score_bv_lt(c, v1.as_bv(), v2.as_bv()),
            "fp.lt" => score_fplt(c, v1.as_fp(), v2.as_fp()),
            "fp.leq" => score_fpleq(c, v1.as_fp(), v2.as_fp()),
            "fp.gt" => score_fpgt(c, v1.as_fp(), v2.as_fp()),
            "fp.geq" => score_fpgeq(c, v1.as_fp(), v2.as_fp()),
            "fp.eq" => score_fpeq(c, v1.as_fp(), v2.as_fp()),
            _ => panic!("not a scorable atom: {head}"),
        }
    } else {
        match head {
            "=" => score_ne(v1, v2),
            "bvult" => score_bv_ge(c, v1.as_bv(), v2.as_bv()),
            "fp.lt" => score_fp_not_lt(c, v1.as_fp(), v2.as_fp()),
            "fp.leq" => score_fp_not_leq(c, v1.as_fp(), v2.as_fp()),
            "fp.gt" => score_fp_not_gt(c, v1.as_fp(), v2.as_fp()),
            "fp.geq" => score_fp_not_geq(c, v1.as_fp(), v2.as_fp()),
            "fp.eq" => score_fp_not_eq(v1.as_fp(), v2.as_fp()),
            _ => panic!("not a scorable atom: {head}"),
        }
    }
}

/// Score a bare boolean term value (a width-1 bit-vector), negated or not.
pub(crate) fn score_bool_value(neg: bool, v: &Value) -> R {
    if neg {
        score_bool_neg(v)
    } else {
        score_bool(v)
    }
}

fn score_negation(c: &R, asn: &Assignment, env: &[(String, Value)], inner: &Sexp) -> R {
    if let Sexp::List(items) = inner {
        let a = || ev(&items[1], asn, env);
        let b = || ev(&items[2], asn, env);
        match items[0].as_sym() {
            Some("=") => return score_ne(&a(), &b()),
            Some("bvult") => return score_bv_ge(c, a().as_bv(), b().as_bv()),
            Some("fp.lt") => return score_fp_not_lt(c, a().as_fp(), b().as_fp()),
            Some("fp.leq") => return score_fp_not_leq(c, a().as_fp(), b().as_fp()),
            Some("fp.gt") => return score_fp_not_gt(c, a().as_fp(), b().as_fp()),
            Some("fp.geq") => return score_fp_not_geq(c, a().as_fp(), b().as_fp()),
            Some("fp.eq") => return score_fp_not_eq(a().as_fp(), b().as_fp()),
            _ => {}
        }
    }
    // `(¬ b)` for a boolean atom `b`.
    score_bool_neg(&ev(inner, asn, env))
}
