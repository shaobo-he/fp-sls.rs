//! Scoring. Port of `score.rkt`.
//!
//! The score of a formula under an assignment is a value in `[0, 1]`, equal to
//! 1 exactly when the formula is satisfied. Following the paper, conjunctions
//! average and disjunctions take the maximum; (in)equalities degrade smoothly
//! with a distance metric scaled by the constant `c`.
//!
//! The scoring logic is written **once**, generic over [`ScoreNum`], and
//! instantiated at exact `Rational` (the sound default) and approximate `f64`
//! (`--f64-score`). The only precision-specific operation is
//! [`ScoreNum::from_ratio`], which turns an exactly-computed integer distance
//! `num/den` into a score; everything else (the NaN/zero case analysis, the
//! `1 - dist`, the `c·…` scaling, max and mean aggregation) is shared. Rust
//! monomorphizes generics, so each instantiation is as fast as a hand-written
//! version.
//!
//! Two fixes relative to the Racket original:
//!   * positive `fp.gt` now threads `env` (the Racket `score` clause dropped it,
//!     an arity bug that crashed on any un-negated `fp.gt`);
//!   * scores are exact rationals (or, opt-in, `f64`) rather than inexact flonums.

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
use std::ops::{Add, Div, Sub};

// ---------- the score numeric type ----------

/// The numeric type used to *rank* candidate moves. Implemented for exact
/// `Rational` (sound default) and approximate `f64` (`--f64-score`). The exact
/// distance is always computed in `Integer`; only [`from_ratio`](ScoreNum::from_ratio)
/// is precision-specific.
pub trait ScoreNum:
    Clone + PartialOrd + Add<Output = Self> + Sub<Output = Self> + Div<Output = Self>
{
    fn one() -> Self;
    fn zero() -> Self;
    /// The exactly-computed distance ratio `num/den`, as a score.
    fn from_ratio(num: Integer, den: Integer) -> Self;
    /// A conjunct count `n`, as a `∧`-mean denominator.
    fn from_count(n: usize) -> Self;
    /// `self · x` — scale a `[0,1]` score by the constant `c`.
    fn scale(&self, x: Self) -> Self;
}

impl ScoreNum for Rational {
    fn one() -> Self {
        Rational::from(1)
    }
    fn zero() -> Self {
        Rational::from(0)
    }
    fn from_ratio(num: Integer, den: Integer) -> Self {
        Rational::from((num, den))
    }
    fn from_count(n: usize) -> Self {
        Rational::from(n as u32)
    }
    fn scale(&self, x: Self) -> Self {
        self * x
    }
}

impl ScoreNum for f64 {
    fn one() -> Self {
        1.0
    }
    fn zero() -> Self {
        0.0
    }
    fn from_ratio(num: Integer, den: Integer) -> Self {
        num.to_f64() / den.to_f64()
    }
    fn from_count(n: usize) -> Self {
        n as f64
    }
    fn scale(&self, x: Self) -> Self {
        self * x
    }
}

fn smax<S: PartialOrd>(a: S, b: S) -> S {
    if a >= b {
        a
    } else {
        b
    }
}

// ---------- distance-based scores ----------

/// `c · (1 - dist/2^width)`, with `dist = |v1 - v2| + [eq]`.
fn bv_dist_score<S: ScoreNum>(c: &S, bv1: &BitVec, bv2: &BitVec, eq: bool) -> S {
    let mut dist = Integer::from(&bv1.value - &bv2.value).abs();
    if eq {
        dist += 1;
    }
    c.scale(S::one() - S::from_ratio(dist, two_pow(bv1.width)))
}

/// `(Hamming-distance …)`-based equality score for bit-vectors.
fn score_bv_eq<S: ScoreNum>(c: &S, bv1: &BitVec, bv2: &BitVec) -> S {
    if bv1.bv_eq(bv2) {
        S::one()
    } else {
        let h = bv1.hamming_distance(bv2);
        c.scale(S::one() - S::from_ratio(Integer::from(h), Integer::from(bv1.width)))
    }
}

fn score_bv_ne<S: ScoreNum>(bv1: &BitVec, bv2: &BitVec) -> S {
    if bv1.bv_eq(bv2) {
        S::zero()
    } else {
        S::one()
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

fn fp_dist_score<S: ScoreNum>(c: &S, fp1: &FloatingPoint, fp2: &FloatingPoint, eq: bool) -> S {
    let mut dist = (get_fp_pos(fp1) - get_fp_pos(fp2)).abs();
    if eq {
        dist += 1;
    }
    let den = two_pow(fp1.exp_width + fp2.sig_width);
    c.scale(S::one() - S::from_ratio(dist, den))
}

// ---------- equality / inequality ----------

fn score_fp_eq_raw<S: ScoreNum>(c: &S, fp1: &FloatingPoint, fp2: &FloatingPoint) -> S {
    if fp1.is_nan() && fp2.is_nan() {
        S::one()
    } else if fp1.is_nan() || fp2.is_nan() {
        S::zero()
    } else if fp1.to_bitvec().bv_eq(&fp2.to_bitvec()) {
        S::one()
    } else {
        fp_dist_score(c, fp1, fp2, false)
    }
}

fn score_fp_ne_raw<S: ScoreNum>(fp1: &FloatingPoint, fp2: &FloatingPoint) -> S {
    if fp1.is_nan() && fp2.is_nan() {
        S::zero()
    } else if fp1.is_nan() || fp2.is_nan() {
        S::one()
    } else {
        score_bv_ne(&fp1.to_bitvec(), &fp2.to_bitvec())
    }
}

fn score_eq<S: ScoreNum>(c: &S, v1: &Value, v2: &Value) -> S {
    match (v1, v2) {
        (Value::BV(a), Value::BV(b)) => score_bv_eq(c, a, b),
        (Value::FP(a), Value::FP(b)) => score_fp_eq_raw(c, a, b),
        _ => panic!("type mismatch in ="),
    }
}

fn score_ne<S: ScoreNum>(v1: &Value, v2: &Value) -> S {
    match (v1, v2) {
        (Value::BV(a), Value::BV(b)) => score_bv_ne(a, b),
        (Value::FP(a), Value::FP(b)) => score_fp_ne_raw(a, b),
        _ => panic!("type mismatch in ≠"),
    }
}

// `fp.eq` / `¬fp.eq`: IEEE equality, which makes ±0 equal and any-NaN unequal.
fn score_fpeq<S: ScoreNum>(c: &S, fp1: &FloatingPoint, fp2: &FloatingPoint) -> S {
    if fp1.is_nan() || fp2.is_nan() {
        S::zero()
    } else if fp1.is_zero() && fp2.is_zero() {
        S::one()
    } else {
        score_fp_eq_raw(c, fp1, fp2)
    }
}

fn score_fp_not_eq<S: ScoreNum>(fp1: &FloatingPoint, fp2: &FloatingPoint) -> S {
    if fp1.is_nan() || fp2.is_nan() {
        S::one()
    } else if fp1.is_zero() && fp2.is_zero() {
        S::zero()
    } else {
        score_bv_ne(&fp1.to_bitvec(), &fp2.to_bitvec())
    }
}

// ---------- bit-vector ordering ----------

fn score_bv_lt<S: ScoreNum>(c: &S, bv1: &BitVec, bv2: &BitVec) -> S {
    if bv1.bv_lt(bv2) {
        S::one()
    } else {
        bv_dist_score(c, bv1, bv2, true)
    }
}

fn score_bv_ge<S: ScoreNum>(c: &S, bv1: &BitVec, bv2: &BitVec) -> S {
    if bv1.bv_ge(bv2) {
        S::one()
    } else {
        bv_dist_score(c, bv1, bv2, false)
    }
}

// ---------- floating-point ordering ----------
// Each predicate has a score and a score for its negation; NaN makes the
// predicate fail (score 0) and its negation hold (score 1).

fn score_fplt<S: ScoreNum>(c: &S, a: &FloatingPoint, b: &FloatingPoint) -> S {
    if a.is_nan() || b.is_nan() {
        S::zero()
    } else if a.fp_lt(b) {
        S::one()
    } else {
        fp_dist_score(c, a, b, true)
    }
}
fn score_fp_not_lt<S: ScoreNum>(c: &S, a: &FloatingPoint, b: &FloatingPoint) -> S {
    if a.is_nan() || b.is_nan() {
        S::one()
    } else if a.fp_ge(b) {
        S::one()
    } else {
        fp_dist_score(c, a, b, false)
    }
}
fn score_fpleq<S: ScoreNum>(c: &S, a: &FloatingPoint, b: &FloatingPoint) -> S {
    if a.is_nan() || b.is_nan() {
        S::zero()
    } else if a.fp_le(b) {
        S::one()
    } else {
        fp_dist_score(c, a, b, false)
    }
}
fn score_fp_not_leq<S: ScoreNum>(c: &S, a: &FloatingPoint, b: &FloatingPoint) -> S {
    if a.is_nan() || b.is_nan() {
        S::one()
    } else if a.fp_gt(b) {
        S::one()
    } else {
        fp_dist_score(c, a, b, true)
    }
}
fn score_fpgt<S: ScoreNum>(c: &S, a: &FloatingPoint, b: &FloatingPoint) -> S {
    if a.is_nan() || b.is_nan() {
        S::zero()
    } else if a.fp_gt(b) {
        S::one()
    } else {
        fp_dist_score(c, a, b, true)
    }
}
fn score_fp_not_gt<S: ScoreNum>(c: &S, a: &FloatingPoint, b: &FloatingPoint) -> S {
    if a.is_nan() || b.is_nan() {
        S::one()
    } else if a.fp_le(b) {
        S::one()
    } else {
        fp_dist_score(c, a, b, false)
    }
}
fn score_fpgeq<S: ScoreNum>(c: &S, a: &FloatingPoint, b: &FloatingPoint) -> S {
    if a.is_nan() || b.is_nan() {
        S::zero()
    } else if a.fp_ge(b) {
        S::one()
    } else {
        fp_dist_score(c, a, b, false)
    }
}
fn score_fp_not_geq<S: ScoreNum>(c: &S, a: &FloatingPoint, b: &FloatingPoint) -> S {
    if a.is_nan() || b.is_nan() {
        S::one()
    } else if a.fp_lt(b) {
        S::one()
    } else {
        fp_dist_score(c, a, b, true)
    }
}

// ---------- booleans ----------

/// `(eval/id v)` as a score (a boolean is a width-1 bit-vector, value 0 or 1).
fn score_bool<S: ScoreNum>(v: &Value) -> S {
    S::from_ratio(v.as_bv().eval_id().clone(), Integer::from(1))
}
fn score_bool_neg<S: ScoreNum>(v: &Value) -> S {
    S::one() - score_bool(v)
}

// ---------- the recursive scorer ----------

fn ev(t: &Sexp, asn: &Assignment, env: &[(String, Value)]) -> Value {
    eval(t, asn, env)
}

/// `((score c assignment env) formula)`.
pub fn score<S: ScoreNum>(c: &S, asn: &Assignment, env: &[(String, Value)], formula: &Sexp) -> S {
    match formula {
        Sexp::Sym(s) if s == "⊤" => return S::one(),
        Sexp::Sym(s) if s == "⊥" => return S::zero(),
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
            let mut m = S::zero();
            for arg in &items[1..] {
                m = smax(m, score(c, asn, env, arg));
            }
            m
        }
        Some("∧") => {
            let args = &items[1..];
            if args.is_empty() {
                return S::one();
            }
            let mut sum = S::zero();
            for arg in args {
                sum = sum + score(c, asn, env, arg);
            }
            sum / S::from_count(args.len())
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
pub(crate) fn score_atom<S: ScoreNum>(c: &S, head: &str, neg: bool, v1: &Value, v2: &Value) -> S {
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
pub(crate) fn score_bool_value<S: ScoreNum>(neg: bool, v: &Value) -> S {
    if neg {
        score_bool_neg(v)
    } else {
        score_bool(v)
    }
}

fn score_negation<S: ScoreNum>(
    c: &S,
    asn: &Assignment,
    env: &[(String, Value)],
    inner: &Sexp,
) -> S {
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
