//! IEEE-style floating-point values of arbitrary format. Port of `data/fp.rkt`.
//!
//! The `value` is an MPFR float (`rug::Float`) whose precision equals the
//! significand width `sig_width` (including the hidden bit) — exactly mirroring
//! Racket's `math/bigfloat` with `(bf-precision sig-width)`. MPFR uses an
//! unbounded exponent range, so — as in the Racket original — every arithmetic
//! result is renormalized afterwards: overflow becomes ±∞ and underflow is
//! rounded into the subnormal range for the target `(exp_width, sig_width)`.

use crate::data::bitvec::{two_pow, BitVec};
use crate::rng::Rng;
use crate::sexp::Sexp;
use rug::float::Round;
use rug::{Float, Integer, Rational};
use std::cmp::Ordering;

/// The five SMT-LIB rounding-mode constants (used to enumerate `RoundingMode`
/// variables).
pub const ROUNDING_MODES: [&str; 5] = [
    "roundNearestTiesToEven",
    "roundTowardZero",
    "roundTowardPositive",
    "roundTowardNegative",
    "roundNearestTiesToAway",
];

/// Map an SMT-LIB rounding-mode symbol (long name or abbreviation) to MPFR's.
pub fn rounding_mode(sym: &str) -> Option<Round> {
    Some(match sym {
        "roundNearestTiesToEven" | "RNE" => Round::Nearest,
        "roundTowardZero" | "RTZ" => Round::Zero,
        "roundTowardPositive" | "RTP" => Round::Up,
        "roundTowardNegative" | "RTN" => Round::Down,
        "roundNearestTiesToAway" | "RNA" => Round::AwayZero,
        _ => return None,
    })
}

#[derive(Clone, Debug)]
pub struct FloatingPoint {
    pub exp_width: u32,
    /// Significand width *including* the hidden bit.
    pub sig_width: u32,
    pub value: Float,
}

impl PartialEq for FloatingPoint {
    fn eq(&self, other: &Self) -> bool {
        self.exp_width == other.exp_width
            && self.sig_width == other.sig_width
            // IEEE total order: distinguishes ±0 and treats NaN == NaN, which is
            // the right notion of "structurally identical" for a stored value.
            && self.value.total_cmp(&other.value) == Ordering::Equal
    }
}

/// `Float::with_val` with `prec` precision from any value MPFR can ingest.
#[inline]
fn fl<T>(prec: u32, v: T) -> Float
where
    Float: rug::Assign<T>,
{
    Float::with_val(prec, v)
}

/// Round the positive rational `num/den` (den > 0) to an integer according to
/// `round`, where `negative` is the sign of the value being rounded (so the
/// directed modes round the magnitude in the correct direction).
fn round_rational(num: Integer, den: &Integer, round: Round, negative: bool) -> Integer {
    let (q, r) = num.div_rem_euc(den.clone());
    if r == 0 {
        return q;
    }
    let two_r = Integer::from(&r * 2);
    let up = match round {
        Round::Zero => false,        // truncate magnitude toward zero
        Round::Up => !negative,      // toward +∞: positive rounds up, negative down
        Round::Down => negative,     // toward −∞: positive rounds down, negative up
        Round::Nearest => match two_r.cmp(den) {
            Ordering::Less => false,
            Ordering::Greater => true,
            Ordering::Equal => q.is_odd(), // ties to even
        },
        Round::AwayZero => match two_r.cmp(den) {
            Ordering::Less => false,
            Ordering::Greater => true,
            Ordering::Equal => true, // ties away from zero
        },
        _ => false,
    };
    if up {
        q + Integer::from(1)
    } else {
        q
    }
}

/// Which arithmetic operation `arith` performs — lets it compute both the fast
/// MPFR result and, when a single exact rounding is required, the exact result.
#[derive(Clone, Copy)]
enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Sqrt,
    Id,
}

/// `floor(log2(num/den))` for positive integers: the unique `e` with
/// `2^e <= num/den < 2^(e+1)`. Exact (no flooring of intermediate ratios).
fn floor_log2(num: &Integer, den: &Integer) -> i64 {
    let ge_pow2 = |e: i64| -> bool {
        // num/den >= 2^e  <=>  num >= den*2^e (e>=0)  or  num*2^-e >= den (e<0)
        if e >= 0 {
            *num >= Integer::from(den << (e as u32))
        } else {
            Integer::from(num << ((-e) as u32)) >= *den
        }
    };
    let mut e = num.significant_bits() as i64 - den.significant_bits() as i64 - 1;
    while ge_pow2(e + 1) {
        e += 1;
    }
    while !ge_pow2(e) {
        e -= 1;
    }
    e
}

/// `num/den * 2^scale` as an exact integer ratio `(p, q)` with `q > 0`.
fn scale_ratio(num: &Integer, den: &Integer, scale: i64) -> (Integer, Integer) {
    if scale >= 0 {
        (Integer::from(num << (scale as u32)), den.clone())
    } else {
        (num.clone(), Integer::from(den << ((-scale) as u32)))
    }
}

impl FloatingPoint {
    pub fn new(exp_width: u32, sig_width: u32, value: Float) -> FloatingPoint {
        FloatingPoint {
            exp_width,
            sig_width,
            value,
        }
    }

    #[inline]
    fn prec(&self) -> u32 {
        self.sig_width
    }

    fn special(exp_width: u32, sig_width: u32, v: f64) -> FloatingPoint {
        FloatingPoint::new(exp_width, sig_width, fl(sig_width, v))
    }

    pub fn plus_inf(exp_width: u32, sig_width: u32) -> FloatingPoint {
        FloatingPoint::special(exp_width, sig_width, f64::INFINITY)
    }
    pub fn minus_inf(exp_width: u32, sig_width: u32) -> FloatingPoint {
        FloatingPoint::special(exp_width, sig_width, f64::NEG_INFINITY)
    }
    pub fn nan(exp_width: u32, sig_width: u32) -> FloatingPoint {
        FloatingPoint::special(exp_width, sig_width, f64::NAN)
    }

    /// `(initialize/fp exp sig)` — positive zero.
    pub fn initialize(exp_width: u32, sig_width: u32) -> FloatingPoint {
        FloatingPoint::special(exp_width, sig_width, 0.0)
    }

    // ----- predicates -----

    pub fn is_nan(&self) -> bool {
        self.value.is_nan()
    }
    pub fn is_infinity(&self) -> bool {
        self.value.is_infinite()
    }
    pub fn is_zero(&self) -> bool {
        self.value.is_zero()
    }

    /// `(bigfloat-signbit v)` — 1 if the sign bit is set (incl. -0, -NaN).
    fn signbit(&self) -> u32 {
        if self.value.is_sign_negative() {
            1
        } else {
            0
        }
    }

    /// `fp/positive?`: +zero or `0 < x`.
    pub fn is_positive(&self) -> bool {
        if self.is_zero() {
            self.signbit() == 0
        } else {
            self.value.is_sign_positive() && !self.is_nan()
        }
    }

    /// `fp/negative?`: -zero or `x < 0`.
    pub fn is_negative(&self) -> bool {
        if self.is_zero() {
            self.signbit() == 1
        } else {
            self.value.is_sign_negative() && !self.is_nan()
        }
    }

    pub fn is_normal(&self) -> bool {
        if self.is_nan() || self.is_infinity() || self.is_zero() {
            return false;
        }
        let abs = self.fpabs();
        abs.fp_gt(&FloatingPoint::maximum_subnormal(self.exp_width, self.sig_width))
    }

    pub fn is_subnormal(&self) -> bool {
        if self.is_nan() || self.is_infinity() || self.is_zero() {
            return false;
        }
        let abs = self.fpabs();
        abs.fp_le(&FloatingPoint::maximum_subnormal(self.exp_width, self.sig_width))
    }

    // ----- comparisons (compare values; NaN-involving compares are false) -----

    pub fn fp_eq(&self, o: &FloatingPoint) -> bool {
        self.value == o.value
    }
    pub fn fp_lt(&self, o: &FloatingPoint) -> bool {
        self.value < o.value
    }
    pub fn fp_gt(&self, o: &FloatingPoint) -> bool {
        self.value > o.value
    }
    pub fn fp_le(&self, o: &FloatingPoint) -> bool {
        self.value <= o.value
    }
    pub fn fp_ge(&self, o: &FloatingPoint) -> bool {
        self.value >= o.value
    }

    // ----- sign-only arithmetic (exact, no renormalization) -----

    pub fn fpabs(&self) -> FloatingPoint {
        FloatingPoint::new(self.exp_width, self.sig_width, self.value.clone().abs())
    }

    pub fn fpneg(&self) -> FloatingPoint {
        FloatingPoint::new(self.exp_width, self.sig_width, fl(self.prec(), -&self.value))
    }

    // ----- format limits -----

    pub fn maximum_subnormal(exp_width: u32, sig_width: u32) -> FloatingPoint {
        // bv = 2^(sig-1) - 1
        let bv = BitVec::new(exp_width + sig_width, &two_pow(sig_width - 1) - Integer::from(1));
        FloatingPoint::from_bitvec(&bv, exp_width, sig_width)
    }

    pub fn maximum_normal(exp_width: u32, sig_width: u32) -> FloatingPoint {
        let inf_bv = FloatingPoint::plus_inf(exp_width, sig_width).to_bitvec();
        let bv = BitVec::new(exp_width + sig_width, inf_bv.value - Integer::from(1));
        FloatingPoint::from_bitvec(&bv, exp_width, sig_width)
    }

    // ----- core arithmetic with renormalization -----

    /// Compute `op` at precision `sig_width` with rounding `round`, then map the
    /// result into the format's exponent range.
    ///
    /// The fast MPFR path is IEEE-correct for RNE/RTZ/RTP/RTN in the normal and
    /// overflow regimes: there the result is already exactly the format value. Two
    /// cases instead need an exact single rounding:
    ///   * `Round::AwayZero` (SMT-LIB roundNearestTiesToAway): MPFR has no
    ///     nearest-ties-away mode, so `with_val_round` used the *directed* RNDA.
    ///   * a subnormal result: the fast path would round twice (to `sig_width`,
    ///     then onto the coarser subnormal grid), double-rounding for nearest
    ///     modes. Rounding the exact result once is correct.
    ///
    /// Classification is by EXPONENT (MPFR `get_exp` convention value = m·2^e,
    /// ½ ≤ |m| < 1): the largest normal has exponent `2^(eb-1)`, the smallest
    /// normal `3 - 2^(eb-1)` (f32 128 / −125, f64 1024 / −1021). This avoids
    /// rebuilding `maximum_normal`/`maximum_subnormal` (→ Rational → gcd) per op,
    /// and the operand/rational work stays off the common (normal) hot path.
    fn arith(&self, o: &FloatingPoint, round: Round, op: ArithOp) -> FloatingPoint {
        assert!(
            self.value.prec() == o.value.prec()
                && self.exp_width == o.exp_width
                && self.sig_width == o.sig_width,
            "invalid arithmetic operation"
        );
        let p = self.prec();
        let result = match op {
            ArithOp::Add => Float::with_val_round(p, &self.value + &o.value, round).0,
            ArithOp::Sub => Float::with_val_round(p, &self.value - &o.value, round).0,
            ArithOp::Mul => Float::with_val_round(p, &self.value * &o.value, round).0,
            ArithOp::Div => Float::with_val_round(p, &self.value / &o.value, round).0,
            ArithOp::Sqrt => Float::with_val_round(p, self.value.sqrt_ref(), round).0,
            ArithOp::Id => Float::with_val_round(p, &self.value, round).0,
        };
        let emax = 1i32 << (self.exp_width - 1);
        // zero / ±∞ / NaN have no exponent and are already valid format values.
        let exp = match result.get_exp() {
            None => return FloatingPoint::new(self.exp_width, self.sig_width, result),
            Some(e) => e,
        };
        // Exact single-rounding path (rare): RNA, or a subnormal result. Only here
        // do we touch the operands — keeping `is_finite`/rational off the hot path.
        if (round == Round::AwayZero || exp < 3 - emax)
            && self.value.is_finite()
            && o.value.is_finite()
        {
            if let Some(rv) = self.exact_result(o, op) {
                if rv != 0 {
                    return FloatingPoint::round_rational_to_format(
                        &rv,
                        self.exp_width,
                        self.sig_width,
                        round,
                    );
                }
            }
        }
        if exp > emax {
            // overflow → ±∞ or ±max-normal, depending on mode and sign (rare).
            return FloatingPoint::overflow_value(
                self.exp_width,
                self.sig_width,
                round,
                result.is_sign_negative(),
            );
        }
        // normal range: the MPFR result is already exactly the format value.
        FloatingPoint::new(self.exp_width, self.sig_width, result)
    }

    /// Exact rational value of the operation on the (finite) operands, used by the
    /// single-rounding path. `sqrt` is irrational, so it returns a high-precision
    /// faithful rational; `sqrt` never produces a subnormal result, so that path
    /// is only reached for `Round::AwayZero`, where an operation result is never
    /// within `2^-(2·sig+18)` of a grid midpoint without being exactly on it.
    fn exact_result(&self, o: &FloatingPoint, op: ArithOp) -> Option<Rational> {
        if let ArithOp::Sqrt = op {
            return Float::with_val(2 * self.sig_width + 18, self.value.sqrt_ref()).to_rational();
        }
        let a = self.value.to_rational()?;
        Some(match op {
            ArithOp::Add => a + o.value.to_rational()?,
            ArithOp::Sub => a - o.value.to_rational()?,
            ArithOp::Mul => a * o.value.to_rational()?,
            ArithOp::Div => {
                let b = o.value.to_rational()?;
                if b == 0 {
                    return None;
                }
                a / b
            }
            ArithOp::Id => a,
            ArithOp::Sqrt => unreachable!(),
        })
    }

    pub fn fpadd(&self, o: &FloatingPoint, round: Round) -> FloatingPoint {
        self.arith(o, round, ArithOp::Add)
    }
    pub fn fpsub(&self, o: &FloatingPoint, round: Round) -> FloatingPoint {
        self.arith(o, round, ArithOp::Sub)
    }
    pub fn fpmul(&self, o: &FloatingPoint, round: Round) -> FloatingPoint {
        self.arith(o, round, ArithOp::Mul)
    }
    pub fn fpdiv(&self, o: &FloatingPoint, round: Round) -> FloatingPoint {
        self.arith(o, round, ArithOp::Div)
    }
    pub fn fpsqrt(&self, round: Round) -> FloatingPoint {
        self.arith(self, round, ArithOp::Sqrt)
    }

    /// `(fp/prune fp)` — push a value through renormalization in mode `round`.
    pub fn prune(&self, round: Round) -> FloatingPoint {
        self.arith(self, round, ArithOp::Id)
    }

    /// Round an exact, finite, NONZERO rational `rv` once to the IEEE
    /// `(exp_width, sig_width)` format with `round`. Single rounding (no
    /// double-rounding) and correct for all five modes, including
    /// nearest-ties-away (`Round::AwayZero`), which MPFR cannot do natively.
    fn round_rational_to_format(
        rv: &Rational,
        exp_width: u32,
        sig_width: u32,
        round: Round,
    ) -> FloatingPoint {
        let neg = *rv < 0;
        let mag = rv.clone().abs();
        let num = Integer::from(mag.numer());
        let den = Integer::from(mag.denom());
        let sig_wo = sig_width - 1;
        let bias = (1i64 << (exp_width - 1)) - 1;
        let e_min = 1 - bias; // smallest normal unbiased exponent
        let e_max = bias; // largest normal unbiased exponent

        // floor(log2(mag)): unique e with 2^e <= mag < 2^(e+1).
        let e = floor_log2(&num, &den);

        let (sig_int, exp_unbiased, subnormal) = if e >= e_min {
            // normal candidate: round mag / 2^(e - sig_wo) to an integer significand.
            let scale = sig_wo as i64 - e;
            let (p, q) = scale_ratio(&num, &den, scale);
            let mut m = round_rational(p, &q, round, neg);
            let mut exp_u = e;
            if m == (Integer::from(1) << sig_width) {
                // 1.11..1 rounded up to 10.00..0: carry into the next binade.
                m >>= 1;
                exp_u += 1;
            }
            (m, exp_u, false)
        } else {
            // subnormal candidate: fixed grid step 2^(e_min - sig_wo).
            let scale = sig_wo as i64 - e_min;
            let (p, q) = scale_ratio(&num, &den, scale);
            (round_rational(p, &q, round, neg), e_min, true)
        };

        if subnormal {
            if sig_int == 0 {
                return FloatingPoint::signed_zero(exp_width, sig_width, neg);
            }
            // sig_int in [1, 2^sig_wo]; the bit pattern equals sig_int, and the
            // value 2^sig_wo encodes the smallest normal (the rounded-up case).
            let fp = FloatingPoint::from_bitvec(
                &BitVec::new(exp_width + sig_width, sig_int),
                exp_width,
                sig_width,
            );
            return if neg { fp.fpneg() } else { fp };
        }
        if exp_unbiased > e_max {
            return FloatingPoint::overflow_value(exp_width, sig_width, round, neg);
        }
        let biased = Integer::from(exp_unbiased + bias);
        let frac = Integer::from(&sig_int) - (Integer::from(1) << sig_wo);
        let pattern = (biased << sig_wo) + frac;
        let fp = FloatingPoint::from_bitvec(
            &BitVec::new(exp_width + sig_width, pattern),
            exp_width,
            sig_width,
        );
        if neg {
            fp.fpneg()
        } else {
            fp
        }
    }

    /// Signed zero of the given format.
    fn signed_zero(exp_width: u32, sig_width: u32, neg: bool) -> FloatingPoint {
        FloatingPoint::special(exp_width, sig_width, if neg { -0.0 } else { 0.0 })
    }

    /// The format value an overflow rounds to, per mode and sign.
    fn overflow_value(exp_width: u32, sig_width: u32, round: Round, neg: bool) -> FloatingPoint {
        let max_normal = FloatingPoint::maximum_normal(exp_width, sig_width);
        let pinf = || FloatingPoint::plus_inf(exp_width, sig_width);
        let ninf = || FloatingPoint::minus_inf(exp_width, sig_width);
        match round {
            Round::Nearest | Round::AwayZero => {
                if neg {
                    ninf()
                } else {
                    pinf()
                }
            }
            Round::Zero => {
                if neg {
                    max_normal.fpneg()
                } else {
                    max_normal
                }
            }
            Round::Up => {
                if neg {
                    max_normal.fpneg()
                } else {
                    pinf()
                }
            }
            Round::Down => {
                if neg {
                    ninf()
                } else {
                    max_normal
                }
            }
            _ => {
                if neg {
                    ninf()
                } else {
                    pinf()
                }
            }
        }
    }

    /// `(eval/fpconv fp dest-exp dest-sig)` in mode `round`. Rounds the exact
    /// source value once into the destination format (no double-rounding).
    pub fn fpconv(&self, dest_exp: u32, dest_sig: u32, round: Round) -> FloatingPoint {
        if self.is_nan() {
            return FloatingPoint::nan(dest_exp, dest_sig);
        }
        if self.is_infinity() {
            return if self.value.is_sign_negative() {
                FloatingPoint::minus_inf(dest_exp, dest_sig)
            } else {
                FloatingPoint::plus_inf(dest_exp, dest_sig)
            };
        }
        if self.is_zero() {
            return FloatingPoint::signed_zero(dest_exp, dest_sig, self.signbit() == 1);
        }
        // Same fast-path/exact-fallback split as `arith`: the MPFR round into the
        // destination precision is correct for RNE/RTZ/RTP/RTN in the normal and
        // overflow regimes; only RNA or a subnormal destination need an exact
        // single rounding (a wide→narrow convert can underflow into subnormals).
        let result = Float::with_val_round(dest_sig, &self.value, round).0;
        let emax = 1i32 << (dest_exp - 1);
        let exp = match result.get_exp() {
            None => return FloatingPoint::new(dest_exp, dest_sig, result),
            Some(e) => e,
        };
        if round == Round::AwayZero || exp < 3 - emax {
            if let Some(rv) = self.value.to_rational() {
                if rv != 0 {
                    return FloatingPoint::round_rational_to_format(&rv, dest_exp, dest_sig, round);
                }
            }
        }
        if exp > emax {
            return FloatingPoint::overflow_value(
                dest_exp,
                dest_sig,
                round,
                result.is_sign_negative(),
            );
        }
        FloatingPoint::new(dest_exp, dest_sig, result)
    }

    // ----- conversions to/from a real number -----

    fn real_from_float(value: Float, exp_width: u32, sig_width: u32) -> FloatingPoint {
        FloatingPoint::new(exp_width, sig_width, value).prune(Round::Nearest)
    }

    /// `(real->FloatingPoint rv exp sig)` for a machine double `rv`.
    pub fn real_from_f64(rv: f64, exp_width: u32, sig_width: u32) -> FloatingPoint {
        if rv == 0.0 {
            return FloatingPoint::signed_zero(exp_width, sig_width, rv.is_sign_negative());
        }
        if !rv.is_finite() {
            // ±∞ / NaN ingest exactly via MPFR (no rounding needed).
            return FloatingPoint::real_from_float(fl(sig_width, rv), exp_width, sig_width);
        }
        // Round the EXACT f64 once into the format (avoids the fl()+prune double
        // rounding for subnormal targets). `rv` at prec 53 is exact in MPFR.
        let r = Float::with_val(53, rv).to_rational().expect("finite f64");
        FloatingPoint::round_rational_to_format(&r, exp_width, sig_width, Round::Nearest)
    }

    /// `(real->FloatingPoint rv exp sig)` for an exact rational `rv`
    /// (used by the Z3 real-model path). Single correct rounding into the format.
    pub fn real_from_rational(rv: &Rational, exp_width: u32, sig_width: u32) -> FloatingPoint {
        if *rv == 0 {
            return FloatingPoint::signed_zero(exp_width, sig_width, false);
        }
        FloatingPoint::round_rational_to_format(rv, exp_width, sig_width, Round::Nearest)
    }

    /// `(bigfloat->flonum value)` — used by `fp->real`.
    pub fn to_f64(&self) -> f64 {
        self.value.to_f64()
    }

    // ----- conversions to/from bit-vectors -----

    fn from_sig_exp(prec: u32, mantissa: Integer, exp: i32) -> Float {
        // value = mantissa · 2^exp, built exactly via a rational then rounded to
        // `prec` (the value fits in `prec` bits, so this rounding is exact).
        let r = if exp >= 0 {
            Rational::from(mantissa << (exp as u32))
        } else {
            Rational::from((mantissa, Integer::from(1) << ((-exp) as u32)))
        };
        fl(prec, r)
    }

    /// `(BitVec->FloatingPoint bv exp sig)` — interpret IEEE bits.
    pub fn from_bitvec(bv: &BitVec, exp_width: u32, sig_width: u32) -> FloatingPoint {
        assert_eq!(bv.width, exp_width + sig_width, "Bit width doesn't match!");
        let prec = sig_width;
        let v = &bv.value;
        let sig_wo = sig_width - 1; // significand bits without hidden bit
        let sig_bits = Integer::from(v % &two_pow(sig_wo));
        let exp_bits = Integer::from(&(v.clone() >> sig_wo) % &two_pow(exp_width));
        let exp_bias = &two_pow(exp_width - 1) - Integer::from(1);
        let sign = v.get_bit(exp_width + sig_wo);

        let all_ones = &two_pow(exp_width) - Integer::from(1);
        let value = if exp_bits == all_ones {
            if sig_bits == 0 {
                fl(prec, if sign { f64::NEG_INFINITY } else { f64::INFINITY })
            } else {
                fl(prec, f64::NAN)
            }
        } else if exp_bits == 0 {
            if sig_bits == 0 {
                fl(prec, if sign { -0.0 } else { 0.0 })
            } else {
                // subnormal: mantissa = ±sig_bits, exponent = (1 - bias) - sig_wo
                let mantissa = if sign { -sig_bits } else { sig_bits };
                let e = (Integer::from(1) - &exp_bias) - Integer::from(sig_wo);
                FloatingPoint::from_sig_exp(prec, mantissa, e.to_i32().expect("exp fits i32"))
            }
        } else {
            // normal: mantissa = ±(2^sig_wo + sig_bits), exponent = exp_bits - bias - sig_wo
            let sig = &two_pow(sig_wo) + sig_bits;
            let mantissa = if sign { -sig } else { sig };
            let e = (exp_bits - &exp_bias) - Integer::from(sig_wo);
            FloatingPoint::from_sig_exp(prec, mantissa, e.to_i32().expect("exp fits i32"))
        };
        FloatingPoint::new(exp_width, sig_width, value)
    }

    /// `(FloatingPoint->BitVec fp)` — encode IEEE bits. Panics on NaN.
    pub fn to_bitvec(&self) -> BitVec {
        let exp_width = self.exp_width;
        let sig_width = self.sig_width;
        let sig_wo = sig_width - 1;
        let exp_bias = &two_pow(exp_width - 1) - Integer::from(1);
        let sign_bit = self.signbit();
        let sign_wrap = |v: Integer| v + (Integer::from(sign_bit) << (exp_width + sig_wo));

        let value = if self.is_nan() {
            panic!("no unique bv representation for nans!");
        } else if self.is_infinity() {
            sign_wrap((&two_pow(exp_width) - Integer::from(1)) << sig_wo)
        } else if self.is_zero() {
            sign_wrap(Integer::new())
        } else {
            let (sig_signed, exp) = self.value.to_integer_exp().expect("finite nonzero");
            let sig = sig_signed.abs();
            debug_assert!(sig >= two_pow(sig_wo) && sig < two_pow(sig_width));
            // normal threshold: exp >= (1 - bias) - sig_wo
            let threshold = (Integer::from(1) - &exp_bias) - Integer::from(sig_wo);
            let mag = if exp >= threshold {
                // normals
                let biased = (Integer::from(exp) + &exp_bias) + Integer::from(sig_wo);
                (biased << sig_wo) + Integer::from(&sig % &two_pow(sig_width - 1))
            } else {
                // subnormals: sig / 2^((1 - (bias+sig_wo)) - exp)
                let k = ((Integer::from(1) - (&exp_bias + Integer::from(sig_wo)))
                    - Integer::from(exp))
                .to_u32()
                .expect("subnormal shift fits");
                sig >> k
            };
            sign_wrap(mag)
        };
        BitVec::new(exp_width + sig_width, value)
    }

    /// `(FloatingPoint->FPConst fp)` — SMT-LIB constant for model printing.
    pub fn to_fp_const(&self) -> Sexp {
        let exp_width = self.exp_width;
        let sig_width = self.sig_width;
        if self.is_nan() {
            return Sexp::List(vec![
                Sexp::sym("_"),
                Sexp::sym("NaN"),
                Sexp::int(exp_width),
                Sexp::int(sig_width),
            ]);
        }
        if self.is_infinity() {
            let tag = if self.is_positive() { "+oo" } else { "-oo" };
            return Sexp::List(vec![
                Sexp::sym("_"),
                Sexp::sym(tag),
                Sexp::int(exp_width),
                Sexp::int(sig_width),
            ]);
        }
        if self.is_zero() {
            let tag = if self.is_positive() { "+zero" } else { "-zero" };
            return Sexp::List(vec![
                Sexp::sym("_"),
                Sexp::sym(tag),
                Sexp::int(exp_width),
                Sexp::int(sig_width),
            ]);
        }
        let bv_val = self.to_bitvec().value;
        let mask = &two_pow(exp_width + sig_width - 1) - Integer::from(1);
        let abs_value = Integer::from(&bv_val & &mask);
        let sig_wo = sig_width - 1;
        let sign = if self.is_positive() {
            BitVec::new(1, Integer::new())
        } else {
            BitVec::new(1, Integer::from(1))
        };
        let exp_bv = BitVec::new(exp_width, Integer::from(&abs_value >> sig_wo));
        let sig_bv = BitVec::new(
            sig_wo,
            Integer::from(&(&two_pow(sig_wo) - Integer::from(1)) & &abs_value),
        );
        Sexp::List(vec![
            Sexp::sym("fp"),
            sign.to_bv_const(),
            exp_bv.to_bv_const(),
            sig_bv.to_bv_const(),
        ])
    }

    // ----- neighborhood relation -----

    fn two(&self) -> FloatingPoint {
        FloatingPoint::real_from_f64(2.0, self.exp_width, self.sig_width)
    }

    /// `(exp/± fp)` — multiply / divide by two.
    fn exp_pm(&self) -> Vec<FloatingPoint> {
        let two = self.two();
        // ×2 / ÷2 are exact, so the rounding mode is irrelevant here.
        vec![
            self.fpmul(&two, Round::Nearest),
            self.fpdiv(&two, Round::Nearest),
        ]
    }

    /// `(sig/± fp)` — ±1 on the underlying bit-vector.
    fn sig_pm(&self) -> Vec<FloatingPoint> {
        let br = self.to_bitvec();
        let one = BitVec::new(br.width, Integer::from(1));
        vec![
            FloatingPoint::from_bitvec(&br.bvadd(&one), self.exp_width, self.sig_width),
            FloatingPoint::from_bitvec(&br.bvsub(&one), self.exp_width, self.sig_width),
        ]
    }

    /// `(get/fp-extended-neighbors fp)`.
    pub fn extended_neighbors(&self, rng: &mut Rng) -> Vec<FloatingPoint> {
        if self.is_nan() {
            return vec![FloatingPoint::random(self.exp_width, self.sig_width, rng)];
        }
        let exp_width = self.exp_width;
        let sig_width = self.sig_width;
        let ns: Vec<FloatingPoint> = self
            .to_bitvec()
            .extended_neighbors()
            .iter()
            .map(|bv| FloatingPoint::from_bitvec(bv, exp_width, sig_width))
            .collect();
        let fns: Vec<FloatingPoint> = ns
            .iter()
            .filter(|fp| !fp.is_nan() && !fp.is_infinity())
            .cloned()
            .collect();
        let mut base = if ns.len() == fns.len() {
            fns
        } else {
            let mut v = vec![
                FloatingPoint::nan(exp_width, sig_width),
                FloatingPoint::plus_inf(exp_width, sig_width),
                FloatingPoint::minus_inf(exp_width, sig_width),
            ];
            v.extend(fns);
            v
        };
        base.extend(self.exp_pm());
        base
    }

    /// `(get/fp-neighbor-exp fp)`.
    fn neighbor_exp(&self) -> Vec<FloatingPoint> {
        let sig_wo = self.sig_width - 1;
        let mut flip: Vec<FloatingPoint> = self
            .to_bitvec()
            .one_exchange_range(sig_wo, sig_wo + self.exp_width)
            .iter()
            .map(|bv| FloatingPoint::from_bitvec(bv, self.exp_width, self.sig_width))
            .collect();
        flip.extend(self.exp_pm());
        flip
    }

    /// `(get/fp-neighbor-sig fp)`.
    fn neighbor_sig(&self) -> Vec<FloatingPoint> {
        let sig_wo = self.sig_width - 1;
        let mut flip: Vec<FloatingPoint> = self
            .to_bitvec()
            .one_exchange_range(0, sig_wo)
            .iter()
            .map(|bv| FloatingPoint::from_bitvec(bv, self.exp_width, self.sig_width))
            .collect();
        flip.extend(self.sig_pm());
        flip
    }

    /// `(get/fp-neighbors val ni)` — variable-neighborhood moves (VNS).
    pub fn neighbors(&self, ni: u32, rng: &mut Rng) -> Vec<FloatingPoint> {
        match ni {
            1 => {
                if self.is_nan() {
                    vec![]
                } else {
                    vec![self.fpneg()]
                }
            }
            2 => {
                if self.is_nan() {
                    vec![]
                } else {
                    self.neighbor_exp()
                }
            }
            3 => {
                if self.is_nan() {
                    self.extended_neighbors(rng)
                } else {
                    self.neighbor_sig()
                }
            }
            _ => vec![],
        }
    }

    /// `(random/fp exp sig)`.
    pub fn random(exp_width: u32, sig_width: u32, rng: &mut Rng) -> FloatingPoint {
        if rng.coin_flip(0.8) {
            match rng.below(3) {
                0 => FloatingPoint::plus_inf(exp_width, sig_width),
                1 => FloatingPoint::minus_inf(exp_width, sig_width),
                _ => FloatingPoint::nan(exp_width, sig_width),
            }
        } else {
            let bv = BitVec::random(exp_width + sig_width, rng);
            FloatingPoint::from_bitvec(&bv, exp_width, sig_width)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rug::Integer;

    fn bv32(v: u64) -> BitVec {
        BitVec::new(32, Integer::from(v))
    }

    #[test]
    fn ieee_single_roundtrip() {
        // Known Float32 bit patterns.
        for (val, bits) in [
            (1.0_f64, 0x3F80_0000u64),
            (2.0, 0x4000_0000),
            (0.5, 0x3F00_0000),
            (-1.0, 0xBF80_0000),
            (0.0, 0x0000_0000),
        ] {
            let fp = FloatingPoint::real_from_f64(val, 8, 24);
            assert_eq!(fp.to_bitvec().value, Integer::from(bits), "encode {val}");
            let dec = FloatingPoint::from_bitvec(&bv32(bits), 8, 24);
            assert_eq!(dec.to_f64(), val, "decode {bits:#x}");
        }
    }

    #[test]
    fn signed_zero() {
        let pz = FloatingPoint::real_from_f64(0.0, 5, 11);
        let nz = FloatingPoint::real_from_f64(-0.0, 5, 11);
        assert!(pz.is_positive() && !pz.is_negative());
        assert!(nz.is_negative() && !nz.is_positive());
        assert!(pz.is_zero() && nz.is_zero());
    }

    #[test]
    fn overflow_to_infinity() {
        // Float16 max normal is 65504; 65520 overflows to +inf.
        let big = FloatingPoint::real_from_f64(65520.0, 5, 11);
        assert!(big.is_infinity() && big.is_positive());
    }

    #[test]
    fn div_by_zero_signs() {
        let one = FloatingPoint::real_from_f64(1.0, 5, 11);
        let pz = FloatingPoint::real_from_f64(0.0, 5, 11);
        let nz = FloatingPoint::real_from_f64(-0.0, 5, 11);
        assert!(one.fpdiv(&pz, Round::Nearest).is_infinity() && one.fpdiv(&pz, Round::Nearest).is_positive());
        assert!(one.fpdiv(&nz, Round::Nearest).is_infinity() && one.fpdiv(&nz, Round::Nearest).is_negative());
    }

    #[test]
    fn nan_compares_false() {
        let nan = FloatingPoint::nan(8, 24);
        let one = FloatingPoint::real_from_f64(1.0, 8, 24);
        assert!(!nan.fp_eq(&nan));
        assert!(!nan.fp_lt(&one) && !nan.fp_gt(&one));
        assert!(nan.is_nan());
    }

    #[test]
    fn normal_subnormal_classification() {
        let one = FloatingPoint::real_from_f64(1.0, 8, 24);
        assert!(one.is_normal() && !one.is_subnormal());
        // Smallest positive subnormal Float32.
        let sub = FloatingPoint::from_bitvec(&bv32(1), 8, 24);
        assert!(sub.is_subnormal() && !sub.is_normal());
    }

    #[test]
    fn arithmetic_basic() {
        let a = FloatingPoint::real_from_f64(1.5, 8, 24);
        let b = FloatingPoint::real_from_f64(2.25, 8, 24);
        let rne = Round::Nearest;
        assert_eq!(a.fpadd(&b, rne).to_f64(), 3.75);
        assert_eq!(a.fpmul(&b, rne).to_f64(), 3.375);
        assert_eq!(b.fpsub(&a, rne).to_f64(), 0.75);
        assert_eq!(FloatingPoint::real_from_f64(9.0, 8, 24).fpsqrt(rne).to_f64(), 3.0);

        // directed rounding: 1/3 at Float32 differs by mode
        let one = FloatingPoint::real_from_f64(1.0, 8, 24);
        let three = FloatingPoint::real_from_f64(3.0, 8, 24);
        let down = one.fpdiv(&three, Round::Down).to_f64();
        let up = one.fpdiv(&three, Round::Up).to_f64();
        assert!(down < up, "toward -inf must be < toward +inf for 1/3");
    }

    #[test]
    fn renormalize_is_ieee_correct() {
        // Ground truth: rounding an MPFR result to (8,24)/(11,53) must equal
        // rounding it to the native f32/f64. Swept over exponents from deep
        // subnormal through normal to overflow, both signs, all mantissas — this
        // includes the subnormal/normal boundary sliver. (Round-to-nearest; Rust's
        // `as` cast is round-to-nearest-even, matching MPFR's Nearest.)
        for &(eb, sb) in &[(8u32, 24u32), (11u32, 53u32)] {
            let emax = 1i32 << (eb - 1);
            let mants = [
                Integer::from(1),
                Integer::from(0b1011u32),
                Integer::from((1u64 << (sb - 1)) | 0xAB),
                (Integer::from(1) << sb) - 1,
            ];
            for exp_off in -(2 * emax + sb as i32 + 8)..=(emax + 8) {
                for m in &mants {
                    for &sign in &[1i32, -1] {
                        let base = FloatingPoint::from_sig_exp(sb, m.clone(), exp_off);
                        let v = if sign < 0 { -base } else { base };
                        // `prune` pushes a value through the format mapping (the
                        // logic formerly in `renormalize`, now inlined in `arith`).
                        let got = FloatingPoint::new(eb, sb, v.clone())
                            .prune(Round::Nearest)
                            .to_f64();
                        // native ground truth (v at prec sb is exact in f64)
                        let truth = if sb == 24 {
                            (v.to_f64() as f32) as f64
                        } else {
                            v.to_f64()
                        };
                        assert!(
                            got == truth || (got.is_nan() && truth.is_nan()),
                            "fmt {eb},{sb} exp={exp_off} sign={sign}: got={got:e} truth={truth:e}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn fpconv_matches_native() {
        // f64 → f32 narrowing under RNE must equal a native `as f32` cast,
        // including the subnormal range (single rounding, no double-rounding) and
        // overflow. Native casts are round-to-nearest-even, matching RNE.
        for &v in &[
            1.0f64,
            -2.5,
            0.1,
            1e-40,             // normal f64 → subnormal f32
            1.4e-45,           // ~smallest f32 subnormal
            7e-46,             // underflows f32 toward zero
            f64::MIN_POSITIVE, // ~2.2e-308 → 0 in f32
            3.0e38,            // near f32 max-normal
            1e40,              // overflows f32
            -1e40,
        ] {
            let wide = FloatingPoint::real_from_f64(v, 11, 53); // exact f64
            let got = wide.fpconv(8, 24, Round::Nearest).to_f64();
            let truth = (v as f32) as f64;
            assert!(
                got == truth || (got.is_nan() && truth.is_nan()),
                "fpconv f64→f32 of {v:e}: got {got:e} want {truth:e}"
            );
        }
        // f32 → f64 widening is exact for every f32 (incl. subnormals).
        for &v in &[1.5f32, -0.25, 1e-40, f32::MIN_POSITIVE, f32::MAX] {
            let narrow = FloatingPoint::real_from_f64(v as f64, 8, 24);
            let got = narrow.fpconv(11, 53, Round::Nearest).to_f64();
            assert_eq!(got, v as f64, "widening {v:e}");
        }
    }

    #[test]
    fn real_from_f64_matches_native() {
        // Ingesting an f64 into f32 must round the EXACT value once (native cast),
        // not fl()+prune double-round. First three are subnormal-f32 cases that
        // double-rounded 1 ULP before the fix.
        for &v in &[
            9.997389223688933e-39f64,
            3.6488262702038793e-39,
            8.722399999575497e-39,
            1.0,
            -2.5,
            0.1,
            1e-40,
            1.4e-45,
            7e-46,
            3.0e38,
            1e40,
            -1e40,
        ] {
            let got = FloatingPoint::real_from_f64(v, 8, 24).to_f64();
            let truth = (v as f32) as f64;
            assert!(
                got == truth || (got.is_nan() && truth.is_nan()),
                "real_from_f64 {v:e}: got {got:e} want {truth:e}"
            );
        }
    }

    #[test]
    fn fpabs_signs_and_zeros() {
        for &(eb, sb) in &[(8u32, 24u32), (11, 53)] {
            let pos = FloatingPoint::real_from_f64(2.5, eb, sb);
            let neg = FloatingPoint::real_from_f64(-2.5, eb, sb);
            // |+x| = +x and |-x| = +x (same magnitude, positive)
            assert_eq!(pos.fpabs().to_f64(), 2.5);
            assert_eq!(neg.fpabs().to_f64(), 2.5);
            assert!(pos.fpabs().is_positive());
            assert!(neg.fpabs().is_positive() && !neg.fpabs().is_negative());
            // signed zeros: |+0| = |-0| = +0
            let pz = FloatingPoint::real_from_f64(0.0, eb, sb);
            let nz = FloatingPoint::real_from_f64(-0.0, eb, sb);
            assert!(pz.fpabs().is_zero() && pz.fpabs().is_positive());
            assert!(nz.fpabs().is_zero() && nz.fpabs().is_positive() && !nz.fpabs().is_negative());
        }
    }

    #[test]
    fn fpabs_inf_and_nan() {
        // Float32 +inf=0x7F800000, -inf=0xFF800000
        let pinf = FloatingPoint::from_bitvec(&bv32(0x7F80_0000), 8, 24);
        let ninf = FloatingPoint::from_bitvec(&bv32(0xFF80_0000), 8, 24);
        assert!(pinf.fpabs().is_infinity() && pinf.fpabs().is_positive());
        assert!(ninf.fpabs().is_infinity() && ninf.fpabs().is_positive());
        // |NaN| is NaN
        assert!(FloatingPoint::nan(8, 24).fpabs().is_nan());
        assert!(FloatingPoint::nan(11, 53).fpabs().is_nan());
    }

    #[test]
    fn fpabs_subnormal() {
        // smallest positive subnormal Float32 (bits=1) and its negative (sign bit set)
        let sub = FloatingPoint::from_bitvec(&bv32(1), 8, 24);
        let neg_sub = FloatingPoint::from_bitvec(&bv32(0x8000_0001), 8, 24);
        assert!(sub.is_subnormal() && neg_sub.is_subnormal());
        // abs of either is the same positive subnormal (bits=1)
        assert_eq!(sub.fpabs().to_bitvec().value, Integer::from(1u64));
        assert_eq!(neg_sub.fpabs().to_bitvec().value, Integer::from(1u64));
    }

    #[test]
    fn fpabs_idempotent_and_matches_neg() {
        for val in [3.75_f64, -3.75, 0.0, -0.0, 1e-30, -1e30] {
            let x = FloatingPoint::real_from_f64(val, 8, 24);
            // result is never negative
            assert!(!x.fpabs().is_negative());
            // idempotent: ||x|| = |x|
            assert_eq!(x.fpabs().fpabs().to_bitvec().value, x.fpabs().to_bitvec().value);
            // |-x| = |x|
            assert_eq!(x.fpneg().fpabs().to_bitvec().value, x.fpabs().to_bitvec().value);
        }
    }
}
