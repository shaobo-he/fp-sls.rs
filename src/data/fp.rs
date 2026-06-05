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

    fn renormalize(value: Float, exp_width: u32, sig_width: u32, round: Round) -> FloatingPoint {
        // overflow → ±∞ or ±max-normal, depending on the mode and sign.
        let max_normal = FloatingPoint::maximum_normal(exp_width, sig_width);
        let abs = Float::with_val(sig_width, value.abs_ref());
        if abs > max_normal.value {
            let neg = value.is_sign_negative();
            let pinf = || FloatingPoint::plus_inf(exp_width, sig_width);
            let ninf = || FloatingPoint::minus_inf(exp_width, sig_width);
            return match round {
                // nearest / ties-away overflow to infinity
                Round::Nearest | Round::AwayZero => {
                    if neg {
                        ninf()
                    } else {
                        pinf()
                    }
                }
                // toward zero never overflows to infinity
                Round::Zero => {
                    if neg {
                        max_normal.fpneg()
                    } else {
                        max_normal
                    }
                }
                // toward +∞
                Round::Up => {
                    if neg {
                        max_normal.fpneg()
                    } else {
                        pinf()
                    }
                }
                // toward −∞
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
            };
        }
        // nonzero but |result| ≤ max subnormal → round into the subnormal grid.
        let max_sub = FloatingPoint::maximum_subnormal(exp_width, sig_width);
        if !value.is_zero() && abs <= max_sub.value {
            return FloatingPoint::round_to_subnormal(&value, exp_width, sig_width, round);
        }
        FloatingPoint::new(exp_width, sig_width, value)
    }

    /// Apply `op` at precision `sig` with rounding `round`, then renormalize.
    fn arith<F>(&self, o: &FloatingPoint, round: Round, op: F) -> FloatingPoint
    where
        F: Fn(&Float, &Float, u32, Round) -> Float,
    {
        assert!(
            self.value.prec() == o.value.prec()
                && self.exp_width == o.exp_width
                && self.sig_width == o.sig_width,
            "invalid arithmetic operation"
        );
        let result = op(&self.value, &o.value, self.prec(), round);
        FloatingPoint::renormalize(result, self.exp_width, self.sig_width, round)
    }

    pub fn fpadd(&self, o: &FloatingPoint, round: Round) -> FloatingPoint {
        self.arith(o, round, |a, b, p, r| Float::with_val_round(p, a + b, r).0)
    }
    pub fn fpsub(&self, o: &FloatingPoint, round: Round) -> FloatingPoint {
        self.arith(o, round, |a, b, p, r| Float::with_val_round(p, a - b, r).0)
    }
    pub fn fpmul(&self, o: &FloatingPoint, round: Round) -> FloatingPoint {
        self.arith(o, round, |a, b, p, r| Float::with_val_round(p, a * b, r).0)
    }
    pub fn fpdiv(&self, o: &FloatingPoint, round: Round) -> FloatingPoint {
        self.arith(o, round, |a, b, p, r| Float::with_val_round(p, a / b, r).0)
    }
    pub fn fpsqrt(&self, round: Round) -> FloatingPoint {
        self.arith(self, round, |a, _, p, r| {
            Float::with_val_round(p, a.sqrt_ref(), r).0
        })
    }

    /// `(fp/prune fp)` — push a value through renormalization in mode `round`.
    pub fn prune(&self, round: Round) -> FloatingPoint {
        self.arith(self, round, |a, _, p, r| Float::with_val_round(p, a, r).0)
    }

    /// `(fp/round-to-subnormal v exp sig)` in mode `round`.
    fn round_to_subnormal(
        v: &Float,
        exp_width: u32,
        sig_width: u32,
        round: Round,
    ) -> FloatingPoint {
        let subnormal_min = FloatingPoint::from_bitvec(
            &BitVec::new(exp_width + sig_width, Integer::from(1)),
            exp_width,
            sig_width,
        )
        .value;
        let pv = Float::with_val(sig_width, v.abs_ref());
        let (s1, p1) = pv.to_integer_exp().expect("finite nonzero");
        let (s2, p2) = subnormal_min.to_integer_exp().expect("finite nonzero");
        let d = p1 - p2;
        let (num, den) = if d >= 0 {
            (s1 << (d as u32), s2)
        } else {
            (s1, s2 << ((-d) as u32))
        };
        let neg = v.is_sign_negative();
        let r = round_rational(num, &den, round, neg);
        if r < 1 {
            FloatingPoint::real_from_f64(if neg { -0.0 } else { 0.0 }, exp_width, sig_width)
        } else {
            let rv = FloatingPoint::from_bitvec(
                &BitVec::new(exp_width + sig_width, r),
                exp_width,
                sig_width,
            );
            if neg {
                rv.fpneg()
            } else {
                rv
            }
        }
    }

    /// `(eval/fpconv fp dest-exp dest-sig)` in mode `round`.
    pub fn fpconv(&self, dest_exp: u32, dest_sig: u32, round: Round) -> FloatingPoint {
        let copied = FloatingPoint::new(
            dest_exp,
            dest_sig,
            Float::with_val_round(dest_sig, &self.value, round).0,
        );
        if self.is_nan() || self.is_infinity() {
            copied
        } else {
            copied.prune(round)
        }
    }

    // ----- conversions to/from a real number -----

    fn real_from_float(value: Float, exp_width: u32, sig_width: u32) -> FloatingPoint {
        FloatingPoint::new(exp_width, sig_width, value).prune(Round::Nearest)
    }

    /// `(real->FloatingPoint rv exp sig)` for a machine double `rv`.
    pub fn real_from_f64(rv: f64, exp_width: u32, sig_width: u32) -> FloatingPoint {
        FloatingPoint::real_from_float(fl(sig_width, rv), exp_width, sig_width)
    }

    /// `(real->FloatingPoint rv exp sig)` for an exact rational `rv`
    /// (used by the Z3 real-model path).
    pub fn real_from_rational(rv: &Rational, exp_width: u32, sig_width: u32) -> FloatingPoint {
        FloatingPoint::real_from_float(fl(sig_width, rv), exp_width, sig_width)
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
            let mag = if Integer::from(exp) >= threshold {
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
}
