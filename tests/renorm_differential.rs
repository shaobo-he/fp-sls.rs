//! Differential soundness fuzz of fp.rs arithmetic vs. an INDEPENDENT exact
//! rational IEEE oracle, for all five rounding modes.
//!
//! Audits commit 9086440 ("detect overflow/subnormal by exponent in
//! renormalize"). The oracle is implemented purely with rug::Integer/Rational
//! (no rug::Float) so it shares no rounding code with the code under test and
//! performs a SINGLE rounding of the exact result (no double-rounding).
//!
//! Strategy: build operands from random IEEE bit patterns (so each operand is
//! exactly representable), decode each operand's EXACT rational value here in
//! the test, compute the exact rational result of +,-,*,/ (exact for dyadic
//! inputs), and round it once with the oracle. Compare to fp.rs's
//! fpadd/fpsub/fpmul/fpdiv bit pattern.

#![allow(dead_code)] // a few helper builders kept for documentation/coverage
// This is a self-contained independent IEEE oracle; favor explicit, redundant
// forms over clippy's stylistic suggestions so the math stays auditable.
#![allow(clippy::useless_conversion)]
#![allow(clippy::needless_return)]
#![allow(clippy::cmp_owned)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::single_match)]

use fp_sls::data::bitvec::{two_pow, BitVec};
use fp_sls::data::fp::FloatingPoint;
use rug::float::Round;
use rug::{Integer, Rational};

const MODES: [(&str, Round); 5] = [
    ("RNE", Round::Nearest),
    ("RTZ", Round::Zero),
    ("RTP", Round::Up),
    ("RTN", Round::Down),
    ("RNA", Round::AwayZero),
];

// ----------------------------------------------------------------------------
// Tiny deterministic PRNG (xorshift64*) so the test is reproducible and has no
// external dependency on the crate's Rng (which is geared toward special-value
// heavy sampling).
// ----------------------------------------------------------------------------
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn bits(&mut self, w: u32) -> Integer {
        // produce a w-bit unsigned integer (w up to 64)
        if w <= 64 {
            let v = self.next() >> (64 - w);
            Integer::from(v)
        } else {
            unreachable!("widths used are <= 64")
        }
    }
}

// ----------------------------------------------------------------------------
// Format helpers (independent reimplementation).
// ----------------------------------------------------------------------------

#[derive(Clone, Copy)]
struct Fmt {
    eb: u32,
    sb: u32,
}
impl Fmt {
    fn bias(&self) -> i64 {
        (1i64 << (self.eb - 1)) - 1
    }
    fn p(&self) -> u32 {
        self.sb
    } // precision (with hidden bit)
    fn emin(&self) -> i64 {
        1 - self.bias()
    } // smallest normal unbiased exp
    fn emax(&self) -> i64 {
        self.bias()
    } // largest normal unbiased exp
    fn width(&self) -> u32 {
        self.eb + self.sb
    }
}

/// Decode an IEEE bit pattern to the EXACT rational it denotes, plus a tag of
/// what kind of value it is. Fully independent of fp.rs. Returns None for the
/// exact value if it is NaN/inf (sign still meaningful for inf).
#[derive(Clone)]
enum Decoded {
    Nan,
    Inf { neg: bool },
    /// finite, exact value (zero handled here too, with signed zero via `neg`)
    Finite { val: Rational, neg_zero: bool },
}

fn decode_bits(bits: &Integer, f: Fmt) -> Decoded {
    let sig_wo = f.sb - 1;
    let sig = Integer::from(bits & &(two_pow(sig_wo) - Integer::from(1)));
    let exp = Integer::from(&(bits.clone() >> sig_wo) & &(two_pow(f.eb) - Integer::from(1)));
    let sign_neg = bits.get_bit(f.eb + sig_wo);
    let all_ones = two_pow(f.eb) - Integer::from(1);
    if exp == all_ones {
        if sig == 0 {
            return Decoded::Inf { neg: sign_neg };
        } else {
            return Decoded::Nan;
        }
    }
    if exp == 0 {
        if sig == 0 {
            return Decoded::Finite {
                val: Rational::from(0),
                neg_zero: sign_neg,
            };
        }
        // subnormal: value = (-1)^s * sig * 2^(emin - (p-1))
        let shift = f.emin() - (f.p() as i64 - 1); // negative
        let mut r = scale_pow2(Rational::from(sig), shift);
        if sign_neg {
            r = -r;
        }
        return Decoded::Finite {
            val: r,
            neg_zero: false,
        };
    }
    // normal: value = (-1)^s * (2^(p-1) + sig) * 2^(E - bias - (p-1))
    let m = two_pow(f.sb - 1) + sig;
    let e_unbiased = exp.to_i64().unwrap() - f.bias();
    let shift = e_unbiased - (f.p() as i64 - 1);
    let mut r = scale_pow2(Rational::from(m), shift);
    if sign_neg {
        r = -r;
    }
    Decoded::Finite {
        val: r,
        neg_zero: false,
    }
}

/// r * 2^k for signed k, exact in Rational.
fn scale_pow2(r: Rational, k: i64) -> Rational {
    if k >= 0 {
        r * Integer::from(Integer::from(1) << (k as u32))
    } else {
        r / Integer::from(Integer::from(1) << ((-k) as u32))
    }
}

/// The rounding semantics the oracle applies. We distinguish two readings of
/// the SMT-LIB `roundNearestTiesToAway` constant:
///   * `MpfrFaithful`  — model exactly what rug/MPFR does for each `Round`
///     variant fp.rs passes in. CRUCIALLY `Round::AwayZero` in MPFR is
///     *directed* "round away from zero" (MPFR_RNDA), NOT nearest-ties-away.
///     This pass audits whether `renormalize` is correct given fp.rs's *actual*
///     in-effect semantics.
///   * `SmtLib`        — the IEEE/SMT-LIB intent: RNA = round to nearest, ties
///     away from zero. fp.rs maps RNA -> Round::AwayZero, so this pass measures
///     fp.rs's divergence from the SMT-LIB spec.
#[derive(Clone, Copy, PartialEq)]
enum Sem {
    MpfrFaithful,
    SmtLib,
}

// ----------------------------------------------------------------------------
// Round an integer ratio num/den (both > 0, the MAGNITUDE) to an integer per
// mode, with `neg` = sign of the value. Independent of fp.rs's round_rational.
// ----------------------------------------------------------------------------
fn round_div(num: &Integer, den: &Integer, mode: Round, neg: bool, sem: Sem) -> Integer {
    let (q, r) = Integer::from(num).div_rem_euc(Integer::from(den));
    if r == 0 {
        return q;
    }
    let two_r = Integer::from(&r * 2);
    let up = match mode {
        Round::Zero => false,
        Round::Up => !neg,
        Round::Down => neg,
        Round::Nearest => match two_r.cmp(den) {
            std::cmp::Ordering::Less => false,
            std::cmp::Ordering::Greater => true,
            std::cmp::Ordering::Equal => q.is_odd(),
        },
        Round::AwayZero => match sem {
            // MPFR_RNDA: directed — round magnitude up on ANY inexact result.
            Sem::MpfrFaithful => true,
            // SMT-LIB RNA: round to nearest, ties away from zero.
            Sem::SmtLib => match two_r.cmp(den) {
                std::cmp::Ordering::Less => false,
                std::cmp::Ordering::Greater => true,
                std::cmp::Ordering::Equal => true,
            },
        },
        _ => false,
    };
    if up {
        q + Integer::from(1)
    } else {
        q
    }
}

// ----------------------------------------------------------------------------
// THE ORACLE: round an exact rational to an IEEE (eb,sb) bit pattern, once.
// Returns the full bit pattern (sign|exp|sig) as an Integer.
// ----------------------------------------------------------------------------
fn round_rational_to_ieee(exact: &Rational, f: Fmt, mode: Round, sem: Sem) -> Integer {
    let sign_neg = *exact < 0;
    let sign_bit = if sign_neg {
        Integer::from(1) << (f.eb + f.sb - 1)
    } else {
        Integer::from(0)
    };

    // zero -> +0 / -0 preserving sign
    if *exact == 0 {
        return sign_bit; // exp=0, sig=0
    }

    let mag = exact.clone().abs();
    let p = f.p() as i64;

    // Find floor(log2(mag)) = E such that 2^E <= mag < 2^(E+1).
    let e = floor_log2(&mag);

    // Candidate: round mag to p significant bits with exponent E.
    // The grid step for an exponent E normal is 2^(E - (p-1)).
    // Represent mag = num/den exactly, and the significand integer is
    // round( mag / 2^(E-(p-1)) ) = round( mag * 2^((p-1)-E) ).
    // Use directed integer rounding.

    // For NORMAL candidate (E >= emin):
    //   sig_int in [2^(p-1), 2^p]; if it overflows to 2^p, E increments.
    // For SUBNORMAL candidate (E < emin):
    //   step exponent is fixed at emin-(p-1); sig_int = round(mag * 2^((p-1)-emin)).
    //   sig_int in [0 .. 2^(p-1)]; if == 2^(p-1) it becomes the smallest normal.

    let emin = f.emin();
    let emax = f.emax();

    if e >= emin {
        // normal candidate
        let scale = (p - 1) - e; // mag * 2^scale = significand magnitude
        let (num, den) = scaled_ratio(&mag, scale);
        let mut sig_int = round_div(&num, &den, mode, sign_neg, sem);
        let mut exp_unbiased = e;
        // carry: rounding may produce 2^p (e.g. 1.111..1 -> 10.000)
        if sig_int == two_pow(p as u32) {
            sig_int >>= 1; // == 2^(p-1)
            exp_unbiased += 1;
        }
        // now sig_int in [2^(p-1), 2^p)
        if exp_unbiased > emax {
            return overflow(f, mode, sign_neg);
        }
        // encode normal
        let biased = exp_unbiased + f.bias();
        let frac = Integer::from(&sig_int - &two_pow(p as u32 - 1));
        let exp_field = Integer::from(biased) << (f.sb - 1);
        return sign_bit + exp_field + frac;
    } else {
        // subnormal (or rounds up to smallest normal) candidate
        let scale = (p - 1) - emin; // step exponent = emin-(p-1); divide by it
        let (num, den) = scaled_ratio(&mag, scale);
        let sig_int = round_div(&num, &den, mode, sign_neg, sem);
        if sig_int == 0 {
            // underflows to (signed) zero
            return sign_bit;
        }
        if sig_int >= two_pow(p as u32 - 1) {
            // rounded up to smallest normal: exp field = 1, frac = sig_int - 2^(p-1)
            // (sig_int can be exactly 2^(p-1) here; never larger by 1 ulp logic)
            let frac = Integer::from(&sig_int - &two_pow(p as u32 - 1));
            let exp_field = Integer::from(1) << (f.sb - 1);
            return sign_bit + exp_field + frac;
        }
        // genuine subnormal: exp field = 0, sig field = sig_int
        return sign_bit + sig_int;
    }
}

/// mag * 2^scale expressed as (num, den) with den > 0, both integers.
fn scaled_ratio(mag: &Rational, scale: i64) -> (Integer, Integer) {
    // mag = n/d.  mag*2^scale = (n * 2^scale)/d   or   n/(d*2^-scale)
    let n = Integer::from(mag.numer());
    let d = Integer::from(mag.denom());
    if scale >= 0 {
        (n << (scale as u32), d)
    } else {
        (n, d << ((-scale) as u32))
    }
}

/// Exact comparison: is n/d >= 2^e ?  (n,d > 0, e any integer)
/// n/d >= 2^e  <=>  n >= d*2^e.  For e>=0 multiply d by 2^e; for e<0 multiply
/// n by 2^(-e) instead (both sides stay integers — no flooring, exact).
fn ratio_ge_pow2(n: &Integer, d: &Integer, e: i64) -> bool {
    if e >= 0 {
        Integer::from(n) >= Integer::from(d << (e as u32))
    } else {
        Integer::from(n << ((-e) as u32)) >= *d
    }
}

/// floor(log2(mag)) for a positive rational: the unique E with 2^E <= mag < 2^(E+1).
fn floor_log2(mag: &Rational) -> i64 {
    let n = Integer::from(mag.numer());
    let d = Integer::from(mag.denom());
    debug_assert!(n > 0 && d > 0);
    // Estimate from bit lengths, then adjust by exact comparison.
    let bn = n.significant_bits() as i64 - 1; // floor(log2(n))
    let bd = d.significant_bits() as i64 - 1; // floor(log2(d))
    let mut e = bn - bd;
    // Invariant target: 2^e <= n/d < 2^(e+1).
    // Move up while n/d >= 2^(e+1); move down while n/d < 2^e.
    while ratio_ge_pow2(&n, &d, e + 1) {
        e += 1;
    }
    while !ratio_ge_pow2(&n, &d, e) {
        e -= 1;
    }
    e
}

// ----------------------------------------------------------------------------
// Overflow encoding per mode/sign.
// ----------------------------------------------------------------------------
fn overflow(f: Fmt, mode: Round, neg: bool) -> Integer {
    let sign_bit = if neg {
        Integer::from(1) << (f.eb + f.sb - 1)
    } else {
        Integer::from(0)
    };
    let to_inf = |neg: bool| -> Integer {
        let s = if neg {
            Integer::from(1) << (f.eb + f.sb - 1)
        } else {
            Integer::from(0)
        };
        let exp_field = (two_pow(f.eb) - Integer::from(1)) << (f.sb - 1);
        s + exp_field
    };
    let max_normal = |neg: bool| -> Integer {
        let s = if neg {
            Integer::from(1) << (f.eb + f.sb - 1)
        } else {
            Integer::from(0)
        };
        // exp field = all ones - 1, frac = all ones
        let exp_field = (two_pow(f.eb) - Integer::from(2)) << (f.sb - 1);
        let frac = two_pow(f.sb - 1) - Integer::from(1);
        s + exp_field + frac
    };
    let _ = sign_bit;
    match mode {
        Round::Nearest | Round::AwayZero => to_inf(neg),
        Round::Zero => max_normal(neg),
        Round::Up => {
            if neg {
                max_normal(true)
            } else {
                to_inf(false)
            }
        }
        Round::Down => {
            if neg {
                to_inf(true)
            } else {
                max_normal(false)
            }
        }
        _ => to_inf(neg),
    }
}

// ----------------------------------------------------------------------------
// Build an FP operand from a bit pattern. Returns (FloatingPoint, Decoded).
// ----------------------------------------------------------------------------
fn make_operand(bits: &Integer, f: Fmt) -> (FloatingPoint, Decoded) {
    let bv = BitVec::new(f.width(), bits.clone());
    let fp = FloatingPoint::from_bitvec(&bv, f.eb, f.sb);
    (fp, decode_bits(bits, f))
}

/// Convert an fp.rs result to a comparable "kind+bits". For finite results we
/// use to_bitvec(); for NaN we tag separately (no unique bits).
enum ResultBits {
    Nan,
    Bits(Integer),
}
fn fp_result_bits(fp: &FloatingPoint) -> ResultBits {
    if fp.is_nan() {
        ResultBits::Nan
    } else {
        ResultBits::Bits(fp.to_bitvec().value)
    }
}

// ----------------------------------------------------------------------------
// Compute the IEEE-correct result of a binary op on two decoded operands.
// Returns Some(bits) for a finite/inf result, or "Nan" / "Inf" appropriately.
// We handle special operand combos (inf/nan/zero) per IEEE so the oracle covers
// the same input space; but the FUZZER focuses on FINITE x FINITE for the
// renormalize audit and we filter accordingly when special handling is fiddly.
// ----------------------------------------------------------------------------
#[derive(Clone, Copy)]
enum Op {
    Add,
    Sub,
    Mul,
    Div,
}

/// Returns Some(oracle_bits) when both operands are finite (incl. zeros) and the
/// op yields a finite real or a well-defined overflow; returns None when the
/// case involves inf/nan operands or 0/0, inf-inf etc. (skipped — not the
/// subject of this renormalize audit). `is_special` indicates a NaN result.
enum Oracle {
    Bits(Integer),
    Nan,
    Skip,
}

fn oracle(op: Op, a: &Decoded, b: &Decoded, f: Fmt, mode: Round, sem: Sem) -> Oracle {
    use Decoded::*;
    // Any NaN operand -> skip (special handling, not renormalize's concern).
    if matches!(a, Nan) || matches!(b, Nan) {
        return Oracle::Skip;
    }
    // Inf operands -> skip (special arithmetic; renormalize returns them as-is).
    if matches!(a, Inf { .. }) || matches!(b, Inf { .. }) {
        return Oracle::Skip;
    }
    // both finite now
    let (av, aneg0) = match a {
        Finite { val, neg_zero } => (val.clone(), *neg_zero),
        _ => unreachable!(),
    };
    let (bv, bneg0) = match b {
        Finite { val, neg_zero } => (val.clone(), *neg_zero),
        _ => unreachable!(),
    };

    let _ = (aneg0, bneg0);
    // Determine the EXACT rational result, then round ONCE with the oracle.
    //
    // We DELIBERATELY skip cases where an operand is exactly zero or the exact
    // result is zero: signed-zero tie-breaking is governed by MPFR's add/sub/mul
    // semantics, NOT by renormalize (the subject of this audit). Including them
    // would test MPFR's zero-sign rules rather than the rounding/overflow/
    // subnormal logic we care about, and could yield "discrepancies" that are
    // really just oracle modeling gaps. All NONZERO finite results — which is
    // where every rounding/overflow/subnormal decision lives — are compared.
    match op {
        Op::Add | Op::Sub => {
            if av == 0 || bv == 0 {
                return Oracle::Skip;
            }
            let res = if matches!(op, Op::Sub) {
                Rational::from(&av - &bv)
            } else {
                Rational::from(&av + &bv)
            };
            if res == 0 {
                return Oracle::Skip; // exact cancellation -> signed-zero rule
            }
            Oracle::Bits(round_rational_to_ieee(&res, f, mode, sem))
        }
        Op::Mul => {
            if av == 0 || bv == 0 {
                return Oracle::Skip;
            }
            let res = Rational::from(&av * &bv);
            // product of two nonzero finite values is nonzero
            Oracle::Bits(round_rational_to_ieee(&res, f, mode, sem))
        }
        Op::Div => {
            if bv == 0 {
                if av == 0 {
                    return Oracle::Nan; // 0/0 -> NaN
                }
                return Oracle::Skip; // x/0 -> signed inf (zero-sign dependent)
            }
            if av == 0 {
                return Oracle::Skip; // 0/x -> signed zero
            }
            let res = Rational::from(&av / &bv);
            Oracle::Bits(round_rational_to_ieee(&res, f, mode, sem))
        }
    }
}

fn zero_bits(f: Fmt, neg: bool) -> Integer {
    if neg {
        Integer::from(1) << (f.eb + f.sb - 1)
    } else {
        Integer::from(0)
    }
}
fn inf_bits(f: Fmt, neg: bool) -> Integer {
    let s = zero_bits(f, neg);
    let exp_field = (two_pow(f.eb) - Integer::from(1)) << (f.sb - 1);
    s + exp_field
}

// ----------------------------------------------------------------------------
// Determine the regime of an exact result (for classifying discrepancies).
// ----------------------------------------------------------------------------
fn regime(res: &Rational, f: Fmt) -> &'static str {
    if *res == 0 {
        return "zero";
    }
    let mag = res.clone().abs();
    let e = floor_log2(&mag);
    let emin = f.emin();
    let emax = f.emax();
    // smallest normal magnitude is 2^emin; largest finite ~ 2^(emax+1).
    if e > emax {
        "overflow"
    } else if e < emin {
        // could still round up to smallest normal -> call it subnormal/sliver
        // distinguish the half-ulp sliver: between max_subnormal and min_normal,
        // i.e. e == emin-1 region where rounding may land on min normal.
        if e == emin - 1 {
            "sliver"
        } else {
            "subnormal"
        }
    } else {
        "normal"
    }
}

fn exact_result(op: Op, a: &Decoded, b: &Decoded) -> Option<Rational> {
    use Decoded::*;
    let av = match a {
        Finite { val, .. } => val.clone(),
        _ => return None,
    };
    let bv = match b {
        Finite { val, .. } => val.clone(),
        _ => return None,
    };
    Some(match op {
        Op::Add => Rational::from(&av + &bv),
        Op::Sub => Rational::from(&av - &bv),
        Op::Mul => Rational::from(&av * &bv),
        Op::Div => {
            if bv == 0 {
                return None;
            }
            Rational::from(&av / &bv)
        }
    })
}

fn run_op(op: Op, a: &FloatingPoint, b: &FloatingPoint, mode: Round) -> FloatingPoint {
    match op {
        Op::Add => a.fpadd(b, mode),
        Op::Sub => a.fpsub(b, mode),
        Op::Mul => a.fpmul(b, mode),
        Op::Div => a.fpdiv(b, mode),
    }
}

fn op_name(op: Op) -> &'static str {
    match op {
        Op::Add => "add",
        Op::Sub => "sub",
        Op::Mul => "mul",
        Op::Div => "div",
    }
}

// ----------------------------------------------------------------------------
// Operand generators biased toward boundary regimes.
// ----------------------------------------------------------------------------

/// Random fully-general bit pattern.
fn gen_random(rng: &mut Lcg, f: Fmt) -> Integer {
    rng.bits(f.width())
}

/// Operand near +/-max_normal / large normals (drives overflow on add/mul).
fn gen_near_max(rng: &mut Lcg, f: Fmt) -> Integer {
    let sign = Integer::from(rng.below(2)) << (f.eb + f.sb - 1);
    // exp field in [all_ones-3 .. all_ones-1] = largest few normals
    let all_ones = (1u64 << f.eb) - 1;
    let efield = all_ones - 1 - rng.below(3);
    let frac = rng.bits(f.sb - 1);
    sign + (Integer::from(efield) << (f.sb - 1)) + frac
}

/// Operand in the subnormal range (exp field == 0, nonzero frac).
fn gen_subnormal(rng: &mut Lcg, f: Fmt) -> Integer {
    let sign = Integer::from(rng.below(2)) << (f.eb + f.sb - 1);
    let mut frac = rng.bits(f.sb - 1);
    if frac == 0 {
        frac = Integer::from(1);
    }
    sign + frac
}

/// Operand near the smallest normals (exp field in [1..4]) — products/quotients
/// of these probe the subnormal grid and the sliver.
fn gen_near_min_normal(rng: &mut Lcg, f: Fmt) -> Integer {
    let sign = Integer::from(rng.below(2)) << (f.eb + f.sb - 1);
    let efield = 1 + rng.below(4);
    let frac = rng.bits(f.sb - 1);
    sign + (Integer::from(efield) << (f.sb - 1)) + frac
}

/// A small-magnitude normal (exp field around bias, i.e. near 1.0) — useful as
/// a multiplier/divisor to push another operand across a boundary.
fn gen_small_mult(rng: &mut Lcg, f: Fmt) -> Integer {
    let sign = Integer::from(rng.below(2)) << (f.eb + f.sb - 1);
    let bias = (1u64 << (f.eb - 1)) - 1;
    // exp field in [bias-2 .. bias+2] -> magnitude in ~[0.25, 8)
    let lo = bias - 2;
    let efield = lo + rng.below(5);
    let frac = rng.bits(f.sb - 1);
    sign + (Integer::from(efield) << (f.sb - 1)) + frac
}

type Gen = fn(&mut Lcg, Fmt) -> Integer;

// ----------------------------------------------------------------------------
// The differential driver.
// ----------------------------------------------------------------------------

struct Stats {
    total: u64,
    skipped: u64,
    compared: u64,
    discrepancies: u64,
    by_regime: std::collections::BTreeMap<String, u64>,
    by_mode_regime: std::collections::BTreeMap<String, u64>,
    examples: Vec<String>,
    // regimes actually exercised (had at least one comparison)
    regimes_seen: std::collections::BTreeSet<String>,
    modes_seen: std::collections::BTreeSet<String>,
}
impl Stats {
    fn new() -> Self {
        Stats {
            total: 0,
            skipped: 0,
            compared: 0,
            discrepancies: 0,
            by_regime: Default::default(),
            by_mode_regime: Default::default(),
            examples: vec![],
            regimes_seen: Default::default(),
            modes_seen: Default::default(),
        }
    }
}

fn run_pair(
    stats: &mut Stats,
    op: Op,
    abits: &Integer,
    bbits: &Integer,
    f: Fmt,
    mode_name: &str,
    mode: Round,
    sem: Sem,
) {
    stats.total += 1;
    let (fa, da) = make_operand(abits, f);
    let (fb, db) = make_operand(bbits, f);

    let orc = oracle(op, &da, &db, f, mode, sem);
    match orc {
        Oracle::Skip => {
            stats.skipped += 1;
            return;
        }
        _ => {}
    }
    stats.compared += 1;
    stats.modes_seen.insert(mode_name.to_string());

    // classify regime from exact result (when finite)
    let reg = match exact_result(op, &da, &db) {
        Some(r) => regime(&r, f).to_string(),
        None => "special".to_string(),
    };
    stats.regimes_seen.insert(reg.clone());

    let got = run_op(op, &fa, &fb, mode);
    let got_bits = fp_result_bits(&got);

    let mismatch = match (&orc, &got_bits) {
        (Oracle::Nan, ResultBits::Nan) => false,
        (Oracle::Nan, ResultBits::Bits(_)) => true,
        (Oracle::Bits(_), ResultBits::Nan) => true,
        (Oracle::Bits(ob), ResultBits::Bits(gb)) => ob != gb,
        (Oracle::Skip, _) => unreachable!(),
    };

    if mismatch {
        stats.discrepancies += 1;
        *stats.by_regime.entry(reg.clone()).or_insert(0) += 1;
        *stats
            .by_mode_regime
            .entry(format!("{}/{}", mode_name, reg))
            .or_insert(0) += 1;
        if stats.examples.len() < 60 {
            let exres = exact_result(op, &da, &db);
            let ob = match &orc {
                Oracle::Bits(b) => format!("{}", b),
                Oracle::Nan => "NaN".to_string(),
                Oracle::Skip => unreachable!(),
            };
            let gb = match &got_bits {
                ResultBits::Bits(b) => format!("{}", b),
                ResultBits::Nan => "NaN".to_string(),
            };
            let exr = exres
                .map(|r| {
                    // print as decimal approx to keep it short
                    let fl = rug::Float::with_val(80, &r);
                    format!("{:e}", fl)
                })
                .unwrap_or_else(|| "special".to_string());
            stats.examples.push(format!(
                "op={} fmt=({},{}) mode={} regime={} a_bits={} b_bits={} exact={} oracle_bits={} got_bits={}",
                op_name(op),
                f.eb,
                f.sb,
                mode_name,
                reg,
                abits,
                bbits,
                exr,
                ob,
                gb,
            ));
        }
    }
}

fn fuzz(stats: &mut Stats, seed: u64, iters: u64, sem: Sem) {
    let mut rng = Lcg(seed);
    let fmts = [Fmt { eb: 8, sb: 24 }, Fmt { eb: 11, sb: 53 }];
    let gens: [Gen; 6] = [
        gen_random,
        gen_near_max,
        gen_subnormal,
        gen_near_min_normal,
        gen_small_mult,
        gen_random,
    ];
    let ops = [Op::Add, Op::Sub, Op::Mul, Op::Div];

    for f in fmts {
        for _ in 0..iters {
            // pick two operand generators (independently) to hit cross-regime cases
            let ga = gens[rng.below(gens.len() as u64) as usize];
            let gb = gens[rng.below(gens.len() as u64) as usize];
            let abits = ga(&mut rng, f);
            let bbits = gb(&mut rng, f);
            for &op in &ops {
                for (mn, mode) in MODES {
                    run_pair(stats, op, &abits, &bbits, f, mn, mode, sem);
                }
            }
        }
    }
}

// ----------------------------------------------------------------------------
// Targeted deterministic cases: explicitly engineer overflow-boundary,
// subnormal, and sliver results so coverage does not depend on the RNG.
// ----------------------------------------------------------------------------
fn targeted(stats: &mut Stats, sem: Sem) {
    let fmts = [Fmt { eb: 8, sb: 24 }, Fmt { eb: 11, sb: 53 }];
    for f in fmts {
        let all_ones = (1u64 << f.eb) - 1;
        let bias = (1u64 << (f.eb - 1)) - 1;
        let sig_wo = f.sb - 1;

        // max_normal bits = exp all_ones-1, frac all_ones
        let max_normal = (Integer::from(all_ones - 1) << sig_wo) + (two_pow(sig_wo) - Integer::from(1));
        // smallest normal = exp 1, frac 0
        let min_normal = Integer::from(1) << sig_wo;
        // largest subnormal = exp 0, frac all_ones
        let max_sub = two_pow(sig_wo) - Integer::from(1);
        // smallest subnormal = 1
        let min_sub = Integer::from(1);
        // 2.0 = exp bias+1, frac 0
        let two = Integer::from(bias + 1) << sig_wo;
        // 0.5 = exp bias-1
        let half = Integer::from(bias - 1) << sig_wo;
        // 1.0
        let one = Integer::from(bias) << sig_wo;

        // (a) overflow boundary: max_normal + max_normal (overflows), max_normal * 2,
        //     max_normal + ulp/2-ish via small adds, etc.
        let cases: Vec<(Op, Integer, Integer, &str)> = vec![
            (Op::Add, max_normal.clone(), max_normal.clone(), "ovf"),
            (Op::Mul, max_normal.clone(), two.clone(), "ovf"),
            (Op::Mul, max_normal.clone(), max_normal.clone(), "ovf"),
            (Op::Sub, max_normal.clone(), Integer::from(&max_normal | (Integer::from(1) << (f.eb + sig_wo))), "ovf"), // max - (-max)
            // subnormal-producing
            (Op::Mul, min_normal.clone(), half.clone(), "sub"),         // min_normal/2 -> max_subnormal+?
            (Op::Div, min_normal.clone(), two.clone(), "sub"),          // min_normal/2
            (Op::Mul, min_sub.clone(), half.clone(), "sub"),            // tiny -> underflow toward 0
            (Op::Div, min_sub.clone(), two.clone(), "sub"),             // half-ulp subnormal -> RNE/dir differ
            (Op::Add, max_sub.clone(), min_sub.clone(), "sub"),         // max_sub + min_sub = min_normal
            (Op::Mul, max_sub.clone(), one.clone(), "sub"),
            // sliver: results between max_subnormal and min_normal
            (Op::Div, min_normal.clone(), Integer::from(bias) << sig_wo, "sliver-ish"), // /1.0
            (Op::Mul, max_sub.clone(), two.clone(), "back-to-normal"),
            // exact ties in subnormal grid: min_subnormal * 1.5
            (Op::Mul, min_sub.clone(), (Integer::from(bias) << sig_wo) + (Integer::from(1) << (sig_wo - 1)), "sub-tie"),
            // three-quarters * min_sub etc.
            (Op::Mul, Integer::from(3) * &min_sub, half.clone(), "sub-tie"),
        ];

        for (op, ab, bb, _tag) in cases {
            for (mn, mode) in MODES {
                run_pair(stats, op, &ab, &bb, f, mn, mode, sem);
            }
            // also try negated operands to exercise directed-mode sign logic
            let neg_a = Integer::from(&ab | (Integer::from(1) << (f.eb + sig_wo)));
            for (mn, mode) in MODES {
                run_pair(stats, op, &neg_a, &bb, f, mn, mode, sem);
            }
        }
    }
}

const SEEDS: [u64; 3] = [
    0x1234_5678_9abc_def0,
    0xdead_beef_cafe_babe,
    0x0f0f_0f0f_1357_9bdf,
];

fn run_all(sem: Sem) -> Stats {
    let mut stats = Stats::new();
    targeted(&mut stats, sem);
    for seed in SEEDS {
        fuzz(&mut stats, seed, 4000, sem);
    }
    stats
}

fn report(label: &str, stats: &Stats) {
    eprintln!("==== {label} ====");
    eprintln!("total op-instances     : {}", stats.total);
    eprintln!("skipped (inf/nan/zero) : {}", stats.skipped);
    eprintln!("compared               : {}", stats.compared);
    eprintln!("discrepancies          : {}", stats.discrepancies);
    eprintln!("modes covered          : {:?}", stats.modes_seen);
    eprintln!("regimes covered        : {:?}", stats.regimes_seen);
    eprintln!("discrepancies by regime    : {:?}", stats.by_regime);
    eprintln!("discrepancies by mode/regime: {:?}", stats.by_mode_regime);
    for (i, ex) in stats.examples.iter().take(20).enumerate() {
        eprintln!("  example[{}]: {}", i, ex);
    }
}

fn bits_of(fp: &FloatingPoint) -> Integer {
    match fp_result_bits(fp) {
        ResultBits::Bits(b) => b,
        ResultBits::Nan => panic!("unexpected NaN result"),
    }
}

fn oracle_bits(op: Op, a: &Decoded, b: &Decoded, f: Fmt, mode: Round, sem: Sem) -> Integer {
    match oracle(op, a, b, f, mode, sem) {
        Oracle::Bits(b) => b,
        Oracle::Nan => panic!("oracle produced NaN"),
        Oracle::Skip => panic!("oracle skipped"),
    }
}

/// MAIN REGRESSION: after the fix, fp.rs must match a SINGLE correct IEEE
/// rounding (the true SMT-LIB semantics: RNA = nearest-ties-away) in EVERY mode
/// and EVERY regime — normal, overflow, subnormal, and the sliver — with zero
/// discrepancies. Before the fix this failed in two places (RNA every regime;
/// nearest-mode subnormal double-rounding).
#[test]
fn fp_matches_ieee_oracle_all_modes_all_regimes() {
    let stats = run_all(Sem::SmtLib);
    report("differential audit vs SMT-LIB/IEEE oracle (post-fix)", &stats);

    for m in ["RNE", "RTZ", "RTP", "RTN", "RNA"] {
        assert!(stats.modes_seen.contains(m), "mode {m} never compared");
    }
    for r in ["normal", "overflow", "subnormal", "sliver"] {
        assert!(stats.regimes_seen.contains(r), "regime {r} never exercised");
    }
    assert_eq!(
        stats.discrepancies, 0,
        "fp.rs must match single-rounding IEEE in all modes/regimes; \
         discrepancies by mode/regime: {:?}; examples: {:?}",
        stats.by_mode_regime, stats.examples
    );
}

/// BUG A regression: `roundNearestTiesToAway` must round to NEAREST (ties away),
/// not MPFR's directed away-from-zero. This f32 fpsub lands just off a grid
/// point so the two readings differ by 1 ULP.
#[test]
fn regression_rna_ties_away() {
    let f = Fmt { eb: 8, sb: 24 };
    let abits = Integer::from(25_825_793u32);
    let bbits = Integer::from(3_198_331_760u32);
    let (fa, da) = make_operand(&abits, f);
    let (fb, db) = make_operand(&bbits, f);

    let got = bits_of(&run_op(Op::Sub, &fa, &fb, Round::AwayZero));
    let want = oracle_bits(Op::Sub, &da, &db, f, Round::AwayZero, Sem::SmtLib);
    let old_directed = oracle_bits(Op::Sub, &da, &db, f, Round::AwayZero, Sem::MpfrFaithful);

    eprintln!("RNA fpsub: got={got} want(ties-away)={want} old(directed)={old_directed}");
    assert_ne!(
        want, old_directed,
        "sanity: this case must distinguish ties-away from directed-away"
    );
    assert_eq!(got, want, "RNA must be nearest-ties-away, not directed away-from-zero");
}

/// BUG B regression: a nearest-mode (RNE) result in the subnormal range must be
/// single-rounded. This f32 fpmul's exact product sits a quarter-ulp from a
/// subnormal-grid point; the old two-step (round to 24 bits, then to the
/// subnormal grid) double-rounded it 1 ULP too high.
#[test]
fn regression_subnormal_rne_single_round() {
    let f = Fmt { eb: 8, sb: 24 };
    let abits = Integer::from(2_148_304_878u32);
    let bbits = Integer::from(3_231_114_841u32);
    let (fa, da) = make_operand(&abits, f);
    let (fb, db) = make_operand(&bbits, f);

    let got = bits_of(&run_op(Op::Mul, &fa, &fb, Round::Nearest));
    let want = oracle_bits(Op::Mul, &da, &db, f, Round::Nearest, Sem::SmtLib);

    eprintln!("RNE subnormal fpmul: got={got} want(single-round)={want}");
    assert_eq!(got, want, "subnormal RNE must be single-rounded (no double rounding)");
}
