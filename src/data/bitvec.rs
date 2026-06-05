//! Bit-vectors. Port of `data/bit-vec.rkt`.
//!
//! A [`BitVec`] stores its `width` and an unsigned `value` in `[0, 2^width)`
//! (the natural number whose two's-complement bit pattern is the bit-vector).
//! This mirrors the Racket `struct BitVec (width value)` where `value` is "a
//! positive integer whose two's complement is the bv to represent".

use crate::rng::Rng;
use crate::sexp::Sexp;
use rug::Integer;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BitVec {
    pub width: u32,
    pub value: Integer,
}

/// `2^w` as a big integer.
#[inline]
pub fn two_pow(w: u32) -> Integer {
    Integer::from(1) << w
}

/// Non-negative remainder `x mod m` (Euclidean; `m > 0`). Mirrors Racket `modulo`.
#[inline]
fn umod(x: Integer, m: &Integer) -> Integer {
    let r = x % m;
    if r < 0 {
        r + m
    } else {
        r
    }
}

impl BitVec {
    /// `(mkBV width value)` — stores `value` verbatim (callers keep it in range).
    pub fn new(width: u32, value: Integer) -> BitVec {
        BitVec { width, value }
    }

    /// Construct, reducing `value` into `[0, 2^width)`.
    pub fn new_mod(width: u32, value: Integer) -> BitVec {
        BitVec {
            width,
            value: umod(value, &two_pow(width)),
        }
    }

    /// `(initialize/bv width)` — the all-zero bit-vector.
    pub fn initialize(width: u32) -> BitVec {
        BitVec::new(width, Integer::new())
    }

    /// `(mkBoolBV b)` — a width-1 bit-vector encoding a boolean.
    pub fn from_bool(b: bool) -> BitVec {
        BitVec::new(1, Integer::from(if b { 1 } else { 0 }))
    }

    /// `(eval/id v)` — the underlying value (booleans are width-1 bit-vectors).
    pub fn eval_id(&self) -> &Integer {
        &self.value
    }

    /// `(BitVec->BVConst bv)` — the SMT-LIB constant `(_ bvVALUE WIDTH)`.
    pub fn to_bv_const(&self) -> Sexp {
        Sexp::List(vec![
            Sexp::sym("_"),
            Sexp::sym(format!("bv{}", self.value)),
            Sexp::Int(Integer::from(self.width)),
        ])
    }

    /// Number of differing bits — `(Hamming-distance bv1 bv2)`.
    pub fn hamming_distance(&self, other: &BitVec) -> u32 {
        // Both values are < 2^width, so the xor is too and `count_ones` over the
        // whole integer equals the number of differing bits within `width`.
        let x = Integer::from(&self.value ^ &other.value);
        x.count_ones().unwrap_or(0)
    }

    // ----- arithmetic (mod 2^width) -----

    fn arith<F: Fn(&Integer, &Integer) -> Integer>(&self, other: &BitVec, op: F) -> BitVec {
        let r = op(&self.value, &other.value);
        BitVec::new(self.width, umod(r, &two_pow(self.width)))
    }

    pub fn bvadd(&self, o: &BitVec) -> BitVec {
        self.arith(o, |a, b| Integer::from(a + b))
    }
    pub fn bvsub(&self, o: &BitVec) -> BitVec {
        self.arith(o, |a, b| Integer::from(a - b))
    }
    pub fn bvmul(&self, o: &BitVec) -> BitVec {
        self.arith(o, |a, b| Integer::from(a * b))
    }

    /// Unsigned division. Per SMT-LIB, division by zero yields all-ones.
    /// (Racket's `eval/bvudiv` used exact `/` and was unsound for non-divisible
    /// operands; this implements the correct semantics.)
    pub fn bvudiv(&self, o: &BitVec) -> BitVec {
        if o.value == 0 {
            BitVec::new(self.width, &two_pow(self.width) - Integer::from(1))
        } else {
            BitVec::new(self.width, Integer::from(&self.value / &o.value))
        }
    }

    /// Unsigned remainder. Per SMT-LIB, `x urem 0 = x`.
    /// (Racket left this unimplemented; this is the correct semantics.)
    pub fn bvurem(&self, o: &BitVec) -> BitVec {
        if o.value == 0 {
            self.clone()
        } else {
            BitVec::new(self.width, Integer::from(&self.value % &o.value))
        }
    }

    /// `(eval/bvneg bv)` — two's-complement negation.
    pub fn bvneg(&self) -> BitVec {
        BitVec::new(
            self.width,
            umod(Integer::from(-&self.value), &two_pow(self.width)),
        )
    }

    // ----- bitwise -----

    pub fn bvand(&self, o: &BitVec) -> BitVec {
        BitVec::new(self.width, Integer::from(&self.value & &o.value))
    }
    pub fn bvor(&self, o: &BitVec) -> BitVec {
        BitVec::new(self.width, Integer::from(&self.value | &o.value))
    }

    /// Logical left shift (mod 2^width).
    pub fn bvshl(&self, o: &BitVec) -> BitVec {
        match o.value.to_u32() {
            Some(s) if s < self.width => BitVec::new(
                self.width,
                umod(Integer::from(&self.value << s), &two_pow(self.width)),
            ),
            _ => BitVec::new(self.width, Integer::new()),
        }
    }

    /// Logical right shift.
    pub fn bvlshr(&self, o: &BitVec) -> BitVec {
        match o.value.to_u32() {
            Some(s) if s < self.width => BitVec::new(self.width, Integer::from(&self.value >> s)),
            _ => BitVec::new(self.width, Integer::new()),
        }
    }

    /// `(eval/bvnot bv)` — bitwise complement.
    pub fn bvnot(&self) -> BitVec {
        BitVec::new(
            self.width,
            (&two_pow(self.width) - Integer::from(1)) - &self.value,
        )
    }

    // ----- comparisons (same width required) -----

    fn same_width(&self, o: &BitVec) {
        assert_eq!(self.width, o.width, "not the same bit-width");
    }
    pub fn bv_eq(&self, o: &BitVec) -> bool {
        self.same_width(o);
        self.value == o.value
    }
    pub fn bv_lt(&self, o: &BitVec) -> bool {
        self.same_width(o);
        self.value < o.value
    }
    pub fn bv_gt(&self, o: &BitVec) -> bool {
        self.same_width(o);
        self.value > o.value
    }
    pub fn bv_le(&self, o: &BitVec) -> bool {
        self.same_width(o);
        self.value <= o.value
    }
    pub fn bv_ge(&self, o: &BitVec) -> bool {
        self.same_width(o);
        self.value >= o.value
    }

    // ----- neighborhood relation -----

    /// `(get/1-exchange-range bv l h)` — flip each bit in `[l, h)`.
    pub fn one_exchange_range(&self, l: u32, h: u32) -> Vec<BitVec> {
        (l..h)
            .map(|i| {
                let mask = Integer::from(1) << i;
                BitVec::new(self.width, Integer::from(&self.value ^ &mask))
            })
            .collect()
    }

    /// `(get/1-exchange bv)` — flip each of the `width` bits in turn.
    pub fn one_exchange(&self) -> Vec<BitVec> {
        self.one_exchange_range(0, self.width)
    }

    /// `(get/±1 bv)` — increment and decrement by one.
    pub fn plus_minus_one(&self) -> Vec<BitVec> {
        let one = BitVec::new(self.width, Integer::from(1));
        vec![self.bvadd(&one), self.bvsub(&one)]
    }

    /// `(get/bv-extended-neighbors bv)` — single-bit flips plus ±1.
    pub fn extended_neighbors(&self) -> Vec<BitVec> {
        let mut ns = self.one_exchange();
        ns.extend(self.plus_minus_one());
        ns
    }

    /// `(random/bv w)` — uniform bit-vector of the given width.
    pub fn random(width: u32, rng: &mut Rng) -> BitVec {
        BitVec::new(width, rng.uniform_bits(width))
    }
}
