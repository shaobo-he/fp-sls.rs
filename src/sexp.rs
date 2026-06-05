//! The dynamic s-expression type used throughout the solver.
//!
//! Racket represents formulas, terms, and types as raw s-expressions, with
//! bit-vector and floating-point *constants* spliced in as struct instances
//! during preprocessing. We mirror that with an enum that additionally carries
//! embedded [`BitVec`] / [`FloatingPoint`] constants.

use crate::data::bitvec::BitVec;
use crate::data::fp::FloatingPoint;
use rug::Integer;
use std::fmt;

#[derive(Clone, Debug, PartialEq)]
pub enum Sexp {
    /// A symbol / identifier / operator (e.g. `fp.add`, `x`, `∧`, `⊤`).
    Sym(String),
    /// A numeric literal (bit-widths, numerals, …).
    Int(Integer),
    /// A list `( … )`.
    List(Vec<Sexp>),
    /// An embedded bit-vector constant.
    BV(BitVec),
    /// An embedded floating-point constant.
    FP(FloatingPoint),
}

impl Sexp {
    pub fn sym<S: Into<String>>(s: S) -> Sexp {
        Sexp::Sym(s.into())
    }
    pub fn int<T: Into<Integer>>(n: T) -> Sexp {
        Sexp::Int(n.into())
    }

    pub fn as_sym(&self) -> Option<&str> {
        match self {
            Sexp::Sym(s) => Some(s.as_str()),
            _ => None,
        }
    }
    pub fn as_list(&self) -> Option<&[Sexp]> {
        match self {
            Sexp::List(v) => Some(v.as_slice()),
            _ => None,
        }
    }
    /// True iff this is exactly the symbol `s`.
    pub fn is_sym(&self, s: &str) -> bool {
        matches!(self, Sexp::Sym(x) if x == s)
    }
    /// The operator (head symbol) of a non-empty list, if any.
    pub fn head_sym(&self) -> Option<&str> {
        match self {
            Sexp::List(v) => v.first().and_then(Sexp::as_sym),
            _ => None,
        }
    }
    /// Interpret an `Int` (e.g. a bit-width) as a `u32`.
    pub fn as_u32(&self) -> Option<u32> {
        match self {
            Sexp::Int(i) => i.to_u32(),
            _ => None,
        }
    }
}

impl fmt::Display for Sexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sexp::Sym(s) => write!(f, "{s}"),
            Sexp::Int(i) => write!(f, "{i}"),
            Sexp::List(v) => {
                write!(f, "(")?;
                for (i, e) in v.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, ")")
            }
            Sexp::BV(bv) => write!(f, "{}", bv.to_bv_const()),
            Sexp::FP(fp) => write!(f, "{}", fp.to_fp_const()),
        }
    }
}
