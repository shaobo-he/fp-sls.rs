//! OL1V3R, ported to Rust: stochastic local search for QF_BV / QF_FP SMT.
//!
//! Reimplements Fröhlich, Biere, Wintersteiger & Hamadi, "Stochastic Local
//! Search for Satisfiability Modulo Theories" (AAAI 2015). Module layout mirrors
//! the original Racket repository for traceability.

pub mod rng;
pub mod sexp;

pub mod data {
    pub mod bitvec;
    pub mod eval;
    pub mod fp;
    pub mod value;
}

pub mod parsing {
    pub mod parse;
    pub mod reader;
    pub mod transform;
}

pub mod score;
pub mod sls;
pub mod z3;
