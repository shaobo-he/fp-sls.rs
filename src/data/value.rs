//! Runtime values produced by the evaluator: a bit-vector or a floating-point.
//! Booleans are width-1 bit-vectors, exactly as in the Racket original.

use crate::data::bitvec::BitVec;
use crate::data::fp::FloatingPoint;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    BV(BitVec),
    FP(FloatingPoint),
}

/// A model: variable name → value.
pub type Assignment = HashMap<String, Value>;

impl Value {
    pub fn as_bv(&self) -> &BitVec {
        match self {
            Value::BV(b) => b,
            Value::FP(_) => panic!("expected a bit-vector value"),
        }
    }
    pub fn as_fp(&self) -> &FloatingPoint {
        match self {
            Value::FP(f) => f,
            Value::BV(_) => panic!("expected a floating-point value"),
        }
    }
}
