//! Command-level parsing: assertions, declarations, types, and variable
//! collection. Port of the non-reader parts of `parsing/parse.rkt`.

use crate::data::value::Assignment;
use crate::parsing::transform::{
    formula_to_nnf, remove_const_bv2fp, remove_fpconst, remove_let_bindings, simplify, transform_expr,
    unnest,
};
use crate::sexp::Sexp;
use std::collections::BTreeSet;

/// The full `main.rkt` preprocessing pipeline, producing the scored formula.
///
/// `remove_const_bv2fp` is included (the Racket `main` omitted it) so that the
/// common `((_ to_fp e s) (_ bv… w))` bit-pattern constants are folded.
pub fn prepare_formula(cmds: &[Sexp]) -> Sexp {
    let f = get_formula(cmds);
    let f = remove_let_bindings(&f);
    let f = formula_to_nnf(&f);
    let f = unnest(&f);
    let f = simplify(&f);
    let f = remove_const_bv2fp(&f);
    remove_fpconst(&f)
}

/// A declared type (kept as an s-expression, e.g. `(_ FloatingPoint 8 24)`).
pub type Type = Sexp;

/// `(get-formula cmds)` — conjoin every `(assert e)` (transformed) under `∧`.
pub fn get_formula(cmds: &[Sexp]) -> Sexp {
    let mut result = Sexp::sym("⊤");
    for cmd in cmds {
        if let Sexp::List(items) = cmd {
            if items.len() == 2 && items[0].is_sym("assert") {
                result = Sexp::List(vec![
                    Sexp::sym("∧"),
                    transform_expr(&items[1]),
                    result,
                ]);
            }
        }
    }
    result
}

/// `(get-var-info cmds)` — name → declared type from `declare-const`/`declare-fun`.
pub fn get_var_info(cmds: &[Sexp]) -> std::collections::HashMap<String, Type> {
    let mut info = std::collections::HashMap::new();
    for cmd in cmds {
        if let Sexp::List(items) = cmd {
            match items[0].as_sym() {
                // (declare-const id type)
                Some("declare-const") if items.len() == 3 => {
                    if let Some(id) = items[1].as_sym() {
                        info.insert(id.to_string(), items[2].clone());
                    }
                }
                // (declare-fun id () type)
                Some("declare-fun") if items.len() == 4 => {
                    if let (Some(id), Some(args)) = (items[1].as_sym(), items[2].as_list()) {
                        if args.is_empty() {
                            info.insert(id.to_string(), items[3].clone());
                        }
                    }
                }
                _ => {}
            }
        }
    }
    info
}

// ---------- type predicates ----------

pub fn bv_type(t: &Type) -> bool {
    matches!(t, Sexp::List(v) if v.len() == 3 && v[0].is_sym("_") && v[1].is_sym("BitVec"))
}

pub fn bv_type_width(t: &Type) -> u32 {
    match t {
        Sexp::List(v) if v.len() == 3 && v[0].is_sym("_") && v[1].is_sym("BitVec") => {
            v[2].as_u32().expect("bv width")
        }
        _ => panic!("not a valid bv type!"),
    }
}

pub fn bool_type(t: &Type) -> bool {
    t.is_sym("Bool")
}

pub fn fp_type(t: &Type) -> bool {
    match t {
        Sexp::List(v) => v.len() == 4 && v[0].is_sym("_") && v[1].is_sym("FloatingPoint"),
        Sexp::Sym(s) => matches!(s.as_str(), "Float16" | "Float32" | "Float64" | "Float128"),
        _ => false,
    }
}

/// `(get/fp-type-widths t)` → `(exp_width, sig_width)`.
pub fn fp_type_widths(t: &Type) -> (u32, u32) {
    match t {
        Sexp::List(v) if v.len() == 4 && v[0].is_sym("_") && v[1].is_sym("FloatingPoint") => {
            (v[2].as_u32().unwrap(), v[3].as_u32().unwrap())
        }
        Sexp::Sym(s) => match s.as_str() {
            "Float16" => (5, 11),
            "Float32" => (8, 24),
            "Float64" => (11, 53),
            "Float128" => (15, 113),
            _ => panic!("not a valid fp type!"),
        },
        _ => panic!("not a valid fp type!"),
    }
}

/// `(get/assertions F)` — the top-level conjuncts (or `[F]` if not a `∧`).
pub fn get_assertions(f: &Sexp) -> Vec<Sexp> {
    match f {
        Sexp::List(v) if v[0].is_sym("∧") => v[1..].to_vec(),
        _ => vec![f.clone()],
    }
}

/// `(get/vars F assignment)` — assignment variables occurring in `F`, sorted.
pub fn get_vars(f: &Sexp, asn: &Assignment) -> Vec<String> {
    fn go(f: &Sexp, asn: &Assignment, out: &mut BTreeSet<String>) {
        match f {
            Sexp::List(items) => {
                for e in items {
                    go(e, asn, out);
                }
            }
            Sexp::BV(_) | Sexp::FP(_) | Sexp::Int(_) => {}
            Sexp::Sym(s) => {
                if asn.contains_key(s) {
                    out.insert(s.clone());
                }
            }
        }
    }
    let mut set = BTreeSet::new();
    go(f, asn, &mut set);
    set.into_iter().collect()
}

/// `(get-reachable-vars F assignment)` — variables reachable in operand
/// position (descends into arguments and `let` bindings; may repeat).
pub fn get_reachable_vars(f: &Sexp, asn: &Assignment) -> Vec<String> {
    fn go(f: &Sexp, asn: &Assignment, out: &mut Vec<String>) {
        match f {
            Sexp::List(items) if items[0].is_sym("let") => {
                // (let ([id binding]...) expr)
                if let Some(bindings) = items[1].as_list() {
                    for b in bindings {
                        if let Some(pair) = b.as_list() {
                            if pair.len() == 2 {
                                go(&pair[1], asn, out);
                            }
                        }
                    }
                }
                go(&items[2], asn, out);
            }
            Sexp::List(items) => {
                for arg in &items[1..] {
                    go(arg, asn, out);
                }
            }
            Sexp::BV(_) | Sexp::FP(_) | Sexp::Int(_) => {}
            Sexp::Sym(s) => {
                if asn.contains_key(s) {
                    out.push(s.clone());
                }
            }
        }
    }
    let mut out = Vec::new();
    go(f, asn, &mut out);
    out
}
