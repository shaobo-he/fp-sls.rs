//! Formula transformations. Port of `parsing/transform.rkt`.
//!
//! Pipeline (as in `main.rkt`): `transform_expr` (done per-assert in
//! `get_formula`) → `remove_let_bindings` → `formula_to_nnf` → `unnest` →
//! `simplify` → `remove_const_bv2fp` → `remove_fpconst`.
//!
//! `remove_const_bv2fp` is wired into the pipeline here (the Racket `main`
//! omitted it); it folds the ubiquitous `((_ to_fp e s) (_ bv… w))`
//! bit-pattern-to-float constants, matching TODO #3 ("conversions to core
//! language"). The unused `remove-equalities` helper is intentionally omitted.

use crate::data::bitvec::BitVec;
use crate::data::fp::FloatingPoint;
use crate::sexp::Sexp;
use rug::Integer;

/// `(extract-bv-value bv)` — the numeral in a `bvNNN` symbol.
fn extract_bv_value(sym: &str) -> Integer {
    Integer::from_str_radix(&sym[2..], 10).expect("bv constant numeral")
}

fn sym_list(op: &str, args: impl Iterator<Item = Sexp>) -> Sexp {
    let mut v = vec![Sexp::sym(op)];
    v.extend(args);
    Sexp::List(v)
}

// ---------- transform_expr: surface SMT → core boolean connectives ----------

pub fn transform_expr(s: &Sexp) -> Sexp {
    match s {
        Sexp::List(items) if !items.is_empty() => match items[0].as_sym() {
            Some("not") => sym_list("¬", items[1..].iter().map(transform_expr)),
            Some("and") => sym_list("∧", items[1..].iter().map(transform_expr)),
            Some("or") => sym_list("∨", items[1..].iter().map(transform_expr)),
            Some("implies") | Some("=>") => {
                // (=> e1 e2) ≡ (or (not e1) e2)
                let rewritten = Sexp::List(vec![
                    Sexp::sym("or"),
                    Sexp::List(vec![Sexp::sym("not"), items[1].clone()]),
                    items[2].clone(),
                ]);
                transform_expr(&rewritten)
            }
            _ => Sexp::List(items.iter().map(transform_expr).collect()),
        },
        Sexp::Sym(s) if s == "true" => Sexp::sym("⊤"),
        Sexp::Sym(s) if s == "false" => Sexp::sym("⊥"),
        _ => s.clone(),
    }
}

// ---------- negation normal form ----------

pub fn formula_to_nnf(f: &Sexp) -> Sexp {
    if let Sexp::List(items) = f {
        if items[0].is_sym("¬") {
            let inner = &items[1];
            if inner.is_sym("⊥") {
                return Sexp::sym("⊤");
            }
            if inner.is_sym("⊤") {
                return Sexp::sym("⊥");
            }
            if let Sexp::List(g) = inner {
                match g[0].as_sym() {
                    Some("¬") => return formula_to_nnf(&g[1]),
                    Some("∧") => {
                        return sym_list(
                            "∨",
                            g[1..]
                                .iter()
                                .map(|fi| formula_to_nnf(&Sexp::List(vec![Sexp::sym("¬"), fi.clone()]))),
                        );
                    }
                    Some("∨") => {
                        return sym_list(
                            "∧",
                            g[1..]
                                .iter()
                                .map(|fi| formula_to_nnf(&Sexp::List(vec![Sexp::sym("¬"), fi.clone()]))),
                        );
                    }
                    _ => {}
                }
            }
        }
        // general: (op fs...) → (op nnf(fs)...)
        let mut v = vec![items[0].clone()];
        v.extend(items[1..].iter().map(formula_to_nnf));
        return Sexp::List(v);
    }
    f.clone()
}

// ---------- flatten nested ∧ / ∨ ----------

pub fn unnest(f: &Sexp) -> Sexp {
    match f {
        Sexp::List(items) if !items.is_empty() => {
            let op = items[0].as_sym();
            if op == Some("∨") || op == Some("∧") {
                let opname = op.unwrap();
                let mut flat = Vec::new();
                let mut changed = false;
                for child in &items[1..] {
                    if child.head_sym() == Some(opname) {
                        if let Sexp::List(c) = child {
                            flat.extend(c[1..].iter().cloned());
                            changed = true;
                            continue;
                        }
                    }
                    flat.push(child.clone());
                }
                if changed {
                    // Re-unnest in case the splice exposed further nesting.
                    let mut v = vec![Sexp::sym(opname)];
                    v.extend(flat);
                    unnest(&Sexp::List(v))
                } else {
                    sym_list(opname, flat.iter().map(unnest))
                }
            } else {
                // (op fs...) → (op map unnest fs)
                let mut v = vec![items[0].clone()];
                v.extend(items[1..].iter().map(unnest));
                Sexp::List(v)
            }
        }
        _ => f.clone(),
    }
}

// ---------- boolean simplification with ⊤ / ⊥ ----------

fn simplify_andor(children: Vec<Sexp>, head: &str, cond_sym: &str, term_sym: &str) -> Sexp {
    // `children` are the already-simplified arguments (not including the head).
    let mut col = vec![Sexp::sym(head)];
    for e in children {
        if e.is_sym(cond_sym) {
            continue; // identity element: drop
        }
        if e.is_sym(term_sym) {
            return Sexp::sym(term_sym); // annihilator: collapse
        }
        col.push(e);
    }
    if col.len() == 2 {
        col.into_iter().nth(1).unwrap() // (∧ v) → v
    } else {
        Sexp::List(col)
    }
}

pub fn simplify(s: &Sexp) -> Sexp {
    if let Sexp::List(items) = s {
        if items[0].is_sym("¬") {
            if let Sexp::List(g) = &items[1] {
                if g[0].is_sym("¬") {
                    return simplify(&g[1]); // (¬ (¬ e)) → e
                }
            }
            if items[1].is_sym("⊤") {
                return Sexp::sym("⊥");
            }
            if items[1].is_sym("⊥") {
                return Sexp::sym("⊤");
            }
        }
        match items[0].as_sym() {
            Some("∧") => {
                let children: Vec<Sexp> = items[1..].iter().map(simplify).collect();
                return simplify_andor(children, "∧", "⊤", "⊥");
            }
            Some("∨") => {
                let children: Vec<Sexp> = items[1..].iter().map(simplify).collect();
                return simplify_andor(children, "∨", "⊥", "⊤");
            }
            _ => return Sexp::List(items.iter().map(simplify).collect()),
        }
    }
    s.clone()
}

// ---------- floating-point constant folding ----------

/// `(remove-const-bv2fp sexp)` — fold `((_ to_fp e s) (_ bv… w))`.
pub fn remove_const_bv2fp(s: &Sexp) -> Sexp {
    if let Sexp::List(items) = s {
        if items.len() == 2 {
            if let (Sexp::List(h), Sexp::List(g)) = (&items[0], &items[1]) {
                if h.len() == 4
                    && h[0].is_sym("_")
                    && h[1].is_sym("to_fp")
                    && g.len() == 3
                    && g[0].is_sym("_")
                    && g[1].as_sym().is_some_and(|s| s.starts_with("bv"))
                {
                    let exp = h[2].as_u32().expect("to_fp exp width");
                    let sig = h[3].as_u32().expect("to_fp sig width");
                    let width = g[2].as_u32().expect("bv width");
                    let val = extract_bv_value(g[1].as_sym().unwrap());
                    return Sexp::FP(FloatingPoint::from_bitvec(
                        &BitVec::new(width, val),
                        exp,
                        sig,
                    ));
                }
            }
        }
        return Sexp::List(items.iter().map(remove_const_bv2fp).collect());
    }
    s.clone()
}

/// `(remove-fpconst sexp)` — fold `(fp …)` and `(_ +zero …)` style constants.
pub fn remove_fpconst(s: &Sexp) -> Sexp {
    if let Sexp::List(items) = s {
        // (fp (_ sign 1) (_ exp ew) (_ sig sw_wo))
        if items.len() == 4 && items[0].is_sym("fp") {
            if let (Sexp::List(sgn), Sexp::List(exp), Sexp::List(sig)) =
                (&items[1], &items[2], &items[3])
            {
                if is_bvconst(sgn) && is_bvconst(exp) && is_bvconst(sig) {
                    let exp_width = exp[2].as_u32().unwrap();
                    let sig_wo = sig[2].as_u32().unwrap();
                    let sval = extract_bv_value(sgn[1].as_sym().unwrap());
                    let eval_ = extract_bv_value(exp[1].as_sym().unwrap());
                    let sigval = extract_bv_value(sig[1].as_sym().unwrap());
                    let value = (sval << (exp_width + sig_wo))
                        + (eval_ << sig_wo)
                        + sigval;
                    let total = sig_wo + 1 + exp_width;
                    return Sexp::FP(FloatingPoint::from_bitvec(
                        &BitVec::new(total, value),
                        exp_width,
                        sig_wo + 1,
                    ));
                }
            }
        }
        // (_ <tag> ew sw)
        if items.len() == 4 && items[0].is_sym("_") {
            if let (Some(tag), Some(ew), Some(sw)) =
                (items[1].as_sym(), items[2].as_u32(), items[3].as_u32())
            {
                let make = |v: f64| Some(Sexp::FP(FloatingPoint::real_from_f64(v, ew, sw)));
                let folded = match tag {
                    "+zero" => make(0.0),
                    "-zero" => make(-0.0),
                    "+oo" => make(f64::INFINITY),
                    "-oo" => make(f64::NEG_INFINITY),
                    "NaN" => make(f64::NAN),
                    _ => None,
                };
                if let Some(f) = folded {
                    return f;
                }
            }
        }
        return Sexp::List(items.iter().map(remove_fpconst).collect());
    }
    s.clone()
}

fn is_bvconst(items: &[Sexp]) -> bool {
    items.len() == 3
        && items[0].is_sym("_")
        && items[1].as_sym().is_some_and(|s| s.starts_with("bv"))
}

// ---------- let elimination ----------

fn boolean_expr(s: &Sexp) -> bool {
    match s.head_sym() {
        Some(op) => matches!(
            op,
            "¬" | "∧"
                | "∨"
                | "="
                | "bvlt"
                | "bvleq"
                | "bvgt"
                | "bvgeq"
                | "fp.eq"
                | "fp.lt"
                | "fp.leq"
                | "fp.gt"
                | "fp.geq"
        ),
        None => false,
    }
}

/// `(remove-let-bindings sexp)` — inline boolean `let` bindings into the
/// environment, keep non-boolean ones as `let`s.
pub fn remove_let_bindings(s: &Sexp) -> Sexp {
    fn lookup(sym: &str, env: &[(String, Sexp)]) -> Sexp {
        for (k, v) in env.iter().rev() {
            if k == sym {
                return v.clone();
            }
        }
        Sexp::sym(sym)
    }

    fn go(s: &Sexp, env: &[(String, Sexp)]) -> Sexp {
        if let Sexp::List(items) = s {
            if items[0].is_sym("let") {
                let bindings = items[1].as_list().expect("let bindings");
                let mut env: Vec<(String, Sexp)> = env.to_vec();
                let mut kept: Vec<Sexp> = Vec::new();
                for b in bindings {
                    let pair = b.as_list().expect("binding pair");
                    let id = pair[0].as_sym().expect("binding name").to_string();
                    let binded = go(&pair[1], &env);
                    if boolean_expr(&binded) {
                        env.push((id, binded));
                    } else {
                        // Faithful to Racket: keep the *original* binding form.
                        kept.push(b.clone());
                    }
                }
                let body = go(&items[2], &env);
                if kept.is_empty() {
                    body
                } else {
                    Sexp::List(vec![Sexp::sym("let"), Sexp::List(kept), body])
                }
            } else {
                let mut v = vec![items[0].clone()];
                v.extend(items[1..].iter().map(|e| go(e, env)));
                Sexp::List(v)
            }
        } else if let Sexp::Sym(name) = s {
            lookup(name, env)
        } else {
            s.clone()
        }
    }

    go(s, &[])
}

// ---------- QF_FP → Real (for the Z3 real-model heuristic) ----------

/// `(fp->real sexp)` — a best-effort encoding of a QF_FP formula over the reals.
pub fn fp_to_real(s: &Sexp) -> Sexp {
    match s {
        Sexp::FP(fp) => Sexp::sym(format!("{}", fp.to_f64())),
        Sexp::List(items) if !items.is_empty() => {
            // types / special constants
            if items[0].is_sym("_") {
                match items.get(1).and_then(Sexp::as_sym) {
                    Some("FloatingPoint") => return Sexp::sym("Real"),
                    Some("+zero") | Some("-zero") => return Sexp::int(0u32),
                    _ => {}
                }
            }
            match items[0].as_sym() {
                Some("fp.eq") => sym_list("=", items[1..].iter().map(fp_to_real)),
                Some("fp.lt") => sym_list("<", items[1..].iter().map(fp_to_real)),
                Some("fp.gt") => sym_list(">", items[1..].iter().map(fp_to_real)),
                Some("fp.leq") => sym_list("<=", items[1..].iter().map(fp_to_real)),
                Some("fp.geq") => sym_list(">=", items[1..].iter().map(fp_to_real)),
                Some("fp.neg") => {
                    Sexp::List(vec![Sexp::sym("-"), Sexp::int(0u32), fp_to_real(&items[1])])
                }
                Some("fp.add") => sym_list("+", items[2..].iter().map(fp_to_real)),
                Some("fp.sub") => sym_list("-", items[2..].iter().map(fp_to_real)),
                Some("fp.mul") => sym_list("*", items[2..].iter().map(fp_to_real)),
                Some("fp.div") => sym_list("/", items[2..].iter().map(fp_to_real)),
                _ => {
                    // ((_ to_fp e s) rm x) → x
                    if let Sexp::List(h) = &items[0] {
                        if h.len() == 4 && h[0].is_sym("_") && h[1].is_sym("to_fp") && items.len() == 3
                        {
                            return fp_to_real(&items[2]);
                        }
                    }
                    Sexp::List(items.iter().map(fp_to_real).collect())
                }
            }
        }
        _ => s.clone(),
    }
}
