//! The stochastic local search engine. Port of `sls.rkt`.
//!
//! Two strategies are provided, matching the Racket original:
//!   * [`sls`] — the WalkSAT-style search with extended bit-vector / FP
//!     neighborhoods and a random-walk diversification probability `wp`;
//!   * [`sls_vns`] — variable-neighborhood search cycling through the three
//!     FP move kinds (sign flip / exponent / significand).
//!
//! Both are written as explicit loops (the Racket version recurses; Rust would
//! overflow the stack for large `max_steps`).

// Several `argmax`/weight loops index in parallel and must keep "first on ties"
// semantics, which reads more clearly as an indexed loop than an iterator chain.
#![allow(clippy::needless_range_loop)]

use crate::data::bitvec::BitVec;
use crate::data::eval::get_value;
use crate::data::fp::FloatingPoint;
use crate::data::value::{Assignment, Value};
use crate::parsing::parse::{
    bool_type, bv_type, bv_type_width, fp_type, fp_type_widths, get_assertions, get_reachable_vars,
    get_vars, Type,
};
use crate::rng::Rng;
use crate::score::score;
use crate::sexp::Sexp;
use rug::Rational;
use std::collections::{HashMap, HashSet};

pub type VarInfo = HashMap<String, Type>;

#[derive(Debug)]
pub enum SolveResult {
    /// Satisfiable, with the model rendered as `(assert (= const var))` forms.
    Sat(Vec<Sexp>),
    Unknown,
}

impl SolveResult {
    pub fn is_sat(&self) -> bool {
        matches!(self, SolveResult::Sat(_))
    }
}

/// Search parameters (`c2` = score scaling constant, `wp` = walk probability).
pub struct Params {
    pub c2: Rational,
    pub max_steps: usize,
    pub wp: f64,
    /// When set, log the per-step formula score to stderr (`--debug`).
    pub debug: bool,
}

// ---------- assignment construction ----------

/// `(initialize/Assignment var-info)` — every variable set to all-zeros.
pub fn initialize_assignment(var_info: &VarInfo) -> Assignment {
    let mut asn = Assignment::new();
    for (name, ty) in var_info {
        asn.insert(name.clone(), zero_value(ty));
    }
    asn
}

fn zero_value(ty: &Type) -> Value {
    if bv_type(ty) {
        Value::BV(BitVec::initialize(bv_type_width(ty)))
    } else if fp_type(ty) {
        let (e, s) = fp_type_widths(ty);
        Value::FP(FloatingPoint::initialize(e, s))
    } else if bool_type(ty) {
        Value::BV(BitVec::initialize(1))
    } else {
        panic!("unsupported variable type: {ty}");
    }
}

/// `(randomize/Assignment var-info)` — every variable set to a random value.
pub fn randomize_assignment(var_info: &VarInfo, rng: &mut Rng) -> Assignment {
    // Sort keys for deterministic iteration order under a fixed seed
    // (mirrors `ordered-hash-keys`).
    let mut names: Vec<&String> = var_info.keys().collect();
    names.sort();
    let mut asn = Assignment::new();
    for name in names {
        let ty = &var_info[name];
        let v = if bv_type(ty) {
            Value::BV(BitVec::random(bv_type_width(ty), rng))
        } else if fp_type(ty) {
            let (e, s) = fp_type_widths(ty);
            Value::FP(FloatingPoint::random(e, s, rng))
        } else if bool_type(ty) {
            Value::BV(BitVec::random(1, rng))
        } else {
            panic!("unsupported variable type: {ty}");
        };
        asn.insert(name.clone(), v);
    }
    asn
}

// ---------- model extraction ----------

fn value_to_const(v: &Value) -> Sexp {
    match v {
        Value::BV(b) => b.to_bv_const(),
        Value::FP(f) => f.to_fp_const(),
    }
}

/// `(get/models assignment asserts)` — `(assert (= const var))` for each
/// reachable variable.
pub fn get_models(asn: &Assignment, asserts: &[Sexp]) -> Vec<Sexp> {
    let mut reachable: HashSet<String> = HashSet::new();
    for a in asserts {
        reachable.extend(get_reachable_vars(a, asn));
    }
    let mut names: Vec<&String> = asn.keys().filter(|k| reachable.contains(*k)).collect();
    names.sort();
    names
        .into_iter()
        .map(|name| {
            Sexp::List(vec![
                Sexp::sym("assert"),
                Sexp::List(vec![
                    Sexp::sym("="),
                    value_to_const(&asn[name]),
                    Sexp::sym(name.clone()),
                ]),
            ])
        })
        .collect()
}

// ---------- shared helpers ----------

fn one() -> Rational {
    Rational::from(1)
}

fn formula_score(c2: &Rational, asn: &Assignment, f: &Sexp) -> Rational {
    score(c2, asn, &[], f)
}

fn average(scores: &[Rational]) -> Rational {
    let mut sum = Rational::from(0);
    for s in scores {
        sum += s;
    }
    sum / Rational::from(scores.len() as u32)
}

/// `(select/Assertion …)` — the highest-scoring *unsatisfied* assertion.
fn select_assertion<'a>(asserts: &'a [Sexp], scores: &[Rational]) -> &'a Sexp {
    let key = |s: &Rational| -> Rational {
        if *s < one() {
            s.clone()
        } else {
            Rational::from(-1)
        }
    };
    let mut best = 0;
    let mut best_key = key(&scores[0]);
    for i in 1..scores.len() {
        let k = key(&scores[i]);
        if k > best_key {
            best_key = k;
            best = i;
        }
    }
    &asserts[best]
}

/// Index and score of the highest-scoring neighbor (first on ties).
fn argmax_score(c2: &Rational, neighbors: &[Assignment], f: &Sexp) -> (usize, Rational) {
    let mut best = 0;
    let mut best_score = formula_score(c2, &neighbors[0], f);
    for i in 1..neighbors.len() {
        let s = formula_score(c2, &neighbors[i], f);
        if s > best_score {
            best_score = s;
            best = i;
        }
    }
    (best, best_score)
}

fn extend_assignment(asn: &Assignment, var: &str, val: Value) -> Assignment {
    let mut a = asn.clone();
    a.insert(var.to_string(), val);
    a
}

fn all_satisfied(scores: &[Rational]) -> bool {
    let one = one();
    scores.iter().all(|s| *s == one)
}

// ---------- WalkSAT-style SLS ----------

pub fn sls(
    var_info: &VarInfo,
    f: &Sexp,
    params: &Params,
    mut assignment: Assignment,
    rng: &mut Rng,
) -> SolveResult {
    let asserts = get_assertions(f);
    for step in 0..params.max_steps {
        let assert_scores: Vec<Rational> = asserts
            .iter()
            .map(|a| formula_score(&params.c2, &assignment, a))
            .collect();
        if all_satisfied(&assert_scores) {
            return SolveResult::Sat(get_models(&assignment, &asserts));
        }

        let curr_score = average(&assert_scores);
        if params.debug {
            eprintln!("[sls] step {step}: score {:.6}", curr_score.to_f64());
        }
        let cand = select_assertion(&asserts, &assert_scores);
        let cand_vars = get_vars(cand, &assignment);

        // Extended neighborhood of every candidate variable.
        let mut neighbors: Vec<Assignment> = Vec::new();
        for var in &cand_vars {
            let val = get_value(&assignment, var).clone();
            for nv in extended_neighbor_values(&val, rng) {
                neighbors.push(extend_assignment(&assignment, var, nv));
            }
        }

        if neighbors.is_empty() {
            assignment = randomize_assignment(var_info, rng);
            continue;
        }

        let accepted = if rng.coin_flip(params.wp) {
            // Random walk: take any neighbor regardless of score.
            let idx = rng.below(neighbors.len());
            Some(neighbors.swap_remove(idx))
        } else {
            let (best_idx, best_score) = argmax_score(&params.c2, &neighbors, f);
            if best_score > curr_score {
                Some(neighbors.swap_remove(best_idx))
            } else {
                None
            }
        };

        assignment = match accepted {
            Some(a) => a,
            None => randomize_assignment(var_info, rng),
        };
    }
    SolveResult::Unknown
}

// ---------- variable-neighborhood search ----------

pub fn sls_vns(
    var_info: &VarInfo,
    f: &Sexp,
    params: &Params,
    mut assignment: Assignment,
    rng: &mut Rng,
) -> SolveResult {
    let asserts = get_assertions(f);
    let nc = 3u32;
    let mut ni = 1u32;
    for step in 0..params.max_steps {
        let assert_scores: Vec<Rational> = asserts
            .iter()
            .map(|a| formula_score(&params.c2, &assignment, a))
            .collect();
        if all_satisfied(&assert_scores) {
            return SolveResult::Sat(get_models(&assignment, &asserts));
        }

        let curr_score = average(&assert_scores);
        if params.debug {
            eprintln!("[vns] step {step} (ni={ni}): score {:.6}", curr_score.to_f64());
        }
        let cand = select_assertion(&asserts, &assert_scores);
        let cand_vars = get_vars(cand, &assignment);

        let mut neighbors: Vec<Assignment> = Vec::new();
        for var in &cand_vars {
            let val = get_value(&assignment, var).clone();
            for nv in vns_neighbor_values(&val, ni, rng) {
                neighbors.push(extend_assignment(&assignment, var, nv));
            }
        }

        let improving = if neighbors.is_empty() {
            None
        } else {
            let (best_idx, best_score) = argmax_score(&params.c2, &neighbors, f);
            if best_score > curr_score {
                Some(neighbors.swap_remove(best_idx))
            } else {
                None
            }
        };

        match improving {
            Some(a) => {
                assignment = a;
                ni = 1;
            }
            None => {
                let new_ni = ni + 1;
                if new_ni > nc {
                    assignment = randomize_assignment(var_info, rng);
                    ni = 1;
                } else {
                    ni = new_ni; // same assignment, next neighborhood
                }
            }
        }
    }
    SolveResult::Unknown
}

// ---------- paper heuristics: UCB selection, PAWS weights, restarts ----------
//
// Addresses the non-urgent Racket TODO "SLS heuristics in the original paper"
// (Fröhlich et al., §4). Three techniques layered onto the WalkSAT search:
//   * UCB-style assertion selection (Agrawal 1995);
//   * additive PAWS assertion weighting (Thornton et al. 2004);
//   * an exponential (Luby-like) restart schedule.
// Paper default constants are used; the score-scaling constant `c1` comes from
// `params.c2` (OL1V3R's `--c2`).

/// Paper UCB exploration constant `c2`.
const UCB_C2: f64 = 20.0;
/// Paper restart base `c4`.
const RESTART_C4: u64 = 100;
/// Paper smoothing probability `sp`.
const SMOOTH_SP: f64 = 0.05;

/// Paper weight delta `c3 = 0.025 = 1/40`.
fn weight_delta() -> Rational {
    Rational::from((1, 40))
}

/// `maxSteps(i) = c4` (i odd) or `c4·2^{i/2}` (i even).
fn restart_round_steps(i: u64) -> u64 {
    if i % 2 == 1 {
        RESTART_C4
    } else {
        RESTART_C4.saturating_mul(1u64 << (i / 2))
    }
}

fn weighted_score(weights: &[Rational], assert_scores: &[Rational]) -> Rational {
    let mut sum = Rational::from(0);
    for (w, s) in weights.iter().zip(assert_scores) {
        sum += Rational::from(w * s);
    }
    sum
}

/// UCB assertion selection among the unsatisfied assertions.
fn select_assertion_ucb(assert_scores: &[Rational], selected: &[u64], moves: u64) -> usize {
    let ln_moves = (moves as f64).max(1.0).ln();
    let mut best = None;
    let mut best_pri = f64::NEG_INFINITY;
    for (i, s) in assert_scores.iter().enumerate() {
        if *s >= Rational::from(1) {
            continue; // only unsatisfied assertions
        }
        // An unexplored assertion is selected first.
        if selected[i] == 0 {
            return i;
        }
        let pri = s.to_f64() + UCB_C2 * (ln_moves / selected[i] as f64).sqrt();
        if pri > best_pri {
            best_pri = pri;
            best = Some(i);
        }
    }
    best.expect("at least one unsatisfied assertion")
}

fn argmax_weighted(
    c2: &Rational,
    weights: &[Rational],
    asserts: &[Sexp],
    neighbors: &[Assignment],
) -> (usize, Rational) {
    let score_of = |a: &Assignment| -> Rational {
        let scores: Vec<Rational> = asserts.iter().map(|x| formula_score(c2, a, x)).collect();
        weighted_score(weights, &scores)
    };
    let mut best = 0;
    let mut best_score = score_of(&neighbors[0]);
    for i in 1..neighbors.len() {
        let s = score_of(&neighbors[i]);
        if s > best_score {
            best_score = s;
            best = i;
        }
    }
    (best, best_score)
}

/// WalkSAT search augmented with the paper's heuristics. `initial` seeds the
/// first round; restarts re-randomize the assignment while retaining the
/// assertion weights and UCB statistics.
pub fn sls_heuristics(
    var_info: &VarInfo,
    f: &Sexp,
    params: &Params,
    initial: Assignment,
    rng: &mut Rng,
) -> SolveResult {
    let asserts = get_assertions(f);
    let n = asserts.len();
    let mut weights = vec![Rational::from(1); n];
    let mut selected = vec![0u64; n];
    let mut moves: u64 = 0;
    let budget = params.max_steps as u64;
    let mut round: u64 = 1;
    let mut first = Some(initial);

    while moves < budget {
        let round_steps = restart_round_steps(round).min(budget - moves);
        let mut assignment = first
            .take()
            .unwrap_or_else(|| randomize_assignment(var_info, rng));

        for _ in 0..round_steps {
            moves += 1;
            let assert_scores: Vec<Rational> = asserts
                .iter()
                .map(|a| formula_score(&params.c2, &assignment, a))
                .collect();
            if all_satisfied(&assert_scores) {
                return SolveResult::Sat(get_models(&assignment, &asserts));
            }

            let cand_idx = select_assertion_ucb(&assert_scores, &selected, moves);
            selected[cand_idx] += 1;
            let curr_w = weighted_score(&weights, &assert_scores);
            if params.debug {
                eprintln!("[heur] move {moves} round {round}: wscore {:.4}", curr_w.to_f64());
            }
            let cand_vars = get_vars(&asserts[cand_idx], &assignment);

            let mut neighbors: Vec<Assignment> = Vec::new();
            for var in &cand_vars {
                let val = get_value(&assignment, var).clone();
                for nv in extended_neighbor_values(&val, rng) {
                    neighbors.push(extend_assignment(&assignment, var, nv));
                }
            }

            let accepted = if neighbors.is_empty() {
                None
            } else if rng.coin_flip(params.wp) {
                let idx = rng.below(neighbors.len());
                Some(neighbors.swap_remove(idx))
            } else {
                let (bi, bw) = argmax_weighted(&params.c2, &weights, &asserts, &neighbors);
                if bw > curr_w {
                    Some(neighbors.swap_remove(bi))
                } else {
                    None
                }
            };

            match accepted {
                Some(a) => assignment = a,
                None => {
                    // PAWS weight update on randomization.
                    let one = Rational::from(1);
                    if rng.coin_flip(1.0 - SMOOTH_SP) {
                        for i in 0..n {
                            if assert_scores[i] < one {
                                weights[i] += weight_delta();
                            }
                        }
                    } else {
                        for i in 0..n {
                            if assert_scores[i] == one {
                                let w = &weights[i] - weight_delta();
                                weights[i] = if w < one { one.clone() } else { w };
                            }
                        }
                    }
                    assignment = randomize_assignment(var_info, rng);
                }
            }
        }
        round += 1;
    }
    SolveResult::Unknown
}

// ---------- neighborhood relations ----------

/// `(get/extended-neighbors v)`.
fn extended_neighbor_values(v: &Value, rng: &mut Rng) -> Vec<Value> {
    match v {
        Value::BV(b) => b.extended_neighbors().into_iter().map(Value::BV).collect(),
        Value::FP(f) => f
            .extended_neighbors(rng)
            .into_iter()
            .map(Value::FP)
            .collect(),
    }
}

/// `(get/fp-neighbors val ni)` — VNS moves (FP only, as in the Racket original).
fn vns_neighbor_values(v: &Value, ni: u32, rng: &mut Rng) -> Vec<Value> {
    match v {
        Value::FP(f) => f.neighbors(ni, rng).into_iter().map(Value::FP).collect(),
        Value::BV(_) => panic!("variable-neighborhood search supports floating-point variables only"),
    }
}
