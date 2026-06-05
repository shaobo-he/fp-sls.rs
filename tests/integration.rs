//! End-to-end tests: parse real QF_FP benchmarks, solve them, and *validate*
//! the models the solver returns (TODO #6 "add tests").

use fp_sls::data::eval::eval;
use fp_sls::data::value::Assignment;
use fp_sls::parsing::parse::{get_var_info, prepare_formula};
use fp_sls::parsing::reader::read_file;
use fp_sls::parsing::transform::{remove_const_bv2fp, remove_fpconst};
use fp_sls::rng::Rng;
use fp_sls::score::score;
use fp_sls::sexp::Sexp;
use fp_sls::sls::{sls, sls_heuristics, sls_vns, Params, SolveResult};
use rug::Rational;

fn fixture(rel: &str) -> String {
    format!("{}/tests/smt/{}", env!("CARGO_MANIFEST_DIR"), rel)
}

fn params(step: usize) -> Params {
    Params {
        c2: Rational::from((1, 2)),
        max_steps: step,
        wp: 0.001,
        debug: false,
    }
}

/// Rebuild an [`Assignment`] from the `(assert (= const var))` model forms.
fn assignment_from_models(models: &[Sexp]) -> Assignment {
    let mut asn = Assignment::new();
    for m in models {
        let eq = &m.as_list().unwrap()[1]; // (= const var)
        let items = eq.as_list().unwrap();
        let const_term = remove_fpconst(&remove_const_bv2fp(&items[1]));
        let var = items[2].as_sym().unwrap().to_string();
        let val = eval(&const_term, &Assignment::new(), &[]);
        asn.insert(var, val);
    }
    asn
}

/// A satisfying model must make the whole formula score exactly 1.
fn assert_model_valid(path: &str, models: &[Sexp]) {
    let cmds = read_file(path).unwrap();
    let formula = prepare_formula(&cmds);
    let asn = assignment_from_models(models);
    let c2 = Rational::from((1, 2));
    let s = score(&c2, &asn, &[], &formula);
    assert_eq!(s, Rational::from(1), "recovered model does not satisfy {path}");
}

fn solve(path: &str, step: usize, seed: u64) -> SolveResult {
    let cmds = read_file(path).unwrap();
    let formula = prepare_formula(&cmds);
    let var_info = get_var_info(&cmds);
    let mut rng = Rng::from_seed(seed);
    let initial = fp_sls::sls::initialize_assignment(&var_info);
    sls(&var_info, &formula, &params(step), initial, &mut rng)
}

const SAT_FIXTURES: &[&str] = &[
    "schanda/spark/incorrect_reordering.smt2",
    "schanda/spark/guarded_div_1.smt2",
    "schanda/spark/exp_3_precision.smt2",
    "griggio/fmcad12/f23.smt2",
];

#[test]
fn parses_all_fixtures() {
    for rel in SAT_FIXTURES {
        let cmds = read_file(&fixture(rel)).unwrap();
        let _ = prepare_formula(&cmds);
        let info = get_var_info(&cmds);
        assert!(!info.is_empty(), "{rel} has no declared variables");
    }
}

#[test]
fn solves_and_validates_known_sat() {
    for rel in SAT_FIXTURES {
        let path = fixture(rel);
        match solve(&path, 20_000, 1) {
            SolveResult::Sat(models) => assert_model_valid(&path, &models),
            SolveResult::Unknown => panic!("expected sat for {rel} within budget"),
        }
    }
}

#[test]
fn deterministic_under_fixed_seed() {
    let path = fixture("griggio/fmcad12/f23.smt2");
    let a = solve(&path, 5_000, 42);
    let b = solve(&path, 5_000, 42);
    match (a, b) {
        (SolveResult::Sat(x), SolveResult::Sat(y)) => {
            let fmt = |v: &[Sexp]| v.iter().map(|s| s.to_string()).collect::<Vec<_>>();
            assert_eq!(fmt(&x), fmt(&y), "same seed produced different models");
        }
        (SolveResult::Unknown, SolveResult::Unknown) => {}
        _ => panic!("same seed produced different sat/unknown outcomes"),
    }
}

#[test]
fn vns_and_heuristics_also_solve() {
    let path = fixture("schanda/spark/incorrect_reordering.smt2");
    let cmds = read_file(&path).unwrap();
    let formula = prepare_formula(&cmds);
    let var_info = get_var_info(&cmds);

    let mut rng = Rng::from_seed(1);
    let init = fp_sls::sls::initialize_assignment(&var_info);
    let r = sls_vns(&var_info, &formula, &params(20_000), init, &mut rng);
    assert!(r.is_sat(), "vns failed to solve incorrect_reordering");
    if let SolveResult::Sat(m) = r {
        assert_model_valid(&path, &m);
    }

    let mut rng = Rng::from_seed(1);
    let init = fp_sls::sls::initialize_assignment(&var_info);
    let r = sls_heuristics(&var_info, &formula, &params(20_000), init, &mut rng);
    assert!(r.is_sat(), "heuristics failed to solve incorrect_reordering");
    if let SolveResult::Sat(m) = r {
        assert_model_valid(&path, &m);
    }
}
