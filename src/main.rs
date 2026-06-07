//! Command-line entry point. Port of `main.rkt`.

use fp_sls::data::fp::ROUNDING_MODES;
use fp_sls::data::value::Assignment;
use fp_sls::parsing::parse::{get_formula, get_var_info, rounding_mode_type};
use fp_sls::parsing::reader::{read_all, read_file};
use fp_sls::parsing::transform::substitute;
use fp_sls::rng::Rng;
use fp_sls::sexp::Sexp;
use fp_sls::sls::{
    initialize_assignment, randomize_assignment, sls, sls_heuristics, sls_vns, Params, SolveResult,
    VarInfo,
};
use fp_sls::z3;
use rug::ops::Pow;
use rug::{Integer, Rational};
use std::collections::HashMap;
use std::str::FromStr;

struct Options {
    seed: u64,
    c2: Rational,
    wp: f64,
    step: usize,
    start_with_zeros: bool,
    try_real_models: bool,
    vns: bool,
    heuristics: bool,
    simplify: bool,
    elim_eqs: bool,
    print_models: bool,
    f64_score: bool,
    debug: bool,
    stats: bool,
    file: Option<String>,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            seed: 1,
            c2: Rational::from((1, 2)),
            wp: 0.001,
            step: 200,
            start_with_zeros: true,
            try_real_models: false,
            vns: false,
            heuristics: false,
            simplify: true,
            elim_eqs: false,
            print_models: false,
            f64_score: false,
            debug: false,
            stats: false,
            file: None,
        }
    }
}

const USAGE: &str = "\
sls — stochastic local search for QF_BV/QF_FP SMT (OL1V3R, Rust port)

usage: fp-sls [options] <filename>

options:
  --seed <n>                 RNG seed (1..2^31-1)                  [default 1]
  --c2 <r>                   score scaling constant in [0,1]       [default 1/2]
  --wp <p>                   diversification probability in [0,1]  [default 0.001]
  --step <n>                 number of search steps                [default 200]
  --initialize-with-random   start from random values (else all 0s)
  --try-real-models          seed search from a Z3 real-relaxation model
  --vns                      use variable-neighborhood search
  --heuristics               use the paper's heuristics (UCB + PAWS weights + restarts)
  --no-simplify              skip the default z3 simplification (jfs-opt equivalent)
  --elim-eqs                 also preprocess with Z3's solve-eqs tactic
  --print-models             print the model when sat
  --debug                    log per-step score to stderr
  --stats                    print `steps <n>` to stderr on a sat result
  -h, --help                 show this help
";

fn parse_decimal_or_ratio(s: &str) -> Option<Rational> {
    if s.contains('/') {
        return Rational::from_str(s).ok();
    }
    if !s.contains('.') {
        return Integer::from_str_radix(s, 10).ok().map(Rational::from);
    }
    let (neg, body) = match s.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, s),
    };
    let (int_part, frac_part) = body.split_once('.').unwrap_or((body, ""));
    let int_digits = if int_part.is_empty() { "0" } else { int_part };
    let scale = Integer::from(10).pow(frac_part.len() as u32);
    let int_val = Integer::from_str_radix(int_digits, 10).ok()?;
    let frac_val = if frac_part.is_empty() {
        Integer::from(0)
    } else {
        Integer::from_str_radix(frac_part, 10).ok()?
    };
    let mut r = Rational::from((int_val * &scale + frac_val, scale));
    if neg {
        r = -r;
    }
    Some(r)
}

fn parse_args() -> Result<Options, String> {
    let mut opts = Options::default();
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        let mut next = |name: &str| {
            args.next()
                .ok_or_else(|| format!("missing value for {name}"))
        };
        match arg.as_str() {
            "-h" | "--help" => {
                print!("{USAGE}");
                std::process::exit(0);
            }
            "--seed" => {
                let v = next("--seed")?;
                let n = v.parse::<u64>().map_err(|_| "not a valid seed")?;
                if n == 0 || n > (1u64 << 31) - 1 {
                    return Err("not a valid seed".into());
                }
                opts.seed = n;
            }
            "--c2" => {
                let v = next("--c2")?;
                let r = parse_decimal_or_ratio(&v).ok_or("not a valid score scaling constant")?;
                if !(0..=1).contains(&r) {
                    return Err("not a valid score scaling constant".into());
                }
                opts.c2 = r;
            }
            "--wp" => {
                let v = next("--wp")?;
                let p = v.parse::<f64>().map_err(|_| "not a valid diversification probability")?;
                if !(0.0..=1.0).contains(&p) {
                    return Err("not a valid diversification probability".into());
                }
                opts.wp = p;
            }
            "--step" => {
                let v = next("--step")?;
                opts.step = v.parse::<usize>().map_err(|_| "not a valid search step")?;
            }
            "--initialize-with-random" => opts.start_with_zeros = false,
            "--try-real-models" => opts.try_real_models = true,
            "--vns" => opts.vns = true,
            "--heuristics" => opts.heuristics = true,
            "--no-simplify" => opts.simplify = false,
            "--simplify" => opts.simplify = true,
            "--elim-eqs" => opts.elim_eqs = true,
            "--print-models" => opts.print_models = true,
            "--f64-score" => opts.f64_score = true,
            "--debug" => opts.debug = true,
            "--stats" => opts.stats = true,
            other if other.starts_with('-') => {
                return Err(format!("unknown option: {other}"));
            }
            other => {
                if opts.file.is_some() {
                    return Err("expected exactly one filename".into());
                }
                opts.file = Some(other.to_string());
            }
        }
    }
    Ok(opts)
}

fn main() {
    let opts = match parse_args() {
        Ok(o) => o,
        Err(e) => {
            eprintln!("error: {e}\n");
            eprint!("{USAGE}");
            std::process::exit(2);
        }
    };
    let file = match &opts.file {
        Some(f) => f.clone(),
        None => {
            eprintln!("error: a filename is required\n");
            eprint!("{USAGE}");
            std::process::exit(2);
        }
    };

    // Z3 preprocessing: jfs-opt-equivalent simplification (on by default), then
    // optionally solve-eqs. Both fall back transparently if z3 is unavailable.
    let mut input_file = file.clone();
    if opts.simplify {
        match z3::simplify_jfs(&input_file) {
            Ok(p) => input_file = p.to_string_lossy().into_owned(),
            Err(e) => eprintln!("warning: simplification failed ({e}); using raw input"),
        }
    }
    if opts.elim_eqs {
        match z3::eliminate_eqs(&input_file) {
            Ok(p) => input_file = p.to_string_lossy().into_owned(),
            Err(e) => eprintln!("warning: --elim-eqs failed ({e}); skipping it"),
        }
    }

    let cmds = read_file(&input_file).unwrap_or_else(|e| {
        eprintln!("error: cannot read {input_file}: {e}");
        std::process::exit(1);
    });

    // `get_formula` only (no `prepare_formula`): the DAG does NNF, constant
    // folding and let-resolution itself, so we skip the pipeline passes that
    // deep-clone z3's million-node let-shared output and OOM.
    let formula = get_formula(&cmds);
    let full_var_info = get_var_info(&cmds);

    // Split off RoundingMode variables: they are not searched but enumerated
    // over the five rounding-mode constants (sound + complete over modes).
    let mut rm_vars: Vec<String> = full_var_info
        .iter()
        .filter(|(_, t)| rounding_mode_type(t))
        .map(|(k, _)| k.clone())
        .collect();
    rm_vars.sort();
    let mut var_info: VarInfo = full_var_info.clone();
    for v in &rm_vars {
        var_info.remove(v);
    }

    // Build the DAG and search on a large stack: the recursive DAG build
    // descends to the formula's nesting depth, which is large for z3's
    // let-shared output and would overflow the default 8 MB main stack.
    let print_models = opts.print_models;
    let result = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || solve(formula, var_info, rm_vars, opts, input_file))
        .expect("spawn solver thread")
        .join()
        .expect("solver thread panicked");

    match result {
        SolveResult::Sat(models) => {
            println!("sat");
            if print_models {
                for m in models {
                    println!("{m}");
                }
            }
        }
        SolveResult::Unknown => println!("unknown"),
    }
}

/// Build the initial model, run the chosen SLS strategy, and (when the formula
/// has free `RoundingMode` variables) enumerate the five rounding-mode constants
/// in their place. Runs on its own large-stack thread (see the call site).
fn solve(
    formula: Sexp,
    var_info: VarInfo,
    rm_vars: Vec<String>,
    opts: Options,
    input_file: String,
) -> SolveResult {
    let mut rng = Rng::from_seed(opts.seed);

    // Initial model over the *search* variables (excludes RoundingMode).
    let mut initial = if opts.start_with_zeros {
        initialize_assignment(&var_info)
    } else {
        randomize_assignment(&var_info, &mut rng)
    };
    if opts.try_real_models {
        let raw_cmds = read_all(&std::fs::read_to_string(&input_file).unwrap_or_default());
        if let Some(real) = z3::get_real_model(&raw_cmds, &var_info) {
            initial = real;
        }
    }

    let params = Params {
        c2: opts.c2,
        max_steps: opts.step,
        wp: opts.wp,
        debug: opts.debug,
        stats: opts.stats,
        f64_score: opts.f64_score,
    };

    // Run the chosen strategy on a (possibly mode-substituted) formula.
    let run = |f: &Sexp, init: Assignment, rng: &mut Rng| -> SolveResult {
        if opts.heuristics {
            sls_heuristics(&var_info, f, &params, init, rng)
        } else if opts.vns {
            sls_vns(&var_info, f, &params, init, rng)
        } else {
            sls(&var_info, f, &params, init, rng)
        }
    };

    if rm_vars.is_empty() {
        return run(&formula, initial, &mut rng);
    }

    // Enumerate the 5^k rounding-mode combinations; combo 0 is all-RNE
    // (ROUNDING_MODES[0]), so the IEEE-default case is tried first.
    let k = rm_vars.len();
    let total = 5u64.checked_pow(k as u32).unwrap_or(u64::MAX);
    let cap = 10_000u64;
    let limit = total.min(cap);
    if total > cap {
        eprintln!("warning: {k} RoundingMode variables → {total} combinations; trying {cap}");
    }
    for idx in 0..limit {
        let mut subs: HashMap<String, String> = HashMap::new();
        let mut chosen: Vec<&str> = Vec::with_capacity(k);
        let mut x = idx;
        for v in &rm_vars {
            let d = (x % 5) as usize;
            x /= 5;
            subs.insert(v.clone(), ROUNDING_MODES[d].to_string());
            chosen.push(ROUNDING_MODES[d]);
        }
        let f = substitute(&formula, &subs);
        if let SolveResult::Sat(mut models) = run(&f, initial.clone(), &mut rng) {
            for (v, m) in rm_vars.iter().zip(&chosen) {
                models.push(Sexp::List(vec![
                    Sexp::sym("assert"),
                    Sexp::List(vec![Sexp::sym("="), Sexp::sym(*m), Sexp::sym(v.clone())]),
                ]));
            }
            return SolveResult::Sat(models);
        }
    }
    SolveResult::Unknown
}
