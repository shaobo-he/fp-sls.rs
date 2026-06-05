//! Command-line entry point. Port of `main.rkt`.

use fp_sls::parsing::parse::{get_var_info, prepare_formula};
use fp_sls::parsing::reader::{read_all, read_file};
use fp_sls::rng::Rng;
use fp_sls::sls::{
    initialize_assignment, randomize_assignment, sls, sls_heuristics, sls_vns, Params, SolveResult,
};
use fp_sls::z3;
use rug::ops::Pow;
use rug::{Integer, Rational};
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
    elim_eqs: bool,
    print_models: bool,
    debug: bool,
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
            elim_eqs: false,
            print_models: false,
            debug: false,
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
  --elim-eqs                 preprocess with Z3's solve-eqs tactic
  --print-models             print the model when sat
  --debug                    log per-step score to stderr
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
                if r < 0 || r > Rational::from(1) {
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
            "--elim-eqs" => opts.elim_eqs = true,
            "--print-models" => opts.print_models = true,
            "--debug" => opts.debug = true,
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

    // Optional Z3 solve-eqs preprocessing.
    let (input_file, _tmp): (String, Option<std::path::PathBuf>) = if opts.elim_eqs {
        match z3::eliminate_eqs(&file) {
            Ok(p) => (p.to_string_lossy().into_owned(), Some(p)),
            Err(e) => {
                eprintln!("warning: --elim-eqs failed ({e}); using original file");
                (file.clone(), None)
            }
        }
    } else {
        (file.clone(), None)
    };

    let cmds = read_file(&input_file).unwrap_or_else(|e| {
        eprintln!("error: cannot read {input_file}: {e}");
        std::process::exit(1);
    });

    let formula = prepare_formula(&cmds);
    let var_info = get_var_info(&cmds);

    let mut rng = Rng::from_seed(opts.seed);

    // Build the initial model.
    let mut initial = if opts.start_with_zeros {
        initialize_assignment(&var_info)
    } else {
        randomize_assignment(&var_info, &mut rng)
    };
    if opts.try_real_models {
        // The relaxation uses the raw declarations/assertions of the input file.
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
    };

    let result = if opts.heuristics {
        sls_heuristics(&var_info, &formula, &params, initial, &mut rng)
    } else if opts.vns {
        sls_vns(&var_info, &formula, &params, initial, &mut rng)
    } else {
        sls(&var_info, &formula, &params, initial, &mut rng)
    };

    match result {
        SolveResult::Sat(models) => {
            println!("sat");
            if opts.print_models {
                for m in models {
                    println!("{m}");
                }
            }
        }
        SolveResult::Unknown => println!("unknown"),
    }
}
