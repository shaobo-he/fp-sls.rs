//! Optional Z3-backed helpers. Ports of `fp2real.rkt` and `elim-eqs.rkt`.
//!
//! These shell out to a `z3` binary on `PATH`:
//!   * [`get_real_model`] (`--try-real-models`): solve a real relaxation of the
//!     QF_FP formula and use Z3's model to seed the initial assignment;
//!   * [`eliminate_eqs`] (`--elim-eqs`): apply Z3's `solve-eqs` tactic to
//!     preprocess equalities.
//!
//! If `z3` is not installed both degrade gracefully (returning `None`/`Err`),
//! and the caller falls back to the default behaviour.

use crate::data::fp::FloatingPoint;
use crate::data::value::{Assignment, Value};
use crate::parsing::parse::{fp_type, fp_type_widths};
use crate::parsing::reader::read_all;
use crate::parsing::transform::{fp_to_real, remove_fpconst};
use crate::sexp::Sexp;
use crate::sls::{initialize_assignment, VarInfo};
use rug::ops::Pow;
use rug::{Integer, Rational};
use std::io::Write;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn temp_path(tag: &str) -> std::path::PathBuf {
    let n = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let mut p = std::env::temp_dir();
    p.push(format!("fp-sls-{}-{}-{}.smt2", std::process::id(), tag, n));
    p
}

/// Per-call z3 wall-clock limit (seconds) and memory limit (MB). Without these,
/// z3 can run unboundedly on a hard (e.g. nonlinear, from `--try-real-models`)
/// query — and if our process is killed meanwhile, the z3 child is orphaned and
/// keeps running, so many such orphans accumulate and exhaust the machine. With
/// the limits z3 self-terminates and our parsers fall back gracefully.
const Z3_TIMEOUT_SECS: u32 = 60;
const Z3_MEMORY_MB: u32 = 2048;

fn run_z3(path: &std::path::Path) -> std::io::Result<String> {
    let out = Command::new("z3")
        .arg(format!("-T:{Z3_TIMEOUT_SECS}"))
        .arg(format!("-memory:{Z3_MEMORY_MB}"))
        .arg(path)
        .output()?;
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

// ---------- decimal / arithmetic helpers for parsing Z3 models ----------

fn parse_number(s: &str) -> Option<Rational> {
    if let Ok(i) = Integer::from_str_radix(s, 10) {
        return Some(Rational::from(i));
    }
    // Decimal: [-]int[.frac]
    let (neg, body) = match s.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, s),
    };
    let (int_part, frac_part) = match body.split_once('.') {
        Some((a, b)) => (a, b),
        None => (body, ""),
    };
    if int_part.is_empty() && frac_part.is_empty() {
        return None;
    }
    let int_digits = if int_part.is_empty() { "0" } else { int_part };
    let scale = Integer::from(10).pow(frac_part.len() as u32);
    let int_val = Integer::from_str_radix(int_digits, 10).ok()?;
    let frac_val = if frac_part.is_empty() {
        Integer::from(0)
    } else {
        Integer::from_str_radix(frac_part, 10).ok()?
    };
    let num = int_val * &scale + frac_val;
    let mut r = Rational::from((num, scale));
    if neg {
        r = -r;
    }
    Some(r)
}

/// `(simple-eval expr)` — evaluate a Z3 model value over the rationals.
fn simple_eval(s: &Sexp) -> Option<Rational> {
    match s {
        Sexp::Int(i) => Some(Rational::from(i.clone())),
        Sexp::Sym(t) => parse_number(t),
        Sexp::List(items) => match (items[0].as_sym(), items.len()) {
            (Some("+"), 3) => Some(simple_eval(&items[1])? + simple_eval(&items[2])?),
            (Some("-"), 3) => Some(simple_eval(&items[1])? - simple_eval(&items[2])?),
            (Some("-"), 2) => Some(-simple_eval(&items[1])?),
            (Some("*"), 3) => Some(simple_eval(&items[1])? * simple_eval(&items[2])?),
            (Some("/"), 3) => Some(simple_eval(&items[1])? / simple_eval(&items[2])?),
            _ => None,
        },
        _ => None,
    }
}

/// `(model->assignment sexp)` — `id ↦ rational` from `(define-fun id () Real v)`.
fn model_to_assignment(defs: &[Sexp]) -> HashMapRat {
    let mut m = HashMapRat::new();
    for d in defs {
        if let Sexp::List(items) = d {
            if items.len() == 5 && items[0].is_sym("define-fun") {
                if let Some(id) = items[1].as_sym() {
                    if let Some(v) = simple_eval(&items[4]) {
                        m.insert(id.to_string(), v);
                    }
                }
            }
        }
    }
    m
}

type HashMapRat = std::collections::HashMap<String, Rational>;

/// `(get-real-model file)` — solve the real relaxation and parse Z3's model.
pub fn get_real_model(cmds: &[Sexp], var_info: &VarInfo) -> Option<Assignment> {
    // Build the real relaxation and ask for a model.
    let path = temp_path("real");
    {
        let mut f = std::fs::File::create(&path).ok()?;
        for cmd in cmds {
            let real = fp_to_real(&remove_fpconst(cmd));
            writeln!(f, "{real}").ok()?;
        }
        writeln!(f, "(get-model)").ok()?;
    }
    let output = run_z3(&path).ok()?;
    let _ = std::fs::remove_file(&path);

    let forms = read_all(&output);
    if forms.first().map(|f| f.is_sym("sat")) != Some(true) {
        return None;
    }
    // Accept either `(model (define-fun …) …)` or a bare `((define-fun …) …)`.
    let defs: Vec<Sexp> = match forms.get(1) {
        Some(Sexp::List(items)) if items.first().map(|h| h.is_sym("model")) == Some(true) => {
            items[1..].to_vec()
        }
        Some(Sexp::List(items)) => items.clone(),
        _ => return None,
    };
    let real_model = model_to_assignment(&defs);
    Some(real_model_to_fp_model(&real_model, var_info))
}

/// `(real-model->fp-model real-model var-info)` — overlaid onto the all-zero
/// model so every variable is defined even if Z3's model omitted some.
pub fn real_model_to_fp_model(real_model: &HashMapRat, var_info: &VarInfo) -> Assignment {
    let mut asn = initialize_assignment(var_info);
    for (k, v) in real_model {
        if let Some(ty) = var_info.get(k) {
            if fp_type(ty) {
                let (e, s) = fp_type_widths(ty);
                asn.insert(k.clone(), Value::FP(FloatingPoint::real_from_rational(v, e, s)));
            }
        }
    }
    asn
}

/// The `jfs-opt --standard-passes` pipeline, reproduced with z3 tactics alone.
///
/// JFS's `SimplificationPass` is z3's `simplify` (with `bv_ite2id=true`) and its
/// `ConstantPropagationPass` is z3's `propagate-values`; the other standard
/// passes (and-hoist, true/duplicate-constraint elimination, contradiction→
/// false) are performed for free by z3's goal/`(apply …)` machinery. So a single
/// `(apply (then …))` reproduces the whole pipeline — no JFS (LLVM/clang) build
/// needed. (`propagate-values`, not `solve-eqs`, so no declared variable is
/// substituted away.)
pub const JFS_OPT_TACTIC: &str = "(then (! simplify :bv_ite2id true) \
                                  propagate-values \
                                  (! simplify :bv_ite2id true) \
                                  propagate-values \
                                  (! simplify :bv_ite2id true))";

/// Apply a z3 tactic to a query and return the path to a rewritten SMT-LIB file
/// (original declarations + the resulting goal's literals + check-sat).
///
/// Robust to inputs without `(check-sat)` (some QF_FP files omit it) and to z3
/// being unavailable or emitting an unexpected result — in those cases it falls
/// back to the original file rather than dropping constraints.
fn apply_z3_tactic(path: &str, tactic: &str, tag: &str) -> std::io::Result<std::path::PathBuf> {
    let raw = std::fs::read_to_string(path)?;
    let cmds = read_all(&raw);
    let decls: Vec<&Sexp> = cmds
        .iter()
        .filter(|e| matches!(e.head_sym(), Some("declare-const") | Some("declare-fun")))
        .collect();

    // Strip the trailing solver commands and append the tactic application.
    // We must remove `(exit)` (and `(get-model)` etc.) too, not just
    // `(check-sat)`: many SMT-LIB files end with `(check-sat) (exit)`, and a
    // leftover `(exit)` makes z3 quit *before* reaching the appended tactic
    // (producing empty output and a silent fallback to the unsimplified file).
    let stripped = raw
        .replace("(check-sat)", "")
        .replace("(exit)", "")
        .replace("(get-model)", "")
        .replace("(get-unsat-core)", "");
    let tactic_file = temp_path(&format!("{tag}-in"));
    std::fs::write(&tactic_file, format!("{stripped}\n(apply {tactic})\n"))?;
    // If z3 is unavailable, transparently fall back to the original file.
    let output = match run_z3(&tactic_file) {
        Ok(o) => o,
        Err(_) => {
            let _ = std::fs::remove_file(&tactic_file);
            return Ok(std::path::PathBuf::from(path));
        }
    };
    let _ = std::fs::remove_file(&tactic_file);

    // z3 prints `(goals (goal <lits…> :precision … :depth …))`. Take the literals
    // up to the first `:keyword` (so bare `false`/`true` goals are preserved);
    // fall back to the original file if the output is not a parseable goal.
    let forms = read_all(&output);
    let goal_lits: Option<Vec<Sexp>> = forms
        .first()
        .and_then(|f| f.as_list())
        .filter(|g| g.first().is_some_and(|h| h.is_sym("goals")))
        .and_then(|g| g.get(1)) // (goal …)
        .and_then(|goal| goal.as_list())
        .map(|goal| {
            goal[1..]
                .iter()
                .take_while(|x| !matches!(x, Sexp::Sym(s) if s.starts_with(':')))
                .cloned()
                .collect()
        });

    let goal_lits = match goal_lits {
        Some(lits) => lits,
        None => return Ok(std::path::PathBuf::from(path)),
    };

    let out_path = temp_path(&format!("{tag}-out"));
    {
        let mut f = std::fs::File::create(&out_path)?;
        for d in &decls {
            writeln!(f, "{d}")?;
        }
        for lit in &goal_lits {
            writeln!(f, "{}", Sexp::List(vec![Sexp::sym("assert"), lit.clone()]))?;
        }
        writeln!(f, "(check-sat)")?;
    }
    Ok(out_path)
}

/// jfs-opt-equivalent simplification preprocessing (z3 only). See [`JFS_OPT_TACTIC`].
pub fn simplify_jfs(path: &str) -> std::io::Result<std::path::PathBuf> {
    apply_z3_tactic(path, JFS_OPT_TACTIC, "simplify")
}

/// `(eliminate-eqs file)` — run Z3's `solve-eqs` tactic.
pub fn eliminate_eqs(path: &str) -> std::io::Result<std::path::PathBuf> {
    apply_z3_tactic(path, "solve-eqs", "solveeqs")
}
