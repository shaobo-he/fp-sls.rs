# fp-sls — OL1V3R in Rust

A Rust port of [OL1V3R](https://github.com/soarlab/OL1V3R), an incomplete
stochastic-local-search (SLS) solver for quantifier-free bit-vector and
floating-point SMT (`QF_BV` / `QF_FP`). It reimplements

> A. Fröhlich, A. Biere, C. M. Wintersteiger, Y. Hamadi.
> *Stochastic Local Search for Satisfiability Modulo Theories.* AAAI 2015.

directly on the theory level: parse an SMT-LIB formula, put it in negation
normal form, and then run a score-guided local search over assignments to the
bit-vector / floating-point variables, escaping local optima with random walks
and randomization.

This port is faithful to the original Racket implementation, additionally
addresses the repository's `TODOs.md`, and fixes two latent bugs found along the
way (see [Deviations](#deviations-from-the-racket-original)).

## Building

The numeric core uses [`rug`](https://crates.io/crates/rug) (GMP/MPFR/MPC).
`rug` builds GMP and MPFR from source, so a C toolchain is required: `cc`, `m4`,
and `make`. Then:

```sh
cargo build --release
```

The binary is `target/release/fp-sls`. The default simplification preprocessing
(see [below](#preprocessing-no-jfs-dependency)) and the `--try-real-models` /
`--elim-eqs` options shell out to a [`z3`](https://github.com/Z3Prover/z3) binary
on `PATH`; without it they degrade gracefully (the raw input is used).

## Usage

```
fp-sls [options] <file.smt2>

  --seed <n>                 RNG seed (1..2^31-1)                  [default 1]
  --c2 <r>                   score scaling constant in [0,1]       [default 1/2]
  --wp <p>                   diversification probability in [0,1]  [default 0.001]
  --step <n>                 number of search steps                [default 200]
  --initialize-with-random   start from random values (else all 0s)
  --try-real-models          seed search from a Z3 real-relaxation model
  --vns                      use variable-neighborhood search
  --heuristics               use the paper's heuristics (UCB + PAWS + restarts)
  --no-simplify              skip the default z3 simplification (jfs-opt equivalent)
  --elim-eqs                 also preprocess with Z3's solve-eqs tactic
  --print-models             print the model when sat
  --debug                    log per-step score to stderr
  --stats                    print `steps <n>` to stderr on a sat result
```

It prints `sat` (optionally followed by the model) or `unknown`. As an
incomplete solver it never reports `unsat`.

### Preprocessing (no JFS dependency)

By default the input is simplified with z3 before search. The NSV'19 paper
preprocessed benchmarks with JFS's `jfs-opt` tool; that tool's standard pipeline
is really just two z3 tactics — `simplify` (with `bv_ite2id=true`) and
`propagate-values` — with the remaining passes (and-hoist, true/duplicate
elimination, contradiction→false) performed for free by z3's `(apply …)`
machinery. So we reproduce `jfs-opt` with a single z3 tactic and **no JFS (LLVM/
clang) build**: strip `(check-sat)`, apply
`(then (! simplify :bv_ite2id true) propagate-values …)`, and rebuild the query
from the resulting goal. This is on by default (disable with `--no-simplify`),
folds away constructs the evaluator doesn't handle natively (e.g. a constant
`ite`), and uses `propagate-values` rather than `solve-eqs` so no declared
variable is substituted away. It falls back to the raw input if z3 is absent.

```sh
fp-sls --step 10000 --print-models tests/smt/schanda/spark/incorrect_reordering.smt2
```

## Architecture

The module layout mirrors the Racket repository for traceability:

| Rust | Racket | role |
|------|--------|------|
| `src/data/bitvec.rs` | `data/bit-vec.rkt` | bit-vectors, arithmetic, neighborhoods |
| `src/data/fp.rs` | `data/fp.rkt` | IEEE floats (arbitrary format) over MPFR |
| `src/data/eval.rs` | `data/eval.rkt` | term evaluator |
| `src/data/value.rs` | — | the `BV \| FP` runtime value |
| `src/score.rs` | `score.rkt` | the scoring function |
| `src/sls.rs` | `sls.rkt` | the SLS / VNS / heuristic search loops |
| `src/parsing/reader.rs` | reader in `parsing/parse.rkt` | SMT-LIB s-expression reader |
| `src/parsing/parse.rs` | `parsing/parse.rkt` | assertions, types, variable collection |
| `src/parsing/transform.rs` | `parsing/transform.rkt` | NNF, simplify, constant folding, let-elim |
| `src/z3.rs` | `fp2real.rkt`, `elim-eqs.rkt` | optional Z3-backed helpers |
| `src/main.rs` | `main.rkt` | CLI |

### Key design decisions

* **Floating-point via MPFR.** Racket's `math/bigfloat` is MPFR; the port uses
  `rug::Float` with precision set to the significand width. MPFR's
  `to_integer_exp` reproduces `bigfloat->sig+exp` exactly, so BV↔FP conversions,
  subnormal rounding, and overflow-to-∞ are bit-for-bit faithful for arbitrary
  `(exp, sig)` formats (Float16/32/64/128 and beyond).
* **Exact rational scores.** All scores are `rug::Rational`, so `argmax` and the
  improvement test are exact. This realizes the Racket TODO *"add types to score
  functions (they should be rational rather than floating point)"*.
* **Reproducibility.** `--seed` seeds a `StdRng`; runs are deterministic for a
  fixed seed (but do not bit-match Racket's generator).

## Addressing `TODOs.md`

| TODO | status |
|------|--------|
| (urgent 1–3) FP score / FP evaluator / parser fixes | already struck through upstream; ported and verified |
| **urgent 7** — rational score types | **done**: scores are `rug::Rational` throughout |
| **urgent 6** — add tests | **done**: unit tests (`src/data/fp.rs`) + integration tests with model validation (`tests/integration.rs`) |
| **urgent 4 / 5** — try Z3 SLS, FP→BV on Z3 SLS | a parallel comparison harness is provided (`bench/run.sh`); see [Benchmarks](#benchmarks). Z3's SLS engine is QF_BV-only, so it cannot take these QF_FP inputs directly — the harness compares against Z3's default tactic and exercises `sls.enable=true` for QF_BV inputs |
| **non-urgent 1** — SLS heuristics from the paper | **done** (`--heuristics`): UCB assertion selection, additive PAWS assertion weights, and an exponential restart schedule (§4 of the paper) |

The open research questions in `QUESTIONS.md` (good FP score/neighborhood
design, etc.) are left as-is; they are not actionable code changes.

## Deviations from the Racket original

* **Bug fix — `score.rkt:210`.** The clause for un-negated `fp.gt` dropped its
  `env` argument (`(score2 op1 op2 assignment (score/fpgt c))`), an arity error
  that crashes on any positive `fp.gt`. Fixed here.
* **Bug fix — `eval.rkt` `let`.** The evaluator's `let` case called `eval` with
  two arguments instead of three, crashing whenever a `let` survived inside a
  term operand. The port implements the intended three-argument behaviour.
* **`remove-const-bv2fp` is wired into the pipeline.** The Racket `main` omitted
  it, so the ubiquitous `((_ to_fp e s) (_ bv… w))` bit-pattern constants were
  not folded. Folding them (matching parser TODO #3) lets more inputs run.
* **`bvudiv` / `bvurem`.** Implemented with correct SMT-LIB semantics
  (division/remainder by zero defined); the Racket `bvudiv` used exact rational
  `/` and `bvurem` was unimplemented. Not exercised by the QF_FP benchmarks.
* The unused `remove-equalities` helper is intentionally omitted.

## Benchmarks

`bench/run.sh <dir> [step] [seed] [timeout] [jobs]` runs this solver and Z3 over
a tree of `.smt2` files in parallel, streaming results and a summary. On the
[QF_FP_OPT](https://github.com/shaobo-he/QF_FP_OPT) set used by OL1V3R
(51 instances, 30 s timeout, `--step 10000 --seed 1`):

```
fp-sls : sat=49  unknown=1  timeout=0  error/unsupported=1
z3     : sat=23  timeout=27  error=1
both definitively sat (agreement): 21
```

This reproduces the paper's central observation: SLS finds models quickly on
many satisfiable floating-point instances, while bit-blasting (Z3's default)
times out on 27 of them. Z3 is a *complete* solver, so `timeout` means "did not
finish in 30 s", not "cannot solve" — the comparison is about speed on
satisfiable instances. Where both return a definitive `sat`, they agree.

The single `unknown` is `average_6.smt2` (a precision counterexample needing a
specific witness — solvable at a larger `--step` budget); the single `error` is
`protected_divide.smt2`, which uses `ite` (see [Limitations](#limitations)).

### Comparison with the Racket original

`bench/compare_racket.sh <dir> [step] [seed] [timeout] [jobs]` runs this port and
the original Racket OL1V3R (compiled with `raco make`) on the same files, same
flags and `--step`/`--seed`.

**Baseline vs baseline** (no flags), 51-file set:

* **Same answers** — both solve the same instances (small differences are
  random-seed luck at a fixed step budget; the two use different RNGs).
* **The port is much faster.** Mean wall-clock on commonly-solved instances:
  ~0.4 s (Rust) vs ~2.8 s (Racket). The Racket figure includes a ~0.36 s
  interpreter-startup floor (Rust's is ~1 ms); even subtracting it, the
  search-time speed-up is **20–50× on the harder instances** (e.g.
  `test_v3_r8_vr10…`: 0.72 s vs 14.2 s) — compiled Rust + GMP rationals vs the
  Racket VM, same algorithm and same MPFR backend.

**All shared flags** (`--vns --elim-eqs --try-real-models`) on both: the two
tools **agree on 50/51** (the 51st is `protected_divide`, which uses `ite` —
both fail), mean **0.03 s (Rust) vs 0.62 s (Racket)**. This required a
z3-compatibility fix to the Racket original, whose z3-output parsing predated
current z3 (`get-model` model format, the `/0` division function, and inputs
without `(check-sat)`); the fix is merged upstream into
[soarlab/OL1V3R](https://github.com/soarlab/OL1V3R). `src/z3.rs` here carries the
analogous `--elim-eqs` soundness fix.

Notes on a fully like-for-like comparison:

* `--heuristics` exists **only in this port** (it implements the Racket repo's
  proposed-but-unimplemented future work), so it is excluded from parity runs.
* `--vns` is an alternative neighborhood strategy, not a strict speed-up — on
  this set it solves slightly fewer instances than the default within a budget.

## Testing

```sh
cargo test          # unit tests (FP/IEEE) + end-to-end solve + model validation
cargo clippy        # lints
```

`tests/integration.rs` solves real benchmarks and *validates* each returned
model by reconstructing the assignment and checking the formula scores to
exactly 1.

## Rounding modes

Unlike the Racket original (which ignored the rounding-mode argument and always
rounded to nearest), the evaluator **honors the rounding mode** of every FP
operation: all five IEEE modes (`roundNearestTiesToEven`, `roundTowardZero`,
`roundToward{Positive,Negative}`, `roundNearestTiesToAway`) map to MPFR's, with
mode-aware overflow (e.g. toward-zero yields max-normal, not ∞). A *non-constant*
rounding mode is rejected (error) rather than silently treated as nearest, so
results stay sound.

A `RoundingMode` **variable** is not searched but **enumerated**: the solver
tries each of the five constants in its place (cartesian product for several
variables, `roundNearestTiesToEven` first), reporting `sat` as soon as one
combination succeeds — sound *and* complete over rounding modes. The chosen mode
is included in the printed model.

(Subnormal results use the same two-step rounding as OL1V3R — round to precision,
then to the subnormal grid — so they can be off by one ULP exactly at the
denormal boundary; inherited from the original.)

## Limitations

These match the Racket original (the evaluator is deliberately partial):

* No `ite`, `concat`, `extract`, shifts, or bit-vector↔float reinterpretation of
  *variables* in the evaluator. Such inputs abort with `unsupported operation`.
  (`--simplify`, on by default, folds away constructs z3 can eliminate — e.g. a
  constant `ite` — but a genuine `ite` over variables survives.)
* `fp.fma`, `fp.rem`, `fp.roundToIntegral`, `fp.min`/`max`/`abs` are not
  implemented.
* `--vns` supports floating-point variables only.
* Incomplete solver: only `sat` / `unknown` are reported, never `unsat`.

## License

The original OL1V3R is released under the CRAPL. This port is provided under the
MIT license; see `Cargo.toml`.
