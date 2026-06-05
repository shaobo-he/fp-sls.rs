# Test fixtures

A small, curated subset of QF_FP benchmarks used to drive the integration tests
in `tests/integration.rs` and the benchmark scripts in `bench/`.

These files come from <https://github.com/shaobo-he/QF_FP_OPT> (the benchmark
set used in He, Baranowski & Rakamarić, "Stochastic Local Search for Solving
Floating-Point Constraints", NSV 2019). They are themselves derived from the
SMT-LIB `QF_FP` benchmarks. The full set can be fetched with:

```sh
git clone https://github.com/shaobo-he/QF_FP_OPT.git
```
