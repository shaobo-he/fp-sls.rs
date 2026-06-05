#!/usr/bin/env bash
# Compare this SLS port against Z3 (default, bit-blasting) on a tree of .smt2
# files, in parallel. Each cell is the solver's answer, or `timeout` (exceeded
# the per-file limit) / `error` (non-zero exit with no answer, e.g. an
# unsupported operation). This is a SPEED comparison: Z3 is a complete solver,
# so `timeout` means "did not finish in TMO seconds", not "cannot solve".
#
# Z3's own SLS engine (relevant to Racket TODOs 4/5) is bit-vector only and is
# not invoked here on QF_FP; for a QF_BV input you can compare against it with
#   z3 tactic.default_tactic=sls <file.smt2>   (or (check-sat-using sls))
#
# Usage: bench/run.sh <dir-with-smt2> [step] [seed] [timeout_s] [jobs]
set -u
DIR="${1:?usage: bench/run.sh <dir> [step] [seed] [timeout] [jobs]}"
STEP="${2:-10000}"
SEED="${3:-1}"
TMO="${4:-20}"
JOBS="${5:-$(nproc)}"
SLS="$(cd "$(dirname "$0")/.." && pwd)/target/release/fp-sls"
export SLS STEP SEED TMO

RESULTS="$(mktemp)"
export RESULTS

# Run one command under timeout; classify as its first stdout line, else
# `timeout` (exit 124) or `error` (other non-zero exit, no answer).
# NB: capture the exit code WITHOUT a pipe — `cmd | head` would clobber it.
run1() {
  local out rc
  out="$(timeout "$TMO" "$@" 2>/dev/null)"; rc=$?
  out="$(printf '%s' "$out" | head -1)"
  if [ "$rc" -eq 124 ]; then echo timeout
  elif [ -n "$out" ]; then echo "$out"
  else echo error
  fi
}

# Worker: print one aligned, live row and append a tab-separated record.
work() {
  f="$1"
  ours=$(run1 "$SLS" --step "$STEP" --seed "$SEED" "$f")
  z3r=$(run1 z3 -smt2 "$f")
  printf "%s\t%s\t%s\n" "$(basename "$f")" "$ours" "$z3r" >> "$RESULTS"
  printf "%-44s %-12s %-12s\n" "$(basename "$f")" "$ours" "$z3r"
}
export -f run1 work

printf "%-44s %-12s %-12s\n" "file" "fp-sls" "z3 (default)"
# Stream each result the moment its worker finishes.
find "$DIR" -name '*.smt2' | sort | xargs -P "$JOBS" -I{} bash -c 'work "$@"' _ {}

echo ""
sort "$RESULTS" | awk -F'\t' '
  { n++
    if ($2=="sat") ours++; if ($2=="timeout") ot++; if ($2=="error") err++; if ($2=="unknown") ou++
    if ($3=="sat") z3++; if ($3=="timeout") zt++; if ($3=="error") ze++
    if ($2=="sat" && $3=="sat") both++ }
  END { printf "files=%d  (per-file timeout %ss)\n", n, ENVIRON["TMO"]
        printf "fp-sls : sat=%d  unknown=%d  timeout=%d  error/unsupported=%d\n", ours, ou, ot, err
        printf "z3     : sat=%d  timeout=%d  error=%d\n", z3, zt, ze
        printf "both definitively sat (agreement): %d\n", both }'
rm -f "$RESULTS"
