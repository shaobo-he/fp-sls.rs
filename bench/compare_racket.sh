#!/usr/bin/env bash
# Compare this Rust port against the original Racket OL1V3R on the same files,
# with the same --step/--seed, in parallel. Reports each solver's answer and
# wall-clock time (the Racket runtime includes ~0.3 s interpreter startup).
#
# Requires `racket` on PATH and the OL1V3R checkout compiled with `raco make
# main.rkt`. Point OL1V3R at the checkout (default: ../OL1V3R).
#
# Usage: bench/compare_racket.sh <dir-with-smt2> [step] [seed] [timeout] [jobs]
set -u
DIR="${1:?usage: bench/compare_racket.sh <dir> [step] [seed] [timeout] [jobs]}"
STEP="${2:-10000}"
SEED="${3:-1}"
TMO="${4:-60}"
JOBS="${5:-$(nproc)}"
RUST="$(cd "$(dirname "$0")/.." && pwd)/target/release/fp-sls"
RKT="${OL1V3R:-$(cd "$(dirname "$0")/../../OL1V3R" 2>/dev/null && pwd)}/main.rkt"
# EXTRA: identical extra flags applied to BOTH tools (e.g. "--vns --elim-eqs
# --try-real-models"). Only use flags that both implementations support.
EXTRA="${EXTRA:-}"
export RUST RKT STEP SEED TMO EXTRA

command -v racket >/dev/null || { echo "racket not on PATH"; exit 1; }
[ -f "$RKT" ] || { echo "OL1V3R main.rkt not found at $RKT (set \$OL1V3R)"; exit 1; }

RESULTS="$(mktemp)"; export RESULTS

# Run a command under timeout, capture exit code WITHOUT a pipe.
run_timed() {  # prints "<answer>\t<seconds>"
  local out rc t0 t1
  t0=$EPOCHREALTIME
  out="$(timeout "$TMO" "$@" 2>/dev/null)"; rc=$?
  t1=$EPOCHREALTIME
  out="$(printf '%s' "$out" | head -1)"
  [ "$rc" -eq 124 ] && out=timeout
  [ -z "$out" ] && out=error
  printf '%s\t%s' "$out" "$(awk "BEGIN{printf \"%.2f\", $t1-$t0}")"
}

work() {
  f="$1"
  # shellcheck disable=SC2086  (intentional word-splitting of $EXTRA)
  IFS=$'\t' read -r ra rt < <(run_timed "$RUST" --step "$STEP" --seed "$SEED" $EXTRA "$f")
  IFS=$'\t' read -r ka kt < <(run_timed racket "$RKT" --step "$STEP" --seed "$SEED" $EXTRA "$f")
  printf "%s\t%s\t%s\t%s\t%s\n" "$(basename "$f")" "$ra" "$rt" "$ka" "$kt" >> "$RESULTS"
  printf "%-40s rust=%-8s %6ss   racket=%-8s %6ss\n" "$(basename "$f")" "$ra" "$rt" "$ka" "$kt"
}
export -f run_timed work

printf "%-40s %-17s %s\n" "file" "rust (fp-sls)" "racket (OL1V3R)"
find "$DIR" -name '*.smt2' | sort | xargs -P "$JOBS" -I{} bash -c 'work "$@"' _ {}

echo ""
sort "$RESULTS" | awk -F'\t' '
  { n++; if ($2=="sat") rs++; if ($4=="sat") ks++; if ($2==$4) agree++
    if ($2=="sat" && $4=="sat") { rsum+=$3; ksum+=$5; bn++ } }
  END { printf "files=%d  rust sat=%d  racket sat=%d  same-answer=%d\n", n, rs, ks, agree
        if (bn) printf "mean time on both-sat: rust=%.2fs  racket=%.2fs  (%d files)\n", rsum/bn, ksum/bn, bn }'
rm -f "$RESULTS"
