#!/usr/bin/env bash
# Correctness check on the Lean programs of the Reussir benchmark suite
# (github.com/reussir-lang/benchmark): build each lean/*.lean of a checkout
# natively, as the suite's compile.py does (`lean FILE -c`, then
# `leanc -flto -O3`), and through lean2rr (`lean -o FILE.olean FILE`, then
# scripts/l2r.py on the file, under its own name such as rbtree-zipper.lean),
# run both, and compare stdout, stderr and the exit code exactly. The
# programs check their own results (exit 1 and a FAIL line on a wrong one).
# No timing: this is not the benchmark.
#
#   tests/reussir-benchmark/run.sh BENCHMARK_CHECKOUT [NAME...]
#
# NAME is a program's file name without .lean (default: every lean/*.lean).
# Both executables run with LEAN_BACKTRACE=0. Environment: L2R_REUSSIR,
# L2R_LEAN2RR, L2R_RUSTC (see scripts/l2r.py); L2R_TEST_BUILD (build
# directory, default tests/reussir-benchmark/build); L2R_BENCH_TIMEOUT
# (seconds per run, default 900); L2R_LEAN_TOOLCHAIN (the toolchain of the
# native builds; scripts/toolchain.sh).
set -u
if [ $# -lt 1 ] || [ ! -d "$1/lean" ]; then
  echo "usage: $0 BENCHMARK_CHECKOUT [NAME...]  (a checkout of github.com/reussir-lang/benchmark)" >&2
  exit 2
fi
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
SUITE=$(cd "$1" && pwd); shift
BUILD=${L2R_TEST_BUILD:-$HERE/build}
TIMEOUT=${L2R_BENCH_TIMEOUT:-900}
mkdir -p "$BUILD"

if [ $# -gt 0 ]; then
  PROGS=("$@")
else
  PROGS=()
  for f in "$SUITE"/lean/*.lean; do PROGS+=("$(basename "$f" .lean)"); done
fi

# Run executable $1 in $d, killed after $TIMEOUT s; results in $2.{out,err,code}.
run_one() {
  local bin=$1 p=$2
  (
    cd "$d" || exit
    LEAN_BACKTRACE=0 timeout -s KILL "$TIMEOUT" "$bin" < /dev/null > "$p.out" 2> "$p.err"
    echo $? > "$p.code"
  )
}

pass=0; fail=0; failed=()
for t in "${PROGS[@]}"; do
  t=${t%.lean}
  d="$BUILD/$t"
  rm -rf "$d"; mkdir -p "$d"
  cp "$SUITE/lean/$t.lean" "$d/"
  status=ok; why=""
  if ! (cd "$d" && lean -o "$t.olean" -c "$t.c" "$t.lean" > build-native.log 2>&1 \
        && leanc -o native "$t.c" -flto -O3 >> build-native.log 2>&1); then
    status=fail; why=" native build failed (see $d/build-native.log)"
  elif ! python3 "$ROOT/scripts/l2r.py" "$d/$t.lean" -o "$d/l2r" --keep-rr "$d/$t.rr" \
        > "$d/build-l2r.log" 2>&1; then
    status=fail; why=" lean2rr build failed (see $d/build-l2r.log)"
  else
    run_one ./native native
    run_one ./l2r l2r
    for k in out err code; do
      if ! cmp -s "$d/native.$k" "$d/l2r.$k"; then
        status=fail; why="$why $k differs (diff $d/native.$k $d/l2r.$k);"
      fi
    done
  fi
  if [ $status = ok ]; then
    pass=$((pass + 1)); echo "PASS  $t (exit $(cat "$d/native.code"))"
  else
    fail=$((fail + 1)); failed+=("$t"); echo "FAIL  $t:$why"
  fi
done
echo "passed $pass, failed $fail"
[ $fail -eq 0 ]
