#!/usr/bin/env bash
# Runtime tests: build each tests/runtime/*.lean natively (lean + leanc) and
# through lean2rr + Reussir (scripts/l2r.py), run both, and compare stdout,
# stderr and the exit code exactly.
#
#   tests/runtime/run.sh [NAME...]       (default: every Rt*.lean)
#
# Per-test inputs, all optional, next to NAME.lean:
#   NAME.args   command-line arguments (one line, split by the shell)
#   NAME.stdin  standard input
#   NAME.xfail  the test is known to fail through lean2rr; the file says why
#               (a "Requests for lean2rr" item in runtime/README.md)
#
# Both executables run with LEAN_BACKTRACE=0, so panics print no stack trace.
# Environment: L2R_REUSSIR, L2R_LEAN2RR, L2R_RUSTC (see scripts/l2r.py);
# L2R_TEST_BUILD (build directory, default tests/runtime/build).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
BUILD=${L2R_TEST_BUILD:-$HERE/build}
mkdir -p "$BUILD"

if [ $# -gt 0 ]; then
  TESTS=("$@")
else
  TESTS=()
  for f in "$HERE"/Rt*.lean; do TESTS+=("$(basename "$f" .lean)"); done
fi

pass=0; fail=0; xfail=0; xpass=0; failed=()
for t in "${TESTS[@]}"; do
  t=${t%.lean}
  src="$HERE/$t.lean"
  d="$BUILD/$t"
  rm -rf "$d"; mkdir -p "$d"
  cp "$src" "$d/"
  args=""; [ -f "$HERE/$t.args" ] && args=$(cat "$HERE/$t.args")
  stdin=/dev/null; [ -f "$HERE/$t.stdin" ] && stdin="$HERE/$t.stdin"
  status=ok; why=""
  if ! (cd "$d" && lean -o "$t.olean" -c "$t.c" "$t.lean" > build-native.log 2>&1 \
        && leanc -O3 -DNDEBUG "$t.c" -o native >> build-native.log 2>&1); then
    status=fail; why="native build failed (see $d/build-native.log)"
  elif ! python3 "$ROOT/scripts/l2r.py" "$t" --lean-path "$d" -o "$d/l2r" --keep-rr "$d/$t.rr" \
        > "$d/build-l2r.log" 2>&1; then
    status=fail; why="lean2rr build failed (see $d/build-l2r.log)"
  else
    # shellcheck disable=SC2086
    (cd "$d" && LEAN_BACKTRACE=0 ./native $args < "$stdin" > native.out 2> native.err; echo $? > native.code)
    # shellcheck disable=SC2086
    (cd "$d" && LEAN_BACKTRACE=0 timeout 120 ./l2r $args < "$stdin" > l2r.out 2> l2r.err; echo $? > l2r.code)
    for k in out err code; do
      if ! cmp -s "$d/native.$k" "$d/l2r.$k"; then
        status=fail; why="$why $k differs (diff $d/native.$k $d/l2r.$k);"
      fi
    done
  fi
  if [ -f "$HERE/$t.xfail" ]; then
    if [ $status = ok ]; then
      xpass=$((xpass + 1)); echo "XPASS $t (remove $t.xfail)"
    else
      xfail=$((xfail + 1)); echo "XFAIL $t: $(head -1 "$HERE/$t.xfail")"
    fi
  elif [ $status = ok ]; then
    pass=$((pass + 1)); echo "PASS  $t"
  else
    fail=$((fail + 1)); failed+=("$t"); echo "FAIL  $t:$why"
  fi
done
echo "passed $pass, failed $fail, expected failures $xfail, unexpected passes $xpass"
[ $fail -eq 0 ]
