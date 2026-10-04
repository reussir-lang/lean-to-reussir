#!/usr/bin/env bash
# Runtime tests: build each tests/runtime/*.lean natively (lean + leanc) and
# through lean2rr + Reussir (scripts/l2r.py), run both, and compare stdout,
# stderr and the exit code exactly. The lean2rr executable must also have no
# text relocations (DT_TEXTREL), as native Lean's has none (Reussir bug 34).
#
#   tests/runtime/run.sh [NAME...]       (default: every Rt*.lean)
#
# Per-test inputs, all optional, next to NAME.lean:
#   NAME.args   command-line arguments (one line, split by the shell)
#   NAME.stdin  standard input
#   NAME.pipe   a bash command line to run instead ($BIN = executable,
#               $ARGS = arguments; pipefail), e.g. `$BIN | head -1`
#   NAME.opts   lean2rr optimizations to turn off for this test (one line,
#               comma-separated, added to L2R_DISABLE_OPTS), e.g. to check a
#               shape the default passes hide
#   NAME.xfail  the test is known to fail through lean2rr; the file says why
#               (a "Requests for lean2rr" item in runtime/README.md)
#
# Both executables run with LEAN_BACKTRACE=0, so panics print no stack trace.
# Environment: L2R_REUSSIR, L2R_LEAN2RR, L2R_RUSTC (see scripts/l2r.py);
# L2R_DISABLE_OPTS / L2R_ENABLE_OPTS (comma-separated lean2rr optimizations
# to turn off / on, passed on by scripts/l2r.py; `lean2rr --list-opts`);
# L2R_TEST_BUILD (build directory, default tests/runtime/build);
# L2R_LEAN_TOOLCHAIN (the Lean toolchain of the native builds, default the
# one lean2rr/lean-toolchain pins; scripts/toolchain.sh).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
BUILD=${L2R_TEST_BUILD:-$HERE/build}
mkdir -p "$BUILD"

if [ $# -gt 0 ]; then
  TESTS=("$@")
else
  TESTS=()
  for f in "$HERE"/Rt*.lean; do TESTS+=("$(basename "$f" .lean)"); done
fi

# Run executable $1 of test $t in $d with its args/stdin (or its NAME.pipe
# command line, where $BIN is the executable and $ARGS the arguments; run by
# bash with pipefail), killing it after 120 s; results in $2.{out,err,code}.
run_one() {
  local bin=$1 p=$2
  (
    cd "$d" || exit
    export LEAN_BACKTRACE=0
    if [ -f "$HERE/$t.pipe" ]; then
      BIN=$bin ARGS="$args" bash -o pipefail -c "$(cat "$HERE/$t.pipe")" < "$stdin" > "$p.out" 2> "$p.err" &
    else
      # shellcheck disable=SC2086
      $bin $args < "$stdin" > "$p.out" 2> "$p.err" &
    fi
    local pid=$!
    ( sleep 120; kill -9 "$pid" 2> /dev/null ) &
    local watch=$!
    wait "$pid" 2> /dev/null
    echo $? > "$p.code"
    kill "$watch" 2> /dev/null
    wait "$watch" 2> /dev/null
  )
}

pass=0; fail=0; xfail=0; xpass=0; failed=()
for t in "${TESTS[@]}"; do
  t=${t%.lean}
  src="$HERE/$t.lean"
  d="$BUILD/$t"
  rm -rf "$d"; mkdir -p "$d"
  cp "$src" "$d/"
  args=""; [ -f "$HERE/$t.args" ] && args=$(cat "$HERE/$t.args")
  stdin=/dev/null; [ -f "$HERE/$t.stdin" ] && stdin="$HERE/$t.stdin"
  opts=${L2R_DISABLE_OPTS:-}
  [ -f "$HERE/$t.opts" ] && opts="$opts${opts:+,}$(tr -d ' \n' < "$HERE/$t.opts")"
  status=ok; why=""
  if ! (cd "$d" && lean -o "$t.olean" -c "$t.c" "$t.lean" > build-native.log 2>&1 \
        && leanc -O3 -DNDEBUG "$t.c" -o native >> build-native.log 2>&1); then
    status=fail; why="native build failed (see $d/build-native.log)"
  elif ! L2R_DISABLE_OPTS=$opts python3 "$ROOT/scripts/l2r.py" "$t" --lean-path "$d" -o "$d/l2r" --keep-rr "$d/$t.rr" \
        > "$d/build-l2r.log" 2>&1; then
    status=fail; why="lean2rr build failed (see $d/build-l2r.log)"
  else
    run_one ./native native
    run_one ./l2r l2r
    for k in out err code; do
      if ! cmp -s "$d/native.$k" "$d/l2r.$k"; then
        status=fail; why="$why $k differs (diff $d/native.$k $d/l2r.$k);"
      fi
    done
    # Like native Lean's, the executable is a PIE without text relocations
    # (Reussir bug 34: rrc compiled static code into a PIE).
    if readelf -d "$d/l2r" 2>/dev/null | grep -q TEXTREL; then
      status=fail; why="$why the executable has text relocations (readelf -d $d/l2r);"
    fi
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
