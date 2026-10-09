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
#   NAME.enable-opts  lean2rr optimizations to turn on for this test (one
#               line, comma-separated, added to L2R_ENABLE_OPTS): an
#               optimization that is off by default (`unread-fields`); a
#               name in NAME.opts is taken out of L2R_ENABLE_OPTS, so a test
#               keeps a pass off also in a run that turns it on for all
#   NAME.xfail  the test is known to fail through lean2rr; the file says why
#               (a "Requests for lean2rr" item in runtime/README.md); a
#               file whose first line starts with `alloc-check:` marks only
#               tests/runtime/alloc-check.sh's check of the test (its
#               allocations) as known to fail: this script ignores it
#   NAME.l2r.out, NAME.l2r.err, NAME.l2r.code
#               a documented, intended difference from native (a Lean
#               runtime bug lean2rr does not reproduce, plan §10 "Runtime:
#               Lean bugs we do not reproduce", or another item of plan
#               §10): that stream of lean2rr's run
#               is compared with this file, and the same stream of native's
#               run with NAME.native.out/.err/.code, instead of with each
#               other; the two files of a stream go together (one without
#               the other fails the test: unpaired expectation file)
#   NAME.deps   companion modules of the program, one name per line, each
#               tests/runtime/<name>.lean (not named Rt*, so not a test):
#               compiled in that order before NAME (the test's build
#               directory first on LEAN_PATH), linked into the native build,
#               found there by lean2rr; e.g. a module whose initializer must
#               run first
#   NAME.ffi.c  C code linked into the native build only: the C side of the
#               test's own `@[extern]` declarations (lean2rr never uses C
#               code other than Lean's runtime library: it compiles their
#               Lean definitions instead; translation plan §5.8)
#   NAME.refused  the lean2rr build must fail, its output containing each
#               line of this file, and not a line's text after `! `
#               (as NAME.l2r-log); natively only `lean -c` runs and must
#               succeed (the program is valid Lean; its C may need code
#               the test does not give to link); nothing runs, so files
#               describing a run (NAME.args, .stdin, .pipe, .ffi.c,
#               .l2r-log, .l2r-debug, NAME.native.*, NAME.l2r.*) are an
#               error with it
#   NAME.l2r-log  lean2rr's build output must contain each line of this
#               file, and must not contain a line's text after `! ` (e.g.
#               which externs run their Lean definition, lean2rr's note)
#   NAME.l2r-debug  as NAME.l2r-log, with lean2rr run under L2R_DEBUG=1,
#               which prints its whole-program facts (e.g. `lean2rr: program
#               casts: no`, the compact array kinds and why one is off)
#
# Both executables run with LEAN_BACKTRACE=0, so panics print no stack trace.
# lean2rr runs with LEAN_ABORT_ON_PANIC=1: a panic of lean2rr itself is a
# lean2rr bug (it goes on with a default value), so it fails the build. Its
# stderr is not searched instead: a panic message has no fixed prefix (the
# panic under `Name.append` prints `Error: unreachable @ extractMainModule`;
# round 9 RV9S-01, test RtHygSpecName).
# Environment: L2R_REUSSIR, L2R_LEAN2RR, L2R_RUSTC, L2R_LEAN_RUNTIME,
# L2R_LEAN_RUNTIME_FEATURES (see scripts/l2r.py);
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
# Every lean2rr build needs lean-runtime: say so once instead of failing each test.
LR=${L2R_LEAN_RUNTIME:-$ROOT/third_party/lean-runtime}
if [ ! -f "$LR/Cargo.toml" ]; then
  echo "no lean-runtime at $LR: run \`git submodule update --init third_party/lean-runtime\` (or set L2R_LEAN_RUNTIME)" >&2
  exit 2
fi

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
  enable=${L2R_ENABLE_OPTS:-}
  [ -f "$HERE/$t.enable-opts" ] && enable="$enable${enable:+,}$(tr -d ' \n' < "$HERE/$t.enable-opts")"
  if [ -f "$HERE/$t.opts" ]; then
    for o in $(tr ', \n' '   ' < "$HERE/$t.opts"); do
      prev=
      while [ "$prev" != "$enable" ]; do
        prev=$enable
        enable=$(echo ",$enable," | sed "s/,$o,/,/g; s/^,*//; s/,*$//")
      done
    done
  fi
  ffi=(); [ -f "$HERE/$t.ffi.c" ] && ffi=("$HERE/$t.ffi.c")
  # (`env` sets it for the lean2rr build only: lean2rr tests whether it is set.)
  debug=(); [ -f "$HERE/$t.l2r-debug" ] && debug=(env L2R_DEBUG=1)
  deps=(); [ -f "$HERE/$t.deps" ] && read -r -d '' -a deps < "$HERE/$t.deps"
  for m in ${deps[@]+"${deps[@]}"}; do cp "$HERE/$m.lean" "$d/"; ffi+=("$m.c"); done
  status=ok; why=""
  # A translation lean2rr must refuse is only compiled by Lean, not linked.
  link=1; [ -f "$HERE/$t.refused" ] && link=""
  if ! (cd "$d" && { [ ${#deps[@]} -eq 0 ] || export LEAN_PATH=$d${LEAN_PATH:+:$LEAN_PATH}; } \
        && for m in ${deps[@]+"${deps[@]}"}; do lean -o "$m.olean" -c "$m.c" "$m.lean" >> build-native.log 2>&1 || exit 1; done \
        && lean -o "$t.olean" -c "$t.c" "$t.lean" >> build-native.log 2>&1 \
        && { [ -z "$link" ] || leanc -O3 -DNDEBUG "$t.c" ${ffi[@]+"${ffi[@]}"} -o native >> build-native.log 2>&1; }); then
    status=fail; why="native build failed (see $d/build-native.log)"
  elif [ -f "$HERE/$t.refused" ] && runfiles=$(cd "$HERE" && ls -d "$t".args "$t".stdin "$t".pipe "$t".ffi.c \
          "$t".l2r-log "$t".l2r-debug "$t".native.* "$t".l2r.* 2> /dev/null || true) && [ -n "$runfiles" ]; then
    status=fail; why="$t.refused expects lean2rr to refuse, but these files describe a run: $(echo $runfiles)"
  elif [ -f "$HERE/$t.refused" ]; then
    # A translation lean2rr refuses, with the expected message.
    if L2R_DISABLE_OPTS=$opts L2R_ENABLE_OPTS=$enable LEAN_ABORT_ON_PANIC=1 python3 "$ROOT/scripts/l2r.py" "$t" --lean-path "$d" -o "$d/l2r" > "$d/build-l2r.log" 2>&1; then
      status=fail; why="lean2rr built it, expected an error"
    else
      while IFS= read -r line; do
        [ -z "$line" ] && continue
        case $line in
          "! "*) if grep -qF -- "${line#! }" "$d/build-l2r.log"; then
                   status=fail; why="$why '${line#! }' in $d/build-l2r.log;"; fi ;;
          *) grep -qF -- "$line" "$d/build-l2r.log" || { status=fail; why="$why no '$line' in $d/build-l2r.log;"; } ;;
        esac
      done < "$HERE/$t.refused"
    fi
  elif ! L2R_DISABLE_OPTS=$opts L2R_ENABLE_OPTS=$enable LEAN_ABORT_ON_PANIC=1 \
        ${debug[@]+"${debug[@]}"} python3 "$ROOT/scripts/l2r.py" "$t" --lean-path "$d" -o "$d/l2r" --keep-rr "$d/$t.rr" \
        > "$d/build-l2r.log" 2>&1; then
    status=fail; why="lean2rr build failed (see $d/build-l2r.log)"
  else
    for f in "$HERE/$t.l2r-log" "$HERE/$t.l2r-debug"; do
      [ -f "$f" ] || continue
      while IFS= read -r line; do
        [ -z "$line" ] && continue
        case $line in
          "! "*) if grep -qF -- "${line#! }" "$d/build-l2r.log"; then
                   status=fail; why="$why '${line#! }' in $d/build-l2r.log;"; fi ;;
          *) grep -qF -- "$line" "$d/build-l2r.log" || { status=fail; why="$why no '$line' in $d/build-l2r.log;"; } ;;
        esac
      done < "$f"
    done
    run_one ./native native
    run_one ./l2r l2r
    for k in out err code; do
      el=0; en=0
      [ -f "$HERE/$t.l2r.$k" ] && el=1
      [ -f "$HERE/$t.native.$k" ] && en=1
      if [ $el != $en ]; then
        # One side's expectation without the other's: a mistake in the test.
        status=fail; why="$why unpaired expectation file ($t.l2r.$k and $t.native.$k go together);"
      elif [ $el = 1 ]; then
        # An intended difference: each side against its own expectation.
        if ! cmp -s "$HERE/$t.native.$k" "$d/native.$k"; then
          status=fail; why="$why native $k differs from $t.native.$k (diff $HERE/$t.native.$k $d/native.$k);"
        fi
        if ! cmp -s "$HERE/$t.l2r.$k" "$d/l2r.$k"; then
          status=fail; why="$why $k differs from $t.l2r.$k (diff $HERE/$t.l2r.$k $d/l2r.$k);"
        fi
      elif ! cmp -s "$d/native.$k" "$d/l2r.$k"; then
        status=fail; why="$why $k differs (diff $d/native.$k $d/l2r.$k);"
      fi
    done
    # Like native Lean's, the executable is a PIE without text relocations
    # (Reussir bug 34: rrc compiled static code into a PIE).
    if readelf -d "$d/l2r" 2>/dev/null | grep -q TEXTREL; then
      status=fail; why="$why the executable has text relocations (readelf -d $d/l2r);"
    fi
  fi
  if [ -f "$HERE/$t.xfail" ] && ! head -1 "$HERE/$t.xfail" | grep -q '^alloc-check:'; then
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
