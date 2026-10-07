#!/usr/bin/env bash
# lean4-raytracer (github.com/kmill/lean4-raytracer; NOTICE lists our
# changes): build the program natively with Lake and through lean2rr +
# Reussir (scripts/l2r.py), run both with the same arguments, and compare
# stdout, stderr, the exit code and the image file (PPM) byte for byte.
# No timing.
#
#   tests/apps/raytracer/run.sh [CONFIG...]      (default: small0 small1)
#
# CONFIG    arguments of `render FILE WIDTH SAMPLES THREADS DEPTH`
#   small0  out.ppm 60 2 0 10    60x40 pixels, 2 samples per pixel,
#                                depth 10, rendered on the main thread
#   small1  out.ppm 60 2 1 10    the same, rendered in one task
#   bench0  out.ppm 200 4 0 30   200x133 pixels, 4 samples per pixel,
#                                depth 30, main thread (about 10 s natively)
# Only THREADS = 0 and THREADS = 1 give one image: all tasks take random
# numbers from IO.stdGenRef, so with two or more tasks the image depends on
# the order in which the threads run.
#
# The package is copied into the build directory and built there, so the
# source tree stays clean. lean2rr translates the module Main from the
# package's .olean files. Both executables run with LEAN_BACKTRACE=0;
# lean2rr runs with LEAN_ABORT_ON_PANIC=1 (a panic of lean2rr fails the
# build, as in tests/runtime/run.sh).
# Environment: L2R_REUSSIR, L2R_LEAN2RR, L2R_RUSTC, L2R_LEAN_RUNTIME,
# L2R_LEAN_RUNTIME_FEATURES, L2R_DISABLE_OPTS / L2R_ENABLE_OPTS (see
# scripts/l2r.py); L2R_TEST_BUILD (build directory, default
# tests/apps/build/raytracer); L2R_APP_TIMEOUT (seconds per run, default
# 900); L2R_LEAN_TOOLCHAIN (the toolchain of the native build, default the
# one lean2rr/lean-toolchain pins; scripts/toolchain.sh).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
BUILD=${L2R_TEST_BUILD:-$ROOT/tests/apps/build/raytracer}
TIMEOUT=${L2R_APP_TIMEOUT:-900}

declare -A CONFIGS=(
  [small0]="out.ppm 60 2 0 10"
  [small1]="out.ppm 60 2 1 10"
  [bench0]="out.ppm 200 4 0 30"
)
if [ $# -gt 0 ]; then NAMES=("$@"); else NAMES=(small0 small1); fi
for n in "${NAMES[@]}"; do
  if [ -z "${CONFIGS[$n]+x}" ]; then
    echo "unknown CONFIG $n (known: small0 small1 bench0)" >&2
    exit 2
  fi
done
LR=${L2R_LEAN_RUNTIME:-$ROOT/third_party/lean-runtime}
if [ ! -f "$LR/Cargo.toml" ]; then
  echo "no lean-runtime at $LR: run \`git submodule update --init third_party/lean-runtime\` (or set L2R_LEAN_RUNTIME)" >&2
  exit 2
fi

rm -rf "$BUILD"; mkdir -p "$BUILD/src"
cp -a "$HERE/Main.lean" "$HERE/Render" "$HERE/lakefile.lean" "$HERE/lake-manifest.json" \
  "$HERE/lean-toolchain" "$BUILD/src/"
if ! (cd "$BUILD/src" && lake build) > "$BUILD/build-native.log" 2>&1; then
  echo "FAIL  native build failed (see $BUILD/build-native.log)"
  exit 1
fi
NATIVE=$BUILD/src/.lake/build/bin/render
if ! (cd "$BUILD" && LEAN_ABORT_ON_PANIC=1 python3 "$ROOT/scripts/l2r.py" Main -o "$BUILD/l2r" \
      --lean-path "$BUILD/src/.lake/build/lib/lean" --keep-rr "$BUILD/Main.rr") \
      > "$BUILD/build-l2r.log" 2>&1; then
  echo "FAIL  lean2rr build failed (see $BUILD/build-l2r.log)"
  exit 1
fi

pass=0; fail=0; failed=()
for n in "${NAMES[@]}"; do
  d=$BUILD/$n
  for k in native l2r; do
    bin=$NATIVE; [ $k = l2r ] && bin=$BUILD/l2r
    mkdir -p "$d/$k"
    (
      cd "$d/$k" || exit
      # shellcheck disable=SC2086
      LEAN_BACKTRACE=0 timeout -s KILL "$TIMEOUT" "$bin" ${CONFIGS[$n]} < /dev/null > stdout 2> stderr
      echo $? > code
    )
  done
  why=""
  [ "$(cat "$d/native/code")" = 0 ] || why=" native exit $(cat "$d/native/code");"
  for f in stdout stderr code out.ppm; do
    if [ ! -f "$d/native/$f" ]; then
      why="$why native wrote no $f;"
    elif ! cmp -s "$d/native/$f" "$d/l2r/$f"; then
      why="$why $f differs (cmp $d/native/$f $d/l2r/$f);"
    fi
  done
  if [ -z "$why" ]; then
    pass=$((pass + 1))
    echo "PASS  $n (${CONFIGS[$n]}): image $(wc -c < "$d/native/out.ppm") bytes"
  else
    fail=$((fail + 1)); failed+=("$n")
    echo "FAIL  $n (${CONFIGS[$n]}):$why"
  fi
done
echo "passed $pass, failed $fail${failed[*]:+ (${failed[*]})}"
[ $fail -eq 0 ]
