#!/usr/bin/env bash
# Unit tests of the leanrt crate (bignums, arrays, hashes), built with
# the pinned rustc against Reussir's runtime, GMP and the shared crate
# lean-runtime (third_party/lean-runtime, built and cached by scripts/l2r.py
# as for programs).
#   tests/runtime/leanrt-unit.sh [TEST FILTER]
# The crate serves both representations of `Nat` and `Int`, so the tests
# run once for each: as `--int-backend leanrt` builds it (leanrt's own big
# numbers), and as `--int-backend rcgmp` builds it (`--cfg leanrt_rcgmp`,
# linked with the Reussir checkout's rcgmp runtime: `leanrt::rcgmp`'s
# tests run too). L2R_INT_BACKEND=leanrt or rcgmp runs only that one;
# unset or empty, both (rcgmp is the default representation since
# 2026-10-25; before, an unset L2R_INT_BACKEND ran the leanrt build only).
# Environment: L2R_REUSSIR, L2R_RUSTC, L2R_GMP, L2R_LEAN_TOOLCHAIN,
# L2R_LEAN_RUNTIME, L2R_LEAN_RUNTIME_FEATURES (see scripts/l2r.py; GMP
# defaults to the toolchain's). L2R_LEANRT_RUSTFLAGS does not apply: both
# crates are built without it (a flag such as -C panic=abort must agree
# between them, and the test harness needs unwinding).
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
REUSSIR=${L2R_REUSSIR:-$ROOT/reussir}
RUSTC=${L2R_RUSTC:-$HOME/.rustup/toolchains/nightly-2026-08-31-aarch64-unknown-linux-gnu/bin/rustc}
RT=$REUSSIR/build/target-rt/release
GMP=${L2R_GMP:-$L2R_LEAN_TOOLCHAIN/lib/libgmp.a}
case "${L2R_INT_BACKEND:-}" in
  "") BACKENDS=(leanrt rcgmp) ;;
  leanrt|rcgmp) BACKENDS=("$L2R_INT_BACKEND") ;;
  *) echo "leanrt-unit: L2R_INT_BACKEND=$L2R_INT_BACKEND: expected leanrt or rcgmp" >&2; exit 2 ;;
esac
mkdir -p "${L2R_TEST_BUILD:-$HERE/build}"
status=0
for be in "${BACKENDS[@]}"; do
  OUT=${L2R_TEST_BUILD:-$HERE/build}/leanrt-unit-$be
  # lean-runtime as scripts/l2r.py builds it for this representation:
  # rustc's arguments for it (--extern lean_runtime=..., -L
  # dependency=...), one a line.
  mapfile -t LR < <(env -u L2R_LEANRT_RUSTFLAGS L2R_INT_BACKEND="$be" L2R_REUSSIR="$REUSSIR" L2R_RUSTC="$RUSTC" \
    PYTHONDONTWRITEBYTECODE=1 python3 -c '
import sys; sys.path.insert(0, sys.argv[1]); import l2r
lr = l2r.build_lean_runtime(l2r.leanrt_out())
for e in lr.externs: print("--extern"); print(e)
for d in lr.dirs: print("-L"); print(f"dependency={d}")' "$ROOT/scripts")
  [ ${#LR[@]} -ge 4 ] || exit 1
  # Debug assertions on (rustc turns them on by itself only at opt-level 0):
  # leanrt's invariant checks run, e.g. that no big `Int` is in the small
  # range (nat::tests::unnormalized_big_int_is_caught).
  # rcgmp: leanrt as `--int-backend rcgmp` builds it (`--cfg leanrt_rcgmp`),
  # linked with the Reussir checkout's rcgmp runtime (built with Reussir:
  # its build directory's `rcgmp-runtime.a`).
  RCGMP=()
  if [ "$be" = rcgmp ]; then
    # The newest one: cargo keeps a build-script output directory per configuration.
    A=$(ls -t "$REUSSIR"/build/target/release/build/rene-*/out/rcgmp-runtime.a 2>/dev/null | head -1)
    [ -n "$A" ] || { echo "leanrt-unit: no rcgmp-runtime.a in $REUSSIR/build (a Reussir built with rcgmp)" >&2; exit 2; }
    RCGMP=(--cfg leanrt_rcgmp -C link-arg="$A")
  fi
  echo "leanrt-unit: --int-backend $be"
  "$RUSTC" --edition 2021 --test --crate-name leanrt -C opt-level=1 -C debug-assertions=on -L "$RT" -L "$RT/deps" \
    "${LR[@]}" ${RCGMP[@]+"${RCGMP[@]}"} -C link-arg="$GMP" "$ROOT/runtime/leanrt/src/lib.rs" -o "$OUT"
  "$OUT" "$@" || status=1
done
exit $status
