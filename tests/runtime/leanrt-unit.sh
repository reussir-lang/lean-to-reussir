#!/usr/bin/env bash
# Unit tests of the leanrt crate (boxes, arrays, strings, the drop stack),
# built with the pinned rustc against Reussir's runtime, its rcgmp runtime,
# GMP and the shared crate lean-runtime (third_party/lean-runtime, built and
# cached by scripts/l2r.py as for programs).
#   tests/runtime/leanrt-unit.sh [TEST FILTER]
# The crate is built as scripts/l2r.py builds it, linked with the Reussir
# checkout's rcgmp runtime, so `leanrt::rcgmp`'s tests run too. (Until
# 2026-10-26 the tests also ran for the leanrt representation of `Nat` and
# `Int`, removed by clean-integration D8; L2R_INT_BACKEND=leanrt is
# refused.)
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
case "${L2R_INT_BACKEND:-rcgmp}" in
  rcgmp) ;;
  *) echo "leanrt-unit: L2R_INT_BACKEND=$L2R_INT_BACKEND: Nat and Int have one representation, rcgmp (leanrt was removed on 2026-10-26, D8)" >&2; exit 2 ;;
esac
mkdir -p "${L2R_TEST_BUILD:-$HERE/build}"
OUT=${L2R_TEST_BUILD:-$HERE/build}/leanrt-unit
# lean-runtime as scripts/l2r.py builds it: rustc's arguments for it
# (--extern lean_runtime=..., -L dependency=...), one a line.
mapfile -t LR < <(env -u L2R_LEANRT_RUSTFLAGS L2R_REUSSIR="$REUSSIR" L2R_RUSTC="$RUSTC" \
  PYTHONDONTWRITEBYTECODE=1 python3 -c '
import sys; sys.path.insert(0, sys.argv[1]); import l2r
lr = l2r.build_lean_runtime(l2r.leanrt_out())
for e in lr.externs: print("--extern"); print(e)
for d in lr.dirs: print("-L"); print(f"dependency={d}")' "$ROOT/scripts")
[ ${#LR[@]} -ge 4 ] || exit 1
# The Reussir checkout's rcgmp runtime (built with Reussir: its build
# directory's `rcgmp-runtime.a`; the newest one, as cargo keeps a
# build-script output directory per configuration).
A=$(ls -t "$REUSSIR"/build/target/release/build/rene-*/out/rcgmp-runtime.a 2>/dev/null | head -1)
[ -n "$A" ] || { echo "leanrt-unit: no rcgmp-runtime.a in $REUSSIR/build (a Reussir built with rcgmp)" >&2; exit 2; }
# Debug assertions on (rustc turns them on by itself only at opt-level 0):
# leanrt's invariant checks run.
"$RUSTC" --edition 2021 --test --crate-name leanrt -C opt-level=1 -C debug-assertions=on -L "$RT" -L "$RT/deps" \
  "${LR[@]}" -C link-arg="$A" -C link-arg="$GMP" "$ROOT/runtime/leanrt/src/lib.rs" -o "$OUT"
exec "$OUT" "$@"
