#!/usr/bin/env bash
# Unit tests of the leanrt crate (bignums, tagged arrays, hashes), built with
# the pinned rustc against Reussir's runtime, GMP and the shared crate
# lean-runtime (third_party/lean-runtime, built and cached by scripts/l2r.py
# as for programs).
#   tests/runtime/leanrt-unit.sh [TEST FILTER]
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
OUT=${L2R_TEST_BUILD:-$HERE/build}/leanrt-unit
mkdir -p "$(dirname "$OUT")"
# lean-runtime as scripts/l2r.py builds it: rustc's arguments for it
# (--extern lean_runtime=..., -L dependency=...), one a line.
mapfile -t LR < <(env -u L2R_LEANRT_RUSTFLAGS L2R_REUSSIR="$REUSSIR" L2R_RUSTC="$RUSTC" \
  PYTHONDONTWRITEBYTECODE=1 python3 -c '
import sys; sys.path.insert(0, sys.argv[1]); import l2r
lr = l2r.build_lean_runtime(l2r.leanrt_out())
for e in lr.externs: print("--extern"); print(e)
for d in lr.dirs: print("-L"); print(f"dependency={d}")' "$ROOT/scripts")
[ ${#LR[@]} -ge 4 ] || exit 1
"$RUSTC" --edition 2021 --test --crate-name leanrt -C opt-level=1 -L "$RT" -L "$RT/deps" \
  "${LR[@]}" -C link-arg="$GMP" "$ROOT/runtime/leanrt/src/lib.rs" -o "$OUT"
"$OUT" "$@"
