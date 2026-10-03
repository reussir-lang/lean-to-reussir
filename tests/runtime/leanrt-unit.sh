#!/usr/bin/env bash
# Unit tests of the leanrt crate (bignums, tagged arrays, hashes), built with
# the pinned rustc against Reussir's runtime and GMP.
#   tests/runtime/leanrt-unit.sh [TEST FILTER]
# Environment: L2R_REUSSIR, L2R_RUSTC, L2R_GMP, L2R_LEAN_TOOLCHAIN (see
# scripts/l2r.py; GMP defaults to the toolchain's).
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
"$RUSTC" --edition 2021 --test --crate-name leanrt -C opt-level=1 -L "$RT" -L "$RT/deps" \
  -C link-arg="$GMP" "$ROOT/runtime/leanrt/src/lib.rs" -o "$OUT"
"$OUT" "$@"
