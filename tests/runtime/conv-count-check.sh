#!/usr/bin/env bash
# No value changes layout: a datatype, an array, a thunk or task and a
# reference have one representation each (rule 1 of the layouts of generic
# types), so the only conversion functions lean2rr generates are the
# casts between two different inductives (`structConv`, `l2r_conv_S_D`).
# - RtUniformUpdates.lean, RtUniformUpdatesJp.lean, RtUniformUpdatesMixed.lean,
#   RtUniformUpdatesNested.lean and RtUniformUpdatesShared.lean (updates of a
#   container whose element type depends on a value), RtConvUniform.lean
#   (trees, rose trees, mutual inductives and arrays through polymorphic
#   recursion), RtLazyRoundTrip.lean (thunks and tasks crossing between
#   typed and uniform code) and RtArrayMapRepr.lean (`Array.map` that
#   changes the element type) are translated only (`lean2rr --emit rr`):
#   the code of each must have no conversion function at all (no
#   `fn l2r_conv_`). Before rule 1 they converted whole containers (the
#   counts grew about 16x for 4x the size: RV9C-02, C02R-01, C02R-02); with
#   rule 1 their runtime counts were zero, and a program without a
#   conversion function counts none (review of rule 1, simplicity finding
#   9: the runtime builds of these eight were a native and a lean2rr build
#   each, for a count that could only be zero). Their outputs are checked by
#   run.sh.
# - RtConvProbeRollback.lean casts through a `Box` between two different
#   inductives whose layouts differ (a `Nat` field read as an `Int`): such a
#   cast is the one conversion left. It is built through lean2rr with the
#   conversion counter (L2R_COUNT_CONVERSIONS=1: every generated conversion
#   counts the elements it rebuilds, and the program prints "leanrt:
#   conversions N" to stderr at exit); the run must print what the native
#   build prints, and count some conversions.
#   tests/runtime/conv-count-check.sh [SMALL]   (default 300: RtConvProbeRollback's argument)
# Environment: as run.sh (L2R_REUSSIR, L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN).
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
LEAN2RR=${L2R_LEAN2RR:-$ROOT/lean2rr/.lake/build/bin/lean2rr}
SMALL=${1:-300}
OUT=${L2R_TEST_BUILD:-$HERE/build}/conv-count-check
mkdir -p "$OUT"
cd "$OUT"
status=0

# The translation-only programs: no conversion function in their code.
for t in RtUniformUpdates RtUniformUpdatesJp RtUniformUpdatesMixed RtUniformUpdatesNested \
         RtUniformUpdatesShared RtConvUniform RtLazyRoundTrip RtArrayMapRepr; do
  cp "$HERE/$t.lean" .
  if ! { lean -o "$t.olean" "$t.lean" &&
         LEAN_PATH="$OUT" L2R_SHIM_DIR="$ROOT/lean2rr/.lake/build/lib/lean" LEAN_STACK_SIZE_KB=1048576 \
           "$LEAN2RR" "$t" --root main --emit rr --prelude "$ROOT/runtime/prelude.rr" -o "$OUT/$t.rr"; } \
       > "$t.translate.log" 2>&1; then
    echo "FAIL $t: translation failed (see $OUT/$t.translate.log)"; status=1; continue
  fi
  n=$(grep -c '^fn l2r_conv_' "$t.rr" || true)
  echo "$t: conversion functions $n"
  if [ "$n" -ne 0 ]; then
    echo "FAIL $t: $n conversion functions (a value changes layout): $(grep -o '^fn l2r_conv_[A-Za-z0-9_]*' "$t.rr" | head -3 | tr '\n' ' ')"; status=1
  fi
done

# The cast: its conversions run and are counted.
t=RtConvProbeRollback
cp "$HERE/$t.lean" .
lean -o "$t.olean" "$t.lean"
lean "$t.lean" -c "$t.c"
leanc "$t.c" -o "$t-native" -O3 2> /dev/null || leanc "$t.c" -o "$t-native"
L2R_COUNT_CONVERSIONS=1 python3 "$ROOT/scripts/l2r.py" "$t" \
  -o "$OUT/$t-counted" --lean-path "$OUT" > "$t.build.log" 2>&1 || { cat "$t.build.log"; exit 1; }
./"$t-native" "$SMALL" > "$t.native.out" 2> /dev/null || true
./"$t-counted" "$SMALL" > "$t.counted.out" 2> "$t.counted.err" || true
if ! cmp -s "$t.native.out" "$t.counted.out"; then
  echo "FAIL $t: output differs from native"; status=1
fi
CONV=$(sed -nE 's/^leanrt: conversions ([0-9]+)$/\1/p' "$t.counted.err")
[ -n "$CONV" ] || CONV=0
echo "$t: elements converted $CONV"
if [ "$CONV" -eq 0 ]; then
  echo "FAIL $t: no conversion counted"; status=1
fi
[ $status -eq 0 ] && echo "PASS  conv-count-check"
exit $status
