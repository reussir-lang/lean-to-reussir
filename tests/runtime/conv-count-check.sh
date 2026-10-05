#!/usr/bin/env bash
# Updates of a container whose element type depends on a value convert no
# container per update: builds RtUniformUpdates.lean, RtUniformUpdatesJp.lean,
# RtUniformUpdatesMixed.lean and RtUniformUpdatesNested.lean through lean2rr
# with the conversion counter (L2R_COUNT_CONVERSIONS=1: every generated
# conversion counts the elements it rebuilds, array elements and constructor
# cells, and the program prints "leanrt: conversions N" to stderr at exit) and
# runs each at two sizes, LARGE = 4 x SMALL.
# - The elements converted must grow at most linearly with the size (at most
#   5x for 4x the size; a whole-container round trip per update, RV9C-02,
#   C02R-01 and C02R-02, makes them grow about 16x).
# - Both runs must print what the native build prints.
# It also builds RtConvProbeRollback.lean with the counter and runs it once:
# its casts' conversions, and the counter's function, are emitted inside
# cast probes (the first one was undone until review CLR-01, and the counter
# then had to be emitted again by the kept one: review R9S2R-04); the run
# must print what native prints and count some conversions.
#   tests/runtime/conv-count-check.sh [SMALL]   (default 300)
# Environment: as run.sh (L2R_REUSSIR, L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN).
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
SMALL=${1:-300}
LARGE=$((SMALL * 4))
OUT=${L2R_TEST_BUILD:-$HERE/build}/conv-count-check
mkdir -p "$OUT"
cd "$OUT"
status=0

# count T N: run the native and counted builds of T at size N, compare, set CONV.
count() {
  local t=$1 n=$2
  ./"$t-native" "$n" > "$t.native.$n.out"
  ./"$t-counted" "$n" > "$t.counted.$n.out" 2> "$t.counted.$n.err"
  if ! cmp -s "$t.native.$n.out" "$t.counted.$n.out"; then
    echo "FAIL $t size $n: output differs from native"; status=1
  fi
  CONV=$(sed -nE 's/^leanrt: conversions ([0-9]+)$/\1/p' "$t.counted.$n.err")
  [ -n "$CONV" ] || CONV=0
  echo "$t size $n: elements converted $CONV"
}

for t in RtUniformUpdates RtUniformUpdatesJp RtUniformUpdatesMixed RtUniformUpdatesNested; do
  cp "$HERE/$t.lean" .
  lean -o "$t.olean" "$t.lean"
  lean "$t.lean" -c "$t.c"
  leanc "$t.c" -o "$t-native" -O3 2> /dev/null || leanc "$t.c" -o "$t-native"
  L2R_COUNT_CONVERSIONS=1 python3 "$ROOT/scripts/l2r.py" "$t" \
    -o "$OUT/$t-counted" --lean-path "$OUT" > "$t.build.log" 2>&1 || { cat "$t.build.log"; exit 1; }
  count "$t" "$SMALL"; c1=$CONV
  count "$t" "$LARGE"; c2=$CONV
  if [ "$c2" -gt $((c1 * 5 + 100)) ]; then
    echo "FAIL $t: elements converted grow faster than the size ($c1 -> $c2 for 4x): a container is converted at each update"
    status=1
  fi
done
t=RtConvProbeRollback
cp "$HERE/$t.lean" .
lean -o "$t.olean" "$t.lean"
lean "$t.lean" -c "$t.c"
leanc "$t.c" -o "$t-native" -O3 2> /dev/null || leanc "$t.c" -o "$t-native"
L2R_COUNT_CONVERSIONS=1 python3 "$ROOT/scripts/l2r.py" "$t" \
  -o "$OUT/$t-counted" --lean-path "$OUT" > "$t.build.log" 2>&1 || { cat "$t.build.log"; exit 1; }
count "$t" "$SMALL"
if [ "$CONV" -eq 0 ]; then
  echo "FAIL $t: no conversion counted"; status=1
fi
[ $status -eq 0 ] && echo "PASS  conv-count-check"
exit $status
