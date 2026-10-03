#!/usr/bin/env bash
# Big numbers are freed exactly once, and big constants are made once:
# builds RtNatStress.lean and RtNatConst.lean through lean2rr with leanrt's
# big-number counters (L2R_LEANRT_RUSTFLAGS="--cfg leanrt_count_bigs", which
# print "made M freed F live L" at exit) and runs each at two sizes.
# - RtNatStress: the numbers still alive at exit (constants) must not grow
#   with the size, and `freed` must never exceed `made` (a double free).
# - RtNatConst: `made` must not grow with the size (a big constant used in a
#   loop is made once, not at every use).
# Both must print what the native build prints.
#   tests/runtime/nat-alloc-check.sh [SMALL LARGE]   (default 300 3000)
# Environment: as run.sh (L2R_REUSSIR, L2R_LEAN2RR, L2R_TEST_BUILD).
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
SMALL=${1:-300}
LARGE=${2:-3000}
OUT=${L2R_TEST_BUILD:-$HERE/build}/nat-alloc-check
mkdir -p "$OUT"
cd "$OUT"
status=0

# counts PROG N: run the native and counted builds at size N, compare, and
# set MADE FREED LIVE.
counts() {
  local t=$1 n=$2
  ./"$t-native" "$n" > "$t.native.$n.out"
  ./"$t-counted" "$n" > "$t.counted.$n.out" 2> "$t.counted.$n.err"
  if ! cmp -s "$t.native.$n.out" "$t.counted.$n.out"; then
    echo "FAIL $t size $n: output differs from native"; status=1
  fi
  local line
  line=$(grep '^leanrt: big numbers' "$t.counted.$n.err" || true)
  if [ -z "$line" ]; then echo "FAIL $t size $n: no counts"; status=1; MADE=0; FREED=0; LIVE=0; return; fi
  read -r MADE FREED LIVE <<< "$(echo "$line" | sed -E 's/.*made ([0-9]+) freed ([0-9]+) live (-?[0-9]+).*/\1 \2 \3/')"
  echo "$t size $n: made $MADE freed $FREED live $LIVE"
  if [ "$FREED" -gt "$MADE" ]; then echo "FAIL $t size $n: freed more than made"; status=1; fi
}

for t in RtNatStress RtNatConst; do
  cp "$HERE/$t.lean" .
  lean -o "$t.olean" "$t.lean"
  lean "$t.lean" -c "$t.c"
  leanc "$t.c" -o "$t-native" -O3 2> /dev/null || leanc "$t.c" -o "$t-native"
  L2R_LEANRT_RUSTFLAGS="--cfg leanrt_count_bigs" python3 "$ROOT/scripts/l2r.py" "$t" \
    -o "$OUT/$t-counted" --lean-path "$OUT" > "$t.build.log" 2>&1 || { cat "$t.build.log"; exit 1; }
  counts "$t" "$SMALL"; m1=$MADE; l1=$LIVE
  counts "$t" "$LARGE"; m2=$MADE; l2=$LIVE
  if [ "$l1" != "$l2" ]; then
    echo "FAIL $t: live big numbers at exit grow with the size ($l1 -> $l2)"; status=1
  fi
  if [ "$t" = RtNatConst ] && [ "$m1" != "$m2" ]; then
    echo "FAIL $t: big numbers made grow with the size ($m1 -> $m2): a big constant is rebuilt at its uses"; status=1
  fi
done
[ $status -eq 0 ] && echo "PASS  nat-alloc-check"
exit $status
