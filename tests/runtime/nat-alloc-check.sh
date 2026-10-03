#!/usr/bin/env bash
# Big numbers are freed exactly once: builds RtNatStress.lean through lean2rr
# with leanrt's big-number counters (L2R_LEANRT_RUSTFLAGS="--cfg
# leanrt_count_bigs", which print "made M freed F live L" at exit) and runs
# it at two sizes. The numbers still alive at exit (constants) must not grow
# with the size, `freed` must never exceed `made` (a double free), and both
# runs must print what the native build prints.
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
cp "$HERE/RtNatStress.lean" .
lean -o RtNatStress.olean RtNatStress.lean
lean RtNatStress.lean -c RtNatStress.c
leanc RtNatStress.c -o native -O3 2> /dev/null || leanc RtNatStress.c -o native
L2R_LEANRT_RUSTFLAGS="--cfg leanrt_count_bigs" python3 "$ROOT/scripts/l2r.py" RtNatStress \
  -o "$OUT/counted" --lean-path "$OUT" > build.log 2>&1 || { cat build.log; exit 1; }
status=0
declare -A live
for n in "$SMALL" "$LARGE"; do
  ./native "$n" > "native.$n.out"
  ./counted "$n" > "counted.$n.out" 2> "counted.$n.err"
  if ! cmp -s "native.$n.out" "counted.$n.out"; then
    echo "FAIL size $n: output differs from native"; status=1
  fi
  line=$(grep '^leanrt: big numbers' "counted.$n.err" || true)
  read -r made freed l <<< "$(echo "$line" | sed -E 's/.*made ([0-9]+) freed ([0-9]+) live (-?[0-9]+).*/\1 \2 \3/')"
  echo "size $n: made $made freed $freed live $l"
  if [ -z "$line" ] || [ "$freed" -gt "$made" ]; then echo "FAIL size $n: freed more than made"; status=1; fi
  live[$n]=$l
done
if [ "${live[$SMALL]}" != "${live[$LARGE]}" ]; then
  echo "FAIL: live big numbers at exit grow with the size (${live[$SMALL]} -> ${live[$LARGE]})"; status=1
fi
[ $status -eq 0 ] && echo "PASS  nat-alloc-check"
exit $status
