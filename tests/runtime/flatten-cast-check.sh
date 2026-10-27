#!/usr/bin/env bash
# In a program that casts and makes resources, flatten-structs splits a
# parameter that is a structure of callbacks when Lean owns it natively and
# the declaration reads its fields at its start (Opt/Flatten.lean,
# `castParamFree`), so conv-liveness does not reach the callbacks that only
# `initialize` blocks store. Translation only (`lean2rr --emit rr`, no
# Reussir build), on tests/runtime/RtFlattenCastCallbacks, whose output
# run.sh checks: the generated code has the workers of `register`, `g1t`,
# `g1o` and `g3` (`l_register___l2r_0____l2r__flat`, …), whose handles
# run.sh's output shows through the split, and no function of the stored
# callbacks (`l_storedNat`, `l_storedStr`, `l_storedList`). With every
# declaration with such a parameter left whole (dev 385cbdd3 to 1d71d2a1),
# the three callbacks were generated (463 functions instead of 439), and a
# program importing `Cslib.Init` with a one-line `main` had 198,768 live
# functions instead of 18,138.
#   tests/runtime/flatten-cast-check.sh
# Environment: as determinism-check.sh (L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
LEAN2RR=${L2R_LEAN2RR:-$ROOT/lean2rr/.lake/build/bin/lean2rr}
BASE=${L2R_TEST_BUILD:-$HERE/build}/flatten-cast-check
rm -rf "$BASE"
P=RtFlattenCastCallbacks
OUT=$BASE/$P
mkdir -p "$OUT"
cp "$HERE/$P.lean" "$OUT/"
status=0
fail() { echo "FAIL $P: $*"; status=1; }
if ! (cd "$OUT" && lean -o "$P.olean" "$P.lean") > "$OUT/lean.log" 2>&1; then
  fail "lean failed (see $OUT/lean.log)"
elif ! (cd "$OUT" && LEAN_PATH="$OUT" L2R_SHIM_DIR="$ROOT/lean2rr/.lake/build/lib/lean" LEAN_STACK_SIZE_KB=1048576 \
        "$LEAN2RR" "$P" --emit rr --prelude "$ROOT/runtime/prelude.rr" -o "$OUT/on.rr") > "$OUT/on.rr.log" 2>&1; then
  fail "did not translate (see $OUT/on.rr.log)"
else
  # The structures run.sh's output checks through a split (g1t, g1o, g3:
  # handles held through a thunk or a callback).
  for f in register g1t g1o g3; do
    if grep -qE "^(#\[[a-z_]+\] *)?fn l_${f}___l2r_0____l2r__flat\(" "$OUT/on.rr"; then
      echo "ok   $f split (its worker is generated)"
    else
      fail "no worker of $f: flatten-structs left it whole"
    fi
  done
  for f in storedNat storedStr storedList; do
    if grep -qE "^(#\[[a-z_]+\] *)?fn l_${f}___" "$OUT/on.rr"; then
      fail "$f is generated: conv-liveness reached a callback that only an initialize block stores"
    else
      echo "ok   $f not generated"
    fi
  done
fi
[ $status -eq 0 ] && echo "PASS  flatten-cast-check"
exit $status
