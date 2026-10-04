#!/usr/bin/env bash
# L2R_ALLOW_MISSING_EXTERNS=1 turns lean2rr's refusal of an extern it cannot
# serve into a warning and generates the program anyway; the program must
# then not build, and must not call the runtime's function of a refused
# extern of the program (review REB-11). Builds tests/runtime/AllowMissing.lean
# (refused externs used directly, partially applied, as a closure, through
# an instance and through the `ptrAddrUnsafe` shortcut) with
# scripts/l2r.py --keep-rr and checks:
# - lean2rr warns and generates the .rr; rrc fails with an unknown function
#   `l2r_refused_…`;
# - the generated part of the .rr (after the prelude) calls
#   `l2r_refused_l_myGcd` and `l2r_refused_l_myAddr`, and neither the
#   runtime's `lean_nat_gcd` nor its address functions (`l2r_ptr_addr_*`).
#   tests/runtime/allow-missing-check.sh
# Environment: as run.sh (L2R_REUSSIR, L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
OUT=${L2R_TEST_BUILD:-$HERE/build}/allow-missing-check
rm -rf "$OUT"; mkdir -p "$OUT"
cd "$OUT" || exit 1
cp "$HERE/AllowMissing.lean" .
status=0
fail() { echo "FAIL allow-missing: $1"; status=1; }
lean -o AllowMissing.olean AllowMissing.lean > lean.log 2>&1 || { echo "FAIL allow-missing: lean (see $OUT/lean.log)"; exit 1; }
if L2R_ALLOW_MISSING_EXTERNS=1 LEAN_ABORT_ON_PANIC=1 python3 "$ROOT/scripts/l2r.py" AllowMissing --lean-path "$OUT" \
    -o "$OUT/l2r" --keep-rr "$OUT/AllowMissing.rr" > build.log 2>&1; then
  fail "the program built (see $OUT/build.log)"
fi
grep -q "lean2rr: warning: .*have no Lean definition that lean2rr can use" build.log \
  || fail "no warning of the refused externs (see $OUT/build.log)"
grep -q 'unknown function `l2r_refused_' build.log \
  || fail "rrc did not fail on an l2r_refused_ function (see $OUT/build.log)"
if [ -f AllowMissing.rr ]; then
  # The generated part: everything after the prelude.
  sed -n '/^\/\/ ---- generated types ----$/,$p' AllowMissing.rr > generated.rr
  [ -s generated.rr ] || fail "no generated part in AllowMissing.rr"
  for f in l2r_refused_l_myGcd l2r_refused_l_myAddr; do
    grep -q "$f(" generated.rr || fail "no call of $f in the generated code"
  done
  for f in 'lean_nat_gcd(' 'l2r_ptr_addr_'; do
    if grep -qF "$f" generated.rr; then fail "the generated code calls $f (see $OUT/generated.rr)"; fi
  done
else
  fail "no AllowMissing.rr (see $OUT/build.log)"
fi
[ $status = 0 ] && echo "PASS  allow-missing"
exit $status
