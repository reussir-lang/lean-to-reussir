#!/usr/bin/env bash
# The check of `--int-backend rcgmp` without `--rcgmp-type-args`
# (lean2rr's Emit/IntBackendCheck): Reussir passes a `Nat` or `Int` at a
# type argument of a generic FFI function as a raw handle and releases it
# after the call, so lean2rr keeps them out of those positions (a wrapper
# record, the boxes' own functions, no typed arrays of them), and the check
# stops lean2rr with an internal error if one is left. Translation only
# (`lean2rr --emit rr`, no Reussir build), on tests/runtime/RtNatGenericFfi
# (computed `Nat`/`Int` constants, `dbgTraceIfShared` at `Nat`, arrays of
# `Nat` and `Int`, references, thunks and tasks of `Nat`) and
# RtNatGenericBig (a big literal's closed term, a typed `Array Nat`; review
# R1-01 of step D: without the guard its sums were silently wrong):
# - with `--int-backend rcgmp` the translation succeeds, and its .rr has no
#   such type argument (no `<Nat>`/`<Int>` on the runtime's once-cell and
#   array functions, no `RVec<Nat>`);
# - with L2R_TEST_NAT_TYPE_ARGS=1 (the lowering keeps `Nat` at those type
#   arguments, as with `--rcgmp-type-args`, but the check stays on) it fails
#   with the check's internal error;
# - with `--rcgmp-type-args` too (Reussir's patch R2 assumed) it succeeds.
# Also `boxed-consts` under rcgmp, on tests/runtime/RtNatBoxedConsts (`Nat`
# and `Int` constants at the edges of the box's immediates, stored in
# lists): only the constants whose box is a cell (`2^63 : Nat`; `2^31`,
# `3000000000`, `2^32 - 1`, `2^62` and `-2^62 - 1 : Int`) get a once-cell
# `l2r_boxed_N`; the others are boxed in line (`constIsImmediate`; review of
# step D: `k5 : Nat := 5` had one). Under leanrt none has one (boxing a
# `Nat` or `Int` never allocates there).
#   tests/runtime/int-backend-check.sh
# Environment: as determinism-check.sh (L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
LEAN2RR=${L2R_LEAN2RR:-$ROOT/lean2rr/.lake/build/bin/lean2rr}
BASE=${L2R_TEST_BUILD:-$HERE/build}/int-backend-check
rm -rf "$BASE"
# translate OUT.rr [lean2rr flags...]
translate() {
  local o=$1; shift
  (cd "$OUT" && LEAN_PATH="$OUT" L2R_SHIM_DIR="$ROOT/lean2rr/.lake/build/lib/lean" LEAN_STACK_SIZE_KB=1048576 \
     "$LEAN2RR" "$P" --emit rr --prelude "$ROOT/runtime/prelude.rr" -o "$o" "$@") > "$o.log" 2>&1
}
status=0
for P in RtNatGenericFfi RtNatGenericBig; do
OUT=$BASE/$P
mkdir -p "$OUT"
cp "$HERE/$P.lean" "$OUT/"
(cd "$OUT" && lean -o "$P.olean" "$P.lean") > "$OUT/lean.log" 2>&1 \
  || { echo "FAIL $P: lean failed (see $OUT/lean.log)"; status=1; continue; }
if ! translate "$OUT/plain.rr" --int-backend rcgmp; then
  echo "FAIL $P: --int-backend rcgmp did not translate $P (see $OUT/plain.rr.log)"; status=1
elif grep -nE '(l2r_once_(get|put|set|take)|l2r_array_[a-z_]+|l2r_view_[a-z_]+|lean_dbg_trace_if_shared)<(Nat|Int)>|(RVec|LRef|LCell)<(Nat|Int)>' "$OUT/plain.rr" > "$OUT/plain.hits"; then
  echo "FAIL $P: --int-backend rcgmp left Nat/Int at a type argument (see $OUT/plain.hits)"; status=1
else
  echo "ok   $P --int-backend rcgmp: translated, no Nat or Int at the runtime's type arguments"
fi
if L2R_TEST_NAT_TYPE_ARGS=1 translate "$OUT/forced.rr" --int-backend rcgmp; then
  echo "FAIL $P: with L2R_TEST_NAT_TYPE_ARGS=1 lean2rr translated $P; the check should stop it"; status=1
elif ! grep -q "internal error: --int-backend rcgmp without --rcgmp-type-args" "$OUT/forced.rr.log"; then
  echo "FAIL $P: with L2R_TEST_NAT_TYPE_ARGS=1 lean2rr failed, but not with the check's error (see $OUT/forced.rr.log)"; status=1
else
  echo "ok   $P L2R_TEST_NAT_TYPE_ARGS=1: the check stops lean2rr ($(grep -c '^  ' "$OUT/forced.rr.log") uses shown)"
fi
if ! L2R_TEST_NAT_TYPE_ARGS=1 translate "$OUT/r2.rr" --int-backend rcgmp --rcgmp-type-args; then
  echo "FAIL $P: with --rcgmp-type-args lean2rr did not translate $P (see $OUT/r2.rr.log)"; status=1
else
  echo "ok   $P --rcgmp-type-args: translated (the check is off)"
fi
done
# The constants that `boxed-consts` boxes once (the constants read by the
# `l2r_boxed_N_init` functions of OUT.rr).
boxed() { grep -A3 '^fn l2r_boxed_[0-9]*_init' "$1" | grep -o 'l_k[A-Za-z0-9]*___l2r_0_' | LC_ALL=C sort | tr '\n' ' '; }
P=RtNatBoxedConsts
OUT=$BASE/$P
mkdir -p "$OUT"
cp "$HERE/$P.lean" "$OUT/"
if ! (cd "$OUT" && lean -o "$P.olean" "$P.lean") > "$OUT/lean.log" 2>&1; then
  echo "FAIL $P: lean failed (see $OUT/lean.log)"; status=1
else
  # Cells: the Nat 2^63; the Ints 2^31, 3000000000, 2^32 - 1 ([2^31, 2^32)),
  # 2^62 and -2^62 - 1. Immediates: the other Nats; the Ints -2^31 and
  # 2^31 - 1 (int32), 2^32, 2^62 - 1, -2^31 - 1, -3000000000 and -2^62
  # ([2^32, 2^62) and [-2^62, -2^31)).
  want="l_kB___l2r_0_ l_kBn___l2r_0_ l_kI31p___l2r_0_ l_kM___l2r_0_ l_kN64___l2r_0_ l_kU32___l2r_0_ "
  if ! translate "$OUT/rcgmp.rr" --int-backend rcgmp --rcgmp-type-args; then
    echo "FAIL $P: --int-backend rcgmp did not translate $P (see $OUT/rcgmp.rr.log)"; status=1
  elif [ "$(boxed "$OUT/rcgmp.rr")" != "$want" ]; then
    echo "FAIL $P --int-backend rcgmp: boxed once: $(boxed "$OUT/rcgmp.rr")(expected $want)"; status=1
  else
    echo "ok   $P --int-backend rcgmp: once-cells only for the constants whose box is a cell"
  fi
  if ! translate "$OUT/leanrt.rr" --int-backend leanrt; then
    echo "FAIL $P: --int-backend leanrt did not translate $P (see $OUT/leanrt.rr.log)"; status=1
  elif grep -q 'l2r_boxed_' "$OUT/leanrt.rr"; then
    echo "FAIL $P --int-backend leanrt: a boxed constant (expected none)"; status=1
  else
    echo "ok   $P --int-backend leanrt: no boxed constant"
  fi
fi
[ $status -eq 0 ] && echo "PASS  int-backend-check"
exit $status
