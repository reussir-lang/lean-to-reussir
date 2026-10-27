#!/usr/bin/env bash
# A match inside an alternative of a match on the same value needs no second
# match at run time when flatten-structs built the value behind a join on
# its tag (Opt/Flatten.lean, `xform`'s `cases` on a built object and
# `xformCases`' `built`: the alternative knows the value's constructor).
# Translation only (`lean2rr --emit rr`, no Reussir build), on
# tests/runtime/RtFlattenNestedMatch, whose output run.sh checks: in the
# loop of each of `storeE` (an `Except`), `storeS` (constructors with the
# same field types) and `meet` (the value then goes into a join point's
# split parameter), the arms of the matches on that type
# (`T_<type>_<n>::c_<ctor>(...) =>`) are at most those that stay: the outer
# match and the inner match of a default alternative (storeE 3, storeS 3,
# meet 2). With the inner matches left to run time they were 5 each
# (before hunt-cleanups).
#   tests/runtime/flatten-match-check.sh
# Environment: as determinism-check.sh (L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
LEAN2RR=${L2R_LEAN2RR:-$ROOT/lean2rr/.lake/build/bin/lean2rr}
BASE=${L2R_TEST_BUILD:-$HERE/build}/flatten-match-check
rm -rf "$BASE"
P=RtFlattenNestedMatch
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
  # body NAME: the generated function of the loop of NAME (its worker).
  body() {
    awk -v f="fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00$1_spec__0___l2r_0____redArg___l2r__flat(" \
      'index($0, f) == 1 { on = 1 } on { print } on && /^}/ { exit }' "$OUT/on.rr"
  }
  # arms NAME TYPE MAX: the loop of NAME has at most MAX arms on TYPE.
  arms() {
    local b n
    b=$(body "$1")
    [ -n "$b" ] || { fail "no loop function for $1"; return; }
    n=$(grep -cE "T_$2_[0-9]+::c_[a-z]+\([^)]*\) =>" <<< "$b")
    if [ "$n" -gt "$3" ]; then fail "$1: $n arms on $2, expected at most $3 (an inner match left to run time)"
    elif [ "$n" -lt 2 ]; then fail "$1: $n arms on $2, expected the outer match (at least 2)"
    else echo "ok   $1: $n arms on $2 (at most $3)"; fi
  }
  arms storeE Except 3
  arms storeS S 3
  arms meet R 2
fi
[ $status -eq 0 ] && echo "PASS  flatten-match-check"
exit $status
