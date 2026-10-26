#!/usr/bin/env bash
# The payload numbers of boxed typed arrays (LowerBase's `boxIsLeaf`,
# `boxLeafArrayElem`): a typed array whose elements leanrt frees at once
# (`free_leaves`, its `leaf_elems!` list: `Nat`, `Int`, `String`, arrays of
# scalars) is a leaf payload of the box, its number has `LEAF_BIT` (0x8000)
# and leanrt releases it directly, also inside a free; a typed array of
# records is not a leaf. Translation only (`lean2rr --emit rr`, no Reussir
# build), on tests/runtime/RtBoxLeafArrays, whose output run.sh checks:
# - under `--int-backend leanrt`, the program's release table
#   (`fn l2r_any_rel_<num>(x : <type>)`, one per payload type) has `RVec<Nat>`, `RVec<Int>`, `RVec<LStr>` and
#   `RVec<RVec<u8>>` at numbers with `LEAF_BIT`, and an `RVec` of a record
#   (`RVec<T_Pt_…>`) at a number without it;
# - the same under `--int-backend rcgmp` (the typed arrays of Reussir's
#   built-in integers, leanrt's `Mpz` elements).
#   tests/runtime/box-leaf-check.sh
# Environment: as determinism-check.sh (L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
LEAN2RR=${L2R_LEAN2RR:-$ROOT/lean2rr/.lake/build/bin/lean2rr}
BASE=${L2R_TEST_BUILD:-$HERE/build}/box-leaf-check
P=RtBoxLeafArrays
OUT=$BASE/$P
rm -rf "$BASE"
mkdir -p "$OUT"
cp "$HERE/$P.lean" "$OUT/"
status=0
fails=0
fail() { echo "FAIL $P: $*"; status=1; fails=$((fails + 1)); }
(cd "$OUT" && lean -o "$P.olean" "$P.lean") > "$OUT/lean.log" 2>&1 \
  || { fail "lean failed (see $OUT/lean.log)"; exit 1; }
# translate OUT.rr [lean2rr flags...]
translate() {
  local o=$1; shift
  (cd "$OUT" && LEAN_PATH="$OUT" L2R_SHIM_DIR="$ROOT/lean2rr/.lake/build/lib/lean" LEAN_STACK_SIZE_KB=1048576 \
     "$LEAN2RR" "$P" --emit rr --prelude "$ROOT/runtime/prelude.rr" -o "$o" "$@") > "$o.log" 2>&1
}
# num FILE TYPE: the payload number of TYPE in FILE's release table (empty
# if TYPE is not boxed); TYPE an extended regular expression.
num() { sed -nE "s/^fn l2r_any_rel_([0-9]+)\(x : ($2)\) -> unit .*/\1/p" "$1" | head -1; }
# check FILE NAME: the leaf arrays have LEAF_BIT, the array of records not.
check() {
  local f=$1 name=$2 n before=$fails
  for t in 'RVec<Nat>' 'RVec<Int>' 'RVec<LStr>' 'RVec<RVec<u8>>'; do
    n=$(num "$f" "$t")
    if [ -z "$n" ]; then fail "$name: no boxed $t"
    elif [ $((n & 0x8000)) -eq 0 ]; then fail "$name: $t has payload number $n, without LEAF_BIT"
    fi
  done
  n=$(num "$f" 'RVec<T_Pt_[0-9]+>')
  if [ -z "$n" ]; then fail "$name: no boxed RVec of the record Pt"
  elif [ $((n & 0x8000)) -ne 0 ]; then fail "$name: the RVec of records has payload number $n, with LEAF_BIT"
  fi
  [ $fails -eq $before ] && echo "ok   $P ($name): RVec<Nat|Int|LStr|RVec<u8>> leaf payloads, RVec<Pt> not"
}
if translate "$OUT/leanrt.rr" --int-backend leanrt; then check "$OUT/leanrt.rr" leanrt
else fail "leanrt did not translate (see $OUT/leanrt.rr.log)"; fi
if translate "$OUT/rcgmp.rr" --int-backend rcgmp; then check "$OUT/rcgmp.rr" rcgmp
else fail "--int-backend rcgmp did not translate (see $OUT/rcgmp.rr.log)"; fi
[ $status -eq 0 ] && echo "PASS  box-leaf-check"
exit $status
