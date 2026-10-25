#!/usr/bin/env bash
# The shapes of the optimization `int-match` (Lower/IntMatch): under
# `--int-backend rcgmp` a case split on a `Nat` or `Int` is a Reussir
# `match` on the built-in integer. Translation only (`lean2rr --emit rr`,
# no Reussir build), on tests/runtime/RtNatMatch and RtIntMatch, whose
# outputs run.sh checks:
# - with `--int-backend rcgmp --rcgmp-type-args`: `sumTo` is one match
#   with the arms `0` and `Nat::Succ(p)` and no `lean_nat_dec_eq`/
#   `lean_nat_sub`; `fib` one match `0`, `1`, `Nat::Succ(Nat::Succ(p))`;
#   `lits` one match with an arm per literal (also 2^64 and 10^30, which
#   Lean reads from closed terms) and no test left; `keepN`, whose
#   `n+1` arm names the scrutinee, matches a copy (`let ns… = n`); `twice`
#   keeps its test (its result is used twice); `fine` (RtIntMatch) is one
#   match with `0`, `Int::OfNat(Nat::Succ(n))`, `-1` and
#   `Int::NegSucc(Nat::Succ(m))` and no `lean_int_dec_lt`/`lean_nat_abs`;
#   `namedI` matches a copy; `intLit`'s tests of `Int` literals (0, 1, -1,
#   5, -7, read from closed terms) are one match;
# - with `--disable-opt int-match` too: no match on a `Nat` or `Int`
#   (no `Nat::Succ(`, `Int::OfNat(`, `Int::NegSucc(` pattern);
# - under leanrt the .rr is the same with and without the optimization.
#   tests/runtime/int-match-check.sh
# Environment: as determinism-check.sh (L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
LEAN2RR=${L2R_LEAN2RR:-$ROOT/lean2rr/.lake/build/bin/lean2rr}
BASE=${L2R_TEST_BUILD:-$HERE/build}/int-match-check
rm -rf "$BASE"
# translate OUT.rr [lean2rr flags...]
translate() {
  local o=$1; shift
  (cd "$OUT" && LEAN_PATH="$OUT" L2R_SHIM_DIR="$ROOT/lean2rr/.lake/build/lib/lean" LEAN_STACK_SIZE_KB=1048576 \
     "$LEAN2RR" "$P" --emit rr --prelude "$ROOT/runtime/prelude.rr" -o "$o" "$@") > "$o.log" 2>&1
}
# body FILE NAME: the generated function of Lean definition NAME (its first instance).
body() { awk -v f="fn l_$2___l2r_0_(" 'index($0, f) == 1 { on = 1 } on { print } on && /^}/ { exit }' "$1"; }
status=0
fail() { echo "FAIL $P: $*"; status=1; }
# has FILE NAME TEXT...: each TEXT occurs in NAME's function; lacks: none does.
has() { local f=$1 n=$2; shift 2; local b; b=$(body "$f" "$n")
  [ -n "$b" ] || { fail "no function for $n"; return; }
  for t in "$@"; do grep -qF -- "$t" <<< "$b" || fail "$n: no '$t'"; done; }
lacks() { local f=$1 n=$2; shift 2; local b; b=$(body "$f" "$n")
  for t in "$@"; do grep -qF -- "$t" <<< "$b" && fail "$n: '$t' left"; done; return 0; }
count() { body "$1" "$2" | grep -c -- "$3"; }
for P in RtNatMatch RtIntMatch; do
  OUT=$BASE/$P
  mkdir -p "$OUT"
  cp "$HERE/$P.lean" "$OUT/"
  (cd "$OUT" && lean -o "$P.olean" "$P.lean") > "$OUT/lean.log" 2>&1 \
    || { fail "lean failed (see $OUT/lean.log)"; continue; }
  before=$status
  if ! translate "$OUT/on.rr" --int-backend rcgmp --rcgmp-type-args; then
    fail "--int-backend rcgmp did not translate (see $OUT/on.rr.log)"
  elif [ $P = RtNatMatch ]; then
    R=$OUT/on.rr
    has $R sumTo "match " "0 => " "Nat::Succ(f"; lacks $R sumTo lean_nat_dec_eq lean_nat_sub
    has $R fib "1 => " "Nat::Succ(Nat::Succ(f"; lacks $R fib lean_nat_dec_eq lean_nat_sub
    has $R lits "5 => " "2305843009213693952 => " "18446744073709551616 => " "1000000000000000000000000000000 => " "_ => "
    lacks $R lits lean_nat_dec_eq
    [ "$(count $R lits ' => ')" = 8 ] || fail "lits: $(count $R lits ' => ') arms, expected 8"
    has $R keepN "let ns" "Nat::Succ(f"
    has $R twice lean_nat_dec_eq
  else
    R=$OUT/on.rr
    has $R fine "0 => " "Int::OfNat(Nat::Succ(f" "-1 => " "Int::NegSucc(Nat::Succ(f"
    lacks $R fine lean_int_dec_lt lean_nat_abs lean_nat_dec_eq
    has $R namedI "let ns" "Int::NegSucc(f"
    has $R intLit "0 => " "1 => " "-1 => " "5 => " "-7 => " "_ => "
    lacks $R intLit lean_int_dec_eq
  fi
  if ! translate "$OUT/off.rr" --int-backend rcgmp --rcgmp-type-args --disable-opt int-match; then
    fail "--disable-opt int-match did not translate (see $OUT/off.rr.log)"
  elif grep -nE 'Nat::Succ\(|Int::(OfNat|NegSucc)\(' "$OUT/off.rr" > "$OUT/off.hits"; then
    fail "--disable-opt int-match left a match on Nat or Int (see $OUT/off.hits)"
  fi
  if ! translate "$OUT/leanrt.rr" || ! translate "$OUT/leanrt-off.rr" --disable-opt int-match; then
    fail "leanrt did not translate (see $OUT/leanrt*.rr.log)"
  elif ! cmp -s "$OUT/leanrt.rr" "$OUT/leanrt-off.rr"; then
    fail "under leanrt int-match changed the .rr"
  fi
  [ $status -eq $before ] && echo "ok   $P: matches under rcgmp, none with int-match off, leanrt unchanged"
done
[ $status -eq 0 ] && echo "PASS  int-match-check"
exit $status
