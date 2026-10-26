#!/usr/bin/env bash
# The functions that the required practice `inline-anchors` keeps out of
# rrc's MLIR inliner for their copies (Emit/CopyAnchors): at each function
# g, the callees that rrc can inline (a lower bound of their size at most
# 256; their size, counting what rrc may inline into them first, over 32)
# add Σ (calls in g - 1) x size; while that is over 4000, the callee that
# adds the most is anchored. Translation only (`lean2rr --emit rr`, no Reussir build), under
# both representations of `Nat` and `Int`:
# - RtJpWide with `--int-backend rcgmp`: its 800-arm
#   `match` is one function (`int-match`) whose arms call three outlined join
#   points (J3) about 266 times each: those three `jp_` functions are
#   `#[transform_anchor]`, and no other `jp_` is;
# - RtJpWide with `--int-backend leanrt`: the same three join points (200 or more calls
#   each), but the `match` is a chain of tests that `Outline` cuts into
#   functions of a few arms, so no function calls one of them more than a
#   few times: none is anchored;
# - RtJpAnchors under both: `tiny`'s small join point (250 or more calls)
#   and `few`'s larger one (2 to 6 calls, more than 40 lines) are
#   outlined and not anchored, and the rule anchors no function; under
#   rcgmp `tiny`'s join point (one function calls it 300 times) is listed
#   as a small function left to the inliner over the budget (so the
#   exemption of small functions is what keeps it inlinable);
# - RtCopyAnchors under both: of `p0`, `p1`, `p2` (each alone under the
#   budget in `sum3`, together over it) exactly two are anchored; `wrap`
#   (own size at most 32, mid-size with `big` inlined into it) is anchored
#   and `big` is not; `build` (which calls itself) is anchored; `mid`
#   (under 256 on its own, over it with `loop`, which calls itself and which
#   rrc does not inline into it) is anchored and `loop` is not; `fc` is
#   anchored for the 64 calls of `fb`, in the cycle fa -> fb -> fc -> fa;
#   six functions in all.
# The functions the rule anchors, with their sizes and calls, are read
# from lean2rr's `L2R_DEBUG` lines `lean2rr: inline-anchors: N function(s)
# kept out of rrc's inliner for their copies NAME (size S, own O, C calls
# in G) …` and `… small function(s) left to rrc's inliner over the budget
# …` (the other anchors, `anchoredFns`, are not in them), and the join
# points' `#[transform_anchor]`s from the .rr.
# The check fails when a program has none of the join points it looks at
# (it would check nothing). Self-check: RtJpWide under rcgmp with
# `L2R_NO_INLINE_ANCHORS` (no anchors at all) must fail the check of its
# .rr.
#   tests/runtime/inline-anchors-check.sh
# Environment: as determinism-check.sh (L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
LEAN2RR=${L2R_LEAN2RR:-$ROOT/lean2rr/.lake/build/bin/lean2rr}
BASE=${L2R_TEST_BUILD:-$HERE/build}/inline-anchors-check
rm -rf "$BASE"
# translate OUT.rr [lean2rr flags...]
translate() {
  local o=$1; shift
  (cd "$OUT" && L2R_DEBUG=1 LEAN_PATH="$OUT" L2R_SHIM_DIR="$ROOT/lean2rr/.lake/build/lib/lean" LEAN_STACK_SIZE_KB=1048576 \
     "$LEAN2RR" "$P" --emit rr --prelude "$ROOT/runtime/prelude.rr" -o "$o" "$@") > "$o.log" 2>&1
}
# anchors FILE.rr [small]: the functions the rule anchored (or, with
# `small`, the small ones left over the budget), one per line: name size
# own calls caller (from FILE.rr.log); empty when there is none.
anchors() {
  local which="kept out of rrc's inliner for their copies"
  [ "${2:-}" = small ] && which="left to rrc's inliner over the budget"
  grep -F "lean2rr: inline-anchors: " "$1.log" | grep -F "$which" \
    | grep -oE '[A-Za-z0-9_]+ \(size [0-9]+, own [0-9]+, [0-9]+ calls in [A-Za-z0-9_]+\)' \
    | sed -E 's/ \(size ([0-9]+), own ([0-9]+), ([0-9]+) calls in ([A-Za-z0-9_]+)\)/ \1 \2 \3 \4/'
}
# count FILE.rr: the N of the debug line (empty when lean2rr printed none).
count() { sed -n "s/^lean2rr: inline-anchors: \([0-9]*\) function(s) kept out of rrc's inliner for their copies.*/\1/p" "$1.log"; }
status=0
fails=0
fail() { echo "FAIL $P: $*"; status=1; fails=$((fails + 1)); }
# jps FILE: one line per generated join-point function: name, 1 if it is
# anchored (`#[transform_anchor]` on the line before), its number of lines,
# its number of calls in FILE.
jps() {
  awk '
    /^fn jp_[0-9]+\(/ { n = $2; sub(/\(.*/, "", n); anch[n] = (prev == "#[transform_anchor]"); start[n] = NR; cur = n }
    cur != "" && /^}/ { len[cur] = NR - start[cur] + 1; cur = "" }
    { prev = $0; line[NR] = $0 }
    END {
      for (n in anch) {
        c = 0
        for (i = 1; i <= NR; i++) {
          s = line[i]
          while ((p = index(s, n "(")) > 0) {
            before = p > 1 ? substr(s, p - 1, 1) : " "
            if (before !~ /[A-Za-z0-9_]/ && !(i == start[n])) c++
            s = substr(s, p + length(n) + 1)
          }
        }
        print n, anch[n], len[n], c
      }
    }' "$1" | sort
}
# wide FILE MODE: RtJpWide's join points (200 or more calls); MODE anchored
# (exactly 3, all anchored, no other jp_ anchored) or free (3 or more, none anchored).
wide() {
  local f=$1 mode=$2 list
  list=$(jps "$f")
  local many; many=$(awk '$4 >= 200' <<< "$list")
  local nmany; nmany=$(grep -c . <<< "$many")
  [ "$nmany" -ge 3 ] || { fail "$mode: $nmany join points with 200 or more calls, expected 3 or more"; return; }
  if [ "$mode" = anchored ]; then
    [ "$nmany" -eq 3 ] || fail "$mode: $nmany join points with 200 or more calls, expected 3"
    awk '$2 != 1 { print "  not anchored: " $0 }' <<< "$many" | grep . && fail "$mode: a join point with 200 or more calls is not anchored"
    awk '$4 < 200 && $2 == 1 { print "  anchored: " $0 }' <<< "$list" | grep . && fail "$mode: a join point with fewer calls is anchored"
  else
    awk '$2 == 1 { print "  anchored: " $0 }' <<< "$list" | grep . && fail "$mode: a join point is anchored"
  fi
  return 0
}
# cases FILE.rr BACKEND: RtCopyAnchors' expectations.
cases() {
  local f=$1 be=$2 list
  list=$(anchors "$f")
  local ps; ps=$(awk '$1 ~ /^l_p[012]___l2r_0_$/' <<< "$list")
  [ "$(grep -c . <<< "$ps")" -eq 2 ] || fail "$be: $(grep -c . <<< "$ps") of p0, p1, p2 anchored, expected 2"
  # Each alone under the budget in sum3: anchored for the sum.
  awk 'NF && ($5 != "l_sum3___l2r_0_" || ($4 - 1) * $2 > 4000) { print "  " $0 }' <<< "$ps" | grep . \
    && fail "$be: a p anchored other than for the sum of sum3's copies"
  awk '$1 == "l_wrap___l2r_0_" && $3 <= 32 && $2 > 32' <<< "$list" | grep -q . \
    || fail "$be: wrap (own size at most 32, more with big inlined) is not anchored for viaWrap's calls"
  grep -q '^l_big___l2r_0_ ' <<< "$list" && fail "$be: big (one call) is anchored"
  grep -q '^l_build___l2r_0_ ' <<< "$list" || fail "$be: build (which calls itself) is not anchored"
  calls "$f" build build 1 || fail "$be: build does not call itself in the .rr (the test checks nothing)"
  # mid: anchored with its size over the limit (shown capped at 256) once
  # loop is counted, its own size under it; loop (which calls itself) not.
  awk '$1 == "l_mid___l2r_0_" && $2 == 256 && $3 <= 256' <<< "$list" | grep -q . \
    || fail "$be: mid (own size under 256, over it with loop) is not anchored for viaMid's calls"
  grep -q '^l_loop___l2r_0_ ' <<< "$list" && fail "$be: loop is anchored"
  { calls "$f" loop loop 1 && calls "$f" mid loop 1; } || fail "$be: mid does not call loop, or loop does not call itself (the test checks nothing)"
  # fc: anchored for fb's calls, in the cycle fa -> fb -> fc -> fa.
  awk '$1 == "l_fc___l2r_0_" && $5 == "l_fb___l2r_0_"' <<< "$list" | grep -q . \
    || fail "$be: fc is not anchored for the calls of fb, in their cycle"
  { calls "$f" fa fb 1 && calls "$f" fb fc 60 && calls "$f" fc fa 1; } \
    || fail "$be: no cycle fa -> fb -> fc -> fa with fb calling fc from its arms (the test checks nothing)"
  return 0
}
# calls FILE.rr G H N: the function of Lean definition G calls H's at least N times.
calls() {
  local c; c=$(awk -v f="fn l_$2___l2r_0_(" 'index($0, f) == 1 { on = 1; next } on { print } on && /^}/ { exit }' "$1" | grep -o "l_$3___l2r_0_(" | grep -c .)
  [ "$c" -ge "$4" ]
}
for P in RtJpWide RtJpAnchors RtCopyAnchors; do
  OUT=$BASE/$P
  mkdir -p "$OUT"
  cp "$HERE/$P.lean" "$OUT/"
  (cd "$OUT" && lean -o "$P.olean" "$P.lean") > "$OUT/lean.log" 2>&1 \
    || { fail "lean failed (see $OUT/lean.log)"; continue; }
  before=$fails
  for be in rcgmp leanrt; do
    # Each representation named (rcgmp is lean2rr's default since
    # 2026-10-25).
    flags=(--int-backend $be)
    R=$OUT/$be.rr
    if ! translate "$R" "${flags[@]}"; then fail "$be did not translate (see $R.log)"; continue; fi
    want=0
    case $P in
      RtJpWide)
        if [ $be = rcgmp ]; then wide "$R" anchored; want=3; else wide "$R" free; fi ;;
      RtJpAnchors)
        list=$(jps "$R")
        awk '$4 >= 250' <<< "$list" | grep -q . || fail "$be: no join point with 250 or more calls (tiny's)"
        awk '$4 >= 2 && $4 <= 6 && $3 > 40' <<< "$list" | grep -q . || fail "$be: no join point of more than 40 lines with 2 to 6 calls (few's)"
        awk '$2 == 1 { print "  anchored: " $0 }' <<< "$list" | grep . && fail "$be: a join point is anchored"
        if [ $be = rcgmp ]; then
          anchors "$R" small | awk '$1 ~ /^jp_/ && $4 >= 250 && ($4 - 1) * $2 > 4000' | grep -q . \
            || fail "$be: tiny's join point is not listed as small and over the budget (the exemption is not exercised)"
        fi ;;
      RtCopyAnchors)
        cases "$R" $be; want=6 ;;
    esac
    n=$(count "$R")
    [ "$n" = $want ] || fail "$be: the rule anchored '$n' function(s), expected $want (see $R.log)"
  done
  if [ $P = RtJpWide ]; then
    # Self-check: without anchors the check of the .rr must fail.
    R=$OUT/noanchors.rr
    if ! L2R_NO_INLINE_ANCHORS=1 translate "$R" --int-backend rcgmp; then
      fail "L2R_NO_INLINE_ANCHORS: did not translate (see $R.log)"
    else
      saved_status=$status saved_fails=$fails
      wide "$R" anchored > /dev/null
      caught=$((fails - saved_fails))
      status=$saved_status fails=$saved_fails
      [ $caught -gt 0 ] || fail "self-check: the check passed without anchors"
    fi
  fi
  [ $fails -eq $before ] && echo "ok   $P"
done
[ $status -eq 0 ] && echo "PASS  inline-anchors-check"
exit $status
