#!/usr/bin/env bash
# Programs without values of unknown type pay nothing for lean2rr's handling
# of them: for each program below (classic programs and runtime tests that
# have no conversion between layouts; the baselines are in
# tests/runtime/paynothing/NAME.fp), compares lean2rr's output for it with
# its baseline:
# - the pay-nothing counts of its generated code (tests/runtime/
#   rr-fingerprint.py `show`: conversion helpers and their uses, values put
#   into an `L2RBox`, the constructors of `L2RBox`) must not grow;
# - its allocations and the bytes it allocates (through lean2rr, with the
#   counter of tests/runtime/alloccount, at a fixed size) must not grow by
#   more than 1% plus 100 allocations or 10000 bytes; the native build's
#   counts are recorded beside them for comparison; both builds must print
#   the same output;
# - the canonical hash of each generated item (rr-fingerprint.py, stable
#   when only lean2rr's numbering changes) is compared with the baseline's,
#   and the changed, dropped and added items are listed: a change that
#   should not touch such programs shows here. The list is information
#   (a program's code may change for other reasons); with
#   PAYNOTHING_STRICT=1 any changed or dropped item fails the check.
#   tests/runtime/paynothing-check.sh [--update] [NAME...]
# --update writes the baselines from this run (after a change that is meant
# to change them; say why in the commit). A NAME is a classic program
# (tests/classic/NAME.lean, run at its `small` size of cases.json) or a
# runtime test (tests/runtime/NAME.lean, run with NAME.args).
# Environment: as run.sh (L2R_REUSSIR, L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN, L2R_LEAN_RUNTIME, L2R_DISABLE_OPTS / L2R_ENABLE_OPTS,
# L2R_RRC_FLAGS); PAYNOTHING_STRICT.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
. "$HERE/alloccount/alloccount.sh"
LEAN2RR=${L2R_LEAN2RR:-$ROOT/lean2rr/.lake/build/bin/lean2rr}
OUT=${L2R_TEST_BUILD:-$HERE/build}/paynothing-check
BASE=$HERE/paynothing
FP="python3 $HERE/rr-fingerprint.py"
update=""
[ "${1:-}" = "--update" ] && { update=1; shift; }
PROGRAMS=(Rbtree Cfold Qsort Deriv Unionfind RtJpSlots RtLazyFields)
[ $# -gt 0 ] && PROGRAMS=("$@")
mkdir -p "$OUT" "$BASE"
cd "$OUT" || exit 2
alloccount_setup "$OUT" || { echo "FAIL paynothing-check: cannot compile the counter"; exit 1; }
opts=()
IFS=, read -r -a dis <<< "${L2R_DISABLE_OPTS:-}"
for o in ${dis[@]+"${dis[@]}"}; do [ -n "$o" ] && opts+=(--disable-opt "$o"); done
IFS=, read -r -a ena <<< "${L2R_ENABLE_OPTS:-}"
for o in ${ena[@]+"${ena[@]}"}; do [ -n "$o" ] && opts+=(--enable-opt "$o"); done

# count FILE KEY: the value of `KEY N` in a fingerprint (empty if none)
count() { sed -nE "s/^$2 ([0-9]+)$/\1/p" "$1" | head -1; }

status=0
for p in "${PROGRAMS[@]}"; do
  if [ -f "$ROOT/tests/classic/$p.lean" ]; then
    src=$ROOT/tests/classic/$p.lean
    args=$(python3 -c "import json,sys; print(next(c['sizes']['small'] for c in json.load(open('$ROOT/tests/classic/cases.json')) if c['module'] == sys.argv[1]))" "$p")
  elif [ -f "$HERE/$p.lean" ]; then
    src=$HERE/$p.lean; args=""; [ -f "$HERE/$p.args" ] && args=$(cat "$HERE/$p.args")
  else
    echo "FAIL $p: no tests/classic/$p.lean or tests/runtime/$p.lean"; status=1; continue
  fi
  d=$OUT/$p; rm -rf "$d"; mkdir -p "$d"; cp "$src" "$d/"
  why=""; note=""
  # shellcheck disable=SC2086
  if ! (cd "$d" && lean -o "$p.olean" -c "$p.c" "$p.lean" && leanc -O3 -DNDEBUG "$p.c" $AC_LEANC -o native) > "$d/build-native.log" 2>&1; then
    echo "FAIL $p: native build failed (see $d/build-native.log)"; status=1; continue
  fi
  if ! (cd "$d" && LEAN_PATH="$d" L2R_SHIM_DIR="$ROOT/lean2rr/.lake/build/lib/lean" LEAN_STACK_SIZE_KB=1048576 \
        "$LEAN2RR" "$p" --root main --emit rr --prelude "$ROOT/runtime/prelude.rr" -o "$d/$p.rr" ${opts[@]+"${opts[@]}"}) \
        > "$d/translate.log" 2>&1; then
    echo "FAIL $p: lean2rr failed (see $d/translate.log)"; status=1; continue
  fi
  if ! L2R_RRC_FLAGS="${L2R_RRC_FLAGS:-} $AC_RRC" python3 "$ROOT/scripts/l2r.py" "$p" --lean-path "$d" -o "$d/l2r" \
       > "$d/build-l2r.log" 2>&1; then
    echo "FAIL $p: lean2rr build failed (see $d/build-l2r.log)"; status=1; continue
  fi
  for b in native l2r; do
    # shellcheck disable=SC2086
    (cd "$d" && LEAN_BACKTRACE=0 timeout -s KILL 120 ./$b $args < /dev/null > "$b.out" 2> "$b.err"; echo $? > "$b.code")
  done
  cmp -s "$d/native.out" "$d/l2r.out" || why="$why stdout differs from native (diff $d/native.out $d/l2r.out);"
  cmp -s "$d/native.code" "$d/l2r.code" || why="$why exit code differs from native;"
  read -r la lb <<< "$(alloccount_read "$d/l2r.err")"
  read -r na nb <<< "$(alloccount_read "$d/native.err")"
  if [ -z "$la" ] || [ -z "$na" ]; then
    echo "FAIL $p: no allocation count (see $d/l2r.err, $d/native.err)"; status=1; continue
  fi
  {
    echo "# Pay-nothing baseline of $p ($( [ "$src" = "$HERE/$p.lean" ] && echo "tests/runtime" || echo "tests/classic")/$p.lean), arguments '$args'."
    echo "# Written by tests/runtime/paynothing-check.sh --update; native allocations for comparison."
    echo "allocs $la"
    echo "bytes $lb"
    echo "native-allocs $na"
    echo "native-bytes $nb"
    $FP show "$d/$p.rr"
  } > "$d/$p.fp"
  if [ -n "$update" ]; then
    cp "$d/$p.fp" "$BASE/$p.fp"
    echo "updated $p: allocations $la (native $na), bytes $lb (native $nb), $(count "$d/$p.fp" conversion-sites) conversion sites, $(count "$d/$p.fp" box-sites) box sites"
    [ -z "$why" ] || { echo "FAIL $p:$why"; status=1; }
    continue
  fi
  if [ ! -f "$BASE/$p.fp" ]; then
    echo "FAIL $p: no baseline $BASE/$p.fp (write it with --update)"; status=1; continue
  fi
  for k in conversion-fns conversion-sites box-sites box-variants; do
    old=$(count "$BASE/$p.fp" "$k"); new=$(count "$d/$p.fp" "$k")
    if [ "$new" -gt "$old" ]; then why="$why $k grew from $old to $new;"; fi
  done
  oa=$(count "$BASE/$p.fp" allocs); ob=$(count "$BASE/$p.fp" bytes)
  [ "$la" -gt $((oa + oa / 100 + 100)) ] && why="$why allocations grew from $oa to $la;"
  [ "$lb" -gt $((ob + ob / 100 + 10000)) ] && why="$why bytes allocated grew from $ob to $lb;"
  [ "$la" -lt $((oa - oa / 100 - 100)) ] && note="$note allocations fell from $oa to $la (update the baseline);"
  $FP check "$BASE/$p.fp" "$d/$p.rr" > "$d/items.txt" 2>&1
  sum=$(grep '^summary:' "$d/items.txt" || echo "summary: (rr-fingerprint.py failed, see $d/items.txt)")
  if [ -n "${PAYNOTHING_STRICT:-}" ] && grep -qE '^(changed|dropped) ' "$d/items.txt"; then
    why="$why generated items changed (${sum#summary: }; see $d/items.txt);"
  fi
  if [ -n "$why" ]; then
    echo "FAIL $p:$why"; status=1
  else
    echo "ok   $p: allocations $la (baseline $oa, native $na); items: ${sum#summary: }${note:+;$note}"
  fi
  grep -E '^(changed|dropped) ' "$d/items.txt" | head -5 | sed 's/^/  /'
done
[ $status -eq 0 ] && echo "PASS  paynothing-check"
exit $status
