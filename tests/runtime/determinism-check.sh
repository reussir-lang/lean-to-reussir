#!/usr/bin/env bash
# lean2rr's translation is deterministic and local: for each program below
# (runtime tests and classic programs, translation only: `lean2rr --emit
# rr`, no Reussir build):
# - two translations of the program give byte-identical .rr files;
# - with one unrelated definition added (a structure of two numbers, a
#   recursive function over it that uses only `Nat` arithmetic, so that it
#   shares no instance or specialization with the program, and a new entry
#   point `l2rDetRoot` that runs the program's `main` and then prints that
#   function's result; translated with `--root l2rDetRoot`), every
#   function translated from the
#   program's own Lean code, except `main` itself (`l_main___*`, now called
#   by the new entry point), is unchanged up to lean2rr's numbering: the
#   generated names that come from lean2rr's one counter (types such as
#   `T_List_15`, helpers such as `l2r_zero_836`, local names) shift when a
#   definition is added, so the functions are compared in the canonical
#   form of tests/runtime/rr-fingerprint.py (`compare`), which replaces those
#   numbers by labels made from the definitions themselves. A changed or
#   dropped function fails the check: it means a definition the program
#   does not use from there changed the code of others (a layout, a
#   representation or an instance chosen from the whole program).
# Programs in KNOWN below are known to fail the second part (XFAIL, with
# the reason; XPASS once they pass). Two translations that differ always
# fail.
#   tests/runtime/determinism-check.sh [PROGRAM...]
# A PROGRAM is the name of a test in tests/runtime (RtFoo) or of a classic
# program in tests/classic (Rbtree); default: the list below.
# Environment: as run.sh (L2R_LEAN2RR, L2R_TEST_BUILD, L2R_LEAN_TOOLCHAIN,
# L2R_DISABLE_OPTS / L2R_ENABLE_OPTS).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
LEAN2RR=${L2R_LEAN2RR:-$ROOT/lean2rr/.lake/build/bin/lean2rr}
OUT=${L2R_TEST_BUILD:-$HERE/build}/determinism-check
FP="python3 $HERE/rr-fingerprint.py"
mkdir -p "$OUT"
cd "$OUT"
# Programs with conversions, uniform code, dependent fields, function values,
# tasks, and two classic programs without values of unknown type.
PROGRAMS=(RtReprProdDag RtDepFields RtUniformUpdates RtExistPayloads RtTaskConvSync RtFnConvChain Rbtree TypeclassGeneric)
[ $# -gt 0 ] && PROGRAMS=("$@")
# Programs known to fail the second part (XFAIL; XPASS once fixed), and why.
declare -A KNOWN=(
  [RtTaskConvSync]="a join point of check gets its parameters in another order from the mono phase (lean2rr --emit mono: same variables, other _uniq ids, other order; Stage 2 runs Lean's passes over the whole program in one session, so one counter draws the ids, and the order follows them, likely through a hash-ordered set): its tuple type and check's code change"
)
opts=()
IFS=, read -r -a dis <<< "${L2R_DISABLE_OPTS:-}"
for o in ${dis[@]+"${dis[@]}"}; do [ -n "$o" ] && opts+=(--disable-opt "$o"); done
IFS=, read -r -a ena <<< "${L2R_ENABLE_OPTS:-}"
for o in ${ena[@]+"${ena[@]}"}; do [ -n "$o" ] && opts+=(--enable-opt "$o"); done

# translate DIR MODULE ROOT OUT.rr
translate() {
  (cd "$1" && LEAN_PATH="$1" L2R_SHIM_DIR="$ROOT/lean2rr/.lake/build/lib/lean" LEAN_STACK_SIZE_KB=1048576 \
     "$LEAN2RR" "$2" --root "$3" --emit rr --prelude "$ROOT/runtime/prelude.rr" -o "$4" ${opts[@]+"${opts[@]}"}) \
    > "$4.log" 2>&1
}

status=0
for p in "${PROGRAMS[@]}"; do
  if [ -f "$HERE/$p.lean" ]; then src=$HERE/$p.lean; else src=$ROOT/tests/classic/$p.lean; fi
  if [ ! -f "$src" ]; then echo "FAIL $p: no $HERE/$p.lean or tests/classic/$p.lean"; status=1; continue; fi
  d=$OUT/$p; rm -rf "$d"; mkdir -p "$d/a" "$d/b"
  cp "$src" "$d/a/$p.lean"
  # The variant: the unrelated definition and the new entry point after
  # the program; the entry point has the type of the program's `main`.
  sig=$(grep -E '^(unsafe )?def main( |$)' "$src" | tail -1)
  case $sig in
    "unsafe "*) un="unsafe " ;;
    *) un="" ;;
  esac
  case $sig in
    *"(args : List String) : IO Unit"*) hdr="(args : List String) : IO Unit"; call="main args"; n="args.length"; ret="" ;;
    *"(args : List String) : IO UInt32"*) hdr="(args : List String) : IO UInt32"; call="let r ← main args"; n="args.length"; ret="  return r" ;;
    *": IO Unit"*) hdr=": IO Unit"; call="main"; n="3"; ret="" ;;
    *": IO UInt32"*) hdr=": IO UInt32"; call="let r ← main"; n="3"; ret="  return r" ;;
    *) echo "FAIL $p: unrecognized main: $sig"; status=1; continue ;;
  esac
  {
    cat "$src"
    cat <<EOF

structure L2RDetExtra where
  a : Nat
  b : Nat

@[noinline] def l2rDetStep : Nat → L2RDetExtra → L2RDetExtra
  | 0, e => e
  | k + 1, e => l2rDetStep k ⟨e.b, (e.a + e.b) % 1000003⟩

@[noinline] def l2rDetExtra (n : Nat) : Nat := (l2rDetStep (n + 10) ⟨0, 1⟩).b

${un}def l2rDetRoot $hdr := do
  $call
  IO.println (l2rDetExtra $n)
$ret
EOF
  } > "$d/b/$p.lean"
  ok=1
  for v in a b; do
    (cd "$d/$v" && lean -o "$p.olean" "$p.lean") > "$d/$v/lean.log" 2>&1 \
      || { echo "FAIL $p: lean failed on the $( [ $v = a ] && echo program || echo variant) (see $d/$v/lean.log)"; status=1; ok=""; }
  done
  [ -n "$ok" ] || continue
  if ! translate "$d/a" "$p" main "$d/a/one.rr" || ! translate "$d/a" "$p" main "$d/a/two.rr"; then
    echo "FAIL $p: lean2rr failed (see $d/a/one.rr.log, $d/a/two.rr.log)"; status=1; continue
  fi
  if ! cmp -s "$d/a/one.rr" "$d/a/two.rr"; then
    echo "FAIL $p: two translations differ (diff $d/a/one.rr $d/a/two.rr)"; status=1; continue
  fi
  if ! translate "$d/b" "$p" l2rDetRoot "$d/b/extra.rr"; then
    echo "FAIL $p: lean2rr failed on the variant (see $d/b/extra.rr.log)"; status=1; continue
  fi
  $FP compare "$d/a/one.rr" "$d/b/extra.rr" --ignore l_main___ > "$d/compare.txt" 2>&1 || true
  sum=$(grep '^summary:' "$d/compare.txt" || echo "summary: (none)")
  if [ "$sum" = "summary: (none)" ]; then
    echo "FAIL $p: rr-fingerprint.py failed (see $d/compare.txt)"; status=1
  elif grep -qE "^(changed|dropped) l_" "$d/compare.txt"; then
    if [ -n "${KNOWN[$p]:-}" ]; then
      echo "XFAIL $p: ${KNOWN[$p]}"
    else
      echo "FAIL $p: an unrelated definition changed other functions ($sum; see $d/compare.txt)"
      status=1
    fi
    grep -E '^(changed|dropped) l_' "$d/compare.txt" | head -5 | sed 's/^/  /'
  elif [ -n "${KNOWN[$p]:-}" ]; then
    echo "XPASS $p: two translations identical, and no other function changed (remove it from KNOWN)"
  else
    echo "ok   $p: two translations identical; with an unrelated definition: ${sum#summary: }"
  fi
done
[ $status -eq 0 ] && echo "PASS  determinism-check"
exit $status
