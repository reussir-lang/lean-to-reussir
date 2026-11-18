#!/usr/bin/env bash
# Reussir makes a loop of a self call whose result goes into a constructor
# (tail recursion modulo cons) where lean2rr's code allows it, and only
# there: builds tests/runtime/TrmcHelper.lean through lean2rr to MLIR's LLVM
# dialect (scripts/l2r.py --emit mlir-llvm: the functions as Reussir's
# passes leave them, before LLVM's inliner) and checks, for each function
# of the program, the helper function that Reussir's pass makes for a loop
# (`<function>.trmc`, also of a borrowing copy: `<function>.borrowed_N.trmc`):
# - `boxNat`, `boxFloat`, `boxStruct` (the only work after the self call is
#   the box of the element) must have one: lean2rr binds the box before the
#   self call (Lower/PreBox;
#   docs/implementation/control-flow/calls-and-lets.md, "The boxes of a
#   constructor that takes a self call's result are bound before the
#   call"). Without that binding, or without Reussir's pass, the functions
#   recurse: right results, but a stack frame per element;
# - `callApp`, `callFn` (a traced call written after the self call) must
#   have none: the call must run after the recursion (tests/runtime/
#   RtTrmcCallOrder checks the order at run time). A helper there is the
#   wrong order of Reussir before upstream #984.
# Each function must also be in the file under its own name, so that a
# changed name cannot pass the "none" checks.
#   tests/runtime/trmc-helper-check.sh
# Environment: as run.sh (L2R_REUSSIR, L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN, L2R_LEAN_RUNTIME).
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
OUT=${L2R_TEST_BUILD:-$HERE/build}/trmc-helper-check
mkdir -p "$OUT"
cd "$OUT"
t=TrmcHelper
cp "$HERE/$t.lean" .
lean -o "$t.olean" "$t.lean"
if ! python3 "$ROOT/scripts/l2r.py" "$t" --lean-path "$OUT" --emit mlir-llvm -o "$OUT/$t.mlir" > "$t.build.log" 2>&1; then
  echo "FAIL $t: build failed (see $OUT/$t.build.log)"; exit 1
fi
# The functions the file defines (`llvm.func … @<symbol>(`), one per line.
grep -o 'llvm\.func [^@(]*@"\?[A-Za-z0-9_.$]*' "$t.mlir" | sed 's/.*@"\{0,1\}//' | sort -u > "$t.funcs"
status=0
# check NAME yes|no: the Lean function NAME (lean2rr's `l_NAME___l2r_0_`).
check() {
  local own helper
  own=$(grep -c "l_$1___l2r_0_\$" "$t.funcs" || true)
  helper=$(grep -c "l_$1___l2r_0_\(\.borrowed_[0-9_]*\)\{0,1\}\.trmc" "$t.funcs" || true)
  if [ "$own" -eq 0 ]; then
    echo "FAIL $t: no function l_$1___l2r_0_ in $OUT/$t.mlir (the check does not know lean2rr's name of $1)"; status=1
  elif [ "$2" = yes ] && [ "$helper" -eq 0 ]; then
    echo "FAIL $t: $1 has no .trmc helper: the self call is not a loop (the box of the element is not bound before it, or Reussir's pass did not run)"; status=1
  elif [ "$2" = no ] && [ "$helper" -ne 0 ]; then
    echo "FAIL $t: $1 has a .trmc helper: the self call moved past the call written after it (wrong order)"; status=1
  else
    echo "PASS  $1: $([ "$2" = yes ] && echo "a loop ($helper helper functions)" || echo "no loop")"
  fi
}
check boxNat yes
check boxFloat yes
check boxStruct yes
check callApp no
check callFn no
[ $status -eq 0 ] && echo "PASS  trmc-helper-check"
exit $status
