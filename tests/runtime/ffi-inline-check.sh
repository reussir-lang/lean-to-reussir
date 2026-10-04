#!/usr/bin/env bash
# The runtime's textures leave no stack slot in Reussir code: builds runtime
# tests that call the libm functions, the string, hash and float rules and
# the fixed-width rules through lean2rr to LLVM IR (scripts/l2r.py --emit
# llvm-ir) and fails on
# - any call through the packed-argument FFI boundary (`call void
#   @_RC..._ffi(`) other than the entry point (l2r_run_main): a texture LLVM
#   did not inline (review RULR-01: lean-runtime's cbrt port in a texture);
# - a `black_box` barrier (`asm sideeffect "", "r,~{memory}"`) inside a
#   Reussir function (`define ... @_RC...`, not a texture's `_ffi` boundary
#   function): a `black_box`ed libm function inlined into Reussir code
#   (review RULR-07; leanrt::float::libm_call keeps them out of line).
# Either keeps stack slots in its caller, and LLVM then keeps a Lean loop's
# self tail call around it: the loop overflows the stack
# (tests/runtime/RtFloatLoopStack.lean).
#   tests/runtime/ffi-inline-check.sh [NAME...]
# Environment: as run.sh (L2R_REUSSIR, L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN, L2R_LEAN_RUNTIME).
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
OUT=${L2R_TEST_BUILD:-$HERE/build}/ffi-inline-check
mkdir -p "$OUT"
cd "$OUT"
[ $# -gt 0 ] || set -- RtFloatLoopStack RtFloat RtString RtSweepStrPos RtHashMap RtSweepFixed RtUInt
status=0
for t in "$@"; do
  cp "$HERE/$t.lean" .
  lean -o "$t.olean" "$t.lean"
  python3 "$ROOT/scripts/l2r.py" "$t" --lean-path "$OUT" --emit llvm-ir -o "$OUT/$t.ll" > "$t.build.log" 2>&1 \
    || { echo "FAIL $t: build failed (see $OUT/$t.build.log)"; status=1; continue; }
  calls=$(grep -o 'call void @_RC[0-9]*[A-Za-z0-9_]*_ffi(' "$t.ll" | grep -v '_RC12l2r_run_main_ffi(' | sort | uniq -c || true)
  # Reussir functions (`_RC...`, not `..._ffi`) that contain a black_box barrier.
  barriers=$(awk '
    /^define / { name = ""; if (match($0, /@"?_RC[^"( ]*/)) { name = substr($0, RSTART + 1, RLENGTH - 1); sub(/^"/, "", name) }
                 if (name ~ /_ffi$/) name = "" }
    /^}/ { name = "" }
    name != "" && index($0, "asm sideeffect \"\", \"r,~{memory}\"") { n[name]++ }
    END { for (f in n) printf "%7d x %s\n", n[f], f }' "$t.ll")
  if [ -n "$calls" ]; then
    echo "FAIL $t: calls through the FFI boundary (not inlined):"; echo "$calls"; status=1
  elif [ -n "$barriers" ]; then
    echo "FAIL $t: black_box barriers inlined into Reussir functions:"; echo "$barriers"; status=1
  else
    echo "PASS  $t"
  fi
done
[ $status -eq 0 ] && echo "PASS  ffi-inline-check"
exit $status
