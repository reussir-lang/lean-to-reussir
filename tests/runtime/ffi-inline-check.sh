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
# For RtReadsDeep (array reads deep in branches, call sites that LLVM judges
# cold), it also fails on any call left of an array read's texture or
# function (`l2r_array_give`, `l2r_view_take`, `lean_byte_array_fget`, ...;
# docs/implementation/ownership.md, "Reads give their reference up first,
# for a view"): the read textures must stay under LLVM's inlining threshold
# for a cold call site (Reussir issue 36), else every such read is a call.
# For RtArraySets (array sets in loops at ordinary call sites), it likewise fails
# on any call left of an array set's texture or function (`l2r_array_set`,
# `lean_array_set`, `l2r_natarr_set_word`, ...; docs/implementation/
# ownership.md, "A set releases a replaced record with its decrement in
# line"): the set of an `Array` of a structure released the replaced
# element with the structure's whole release in line, and LLVM kept the
# texture out of line (unionfind's `l2r_array_set`).
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
[ $# -gt 0 ] || set -- RtFloatLoopStack RtFloat RtString RtSweepStrPos RtHashMap RtSweepFixed RtUInt RtReadsDeep RtArraySets
# Reussir's symbols are `_RC<length><name>...` (`_RIC` for an instance of a
# generic function); the read functions whose calls RtReadsDeep must not keep
# (`deep_calls FILE reads`), the set functions whose calls RtArraySets must
# not keep (`deep_calls FILE sets`).
deep_calls() {
  python3 - "$1" "$2" <<'PY'
import re, sys
if sys.argv[2] == "reads":
    names = {f"l2r_{k}arr_{op}" for k in ("nat", "int") for op in
             ("give", "view_size", "view_take", "view_end", "take", "get", "get_word")}
    names |= {"l2r_array_give", "l2r_view_size", "l2r_view_take", "l2r_view_end",
              "l2r_array_get", "l2r_array_get_word", "l2r_consume"}
    names |= {f"lean_{a}_{op}" for a in ("array", "byte_array", "float_array", "natarr", "intarr")
              for op in ("fget", "fget_borrowed", "uget", "uget_borrowed", "get", "get_borrowed")}
else:
    names = {f"l2r_{k}arr_{op}" for k in ("nat", "int") for op in ("set", "set_word")}
    names |= {"l2r_array_set"}
    names |= {f"lean_{a}_{op}" for a in ("array", "byte_array", "float_array", "natarr", "intarr")
              for op in ("set", "fset", "uset")}
seen = {}
for m in re.finditer(r'call [^@\n]*@"?_RI?C(\d+)([A-Za-z0-9_]+)\(', open(sys.argv[1]).read()):
    n = m.group(2)[:int(m.group(1))]
    if n in names:
        seen[n] = seen.get(n, 0) + 1
for n, k in sorted(seen.items()):
    print(f"{k:7d} x {n}")
PY
}
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
  reads=""
  [ "$t" = RtReadsDeep ] && reads=$(deep_calls "$t.ll" reads)
  sets=""
  [ "$t" = RtArraySets ] && sets=$(deep_calls "$t.ll" sets)
  if [ -n "$calls" ]; then
    echo "FAIL $t: calls through the FFI boundary (not inlined):"; echo "$calls"; status=1
  elif [ -n "$reads" ]; then
    echo "FAIL $t: array reads left as calls (a read texture over LLVM's cold-site threshold):"; echo "$reads"; status=1
  elif [ -n "$sets" ]; then
    echo "FAIL $t: array sets left as calls (a set texture LLVM did not inline):"; echo "$sets"; status=1
  elif [ -n "$barriers" ]; then
    echo "FAIL $t: black_box barriers inlined into Reussir functions:"; echo "$barriers"; status=1
  else
    echo "PASS  $t"
  fi
done
[ $status -eq 0 ] && echo "PASS  ffi-inline-check"
exit $status
