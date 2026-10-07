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
# function (`l2r_array_give`, `l2r_view_take`, `lean_byte_array_fget`, the
# reads at a type `lean_array_fget_as`, `l2r_view_take_as`, ...;
# docs/implementation/ownership.md, "Reads give their reference up first,
# for a view"): the read textures must stay under LLVM's inlining threshold
# for a cold call site (cost 45), else every such read is a call. The
# exception: three read textures cost more than 45, the read of a box
# (`l2r_view_take<LAny>`: with the one-word `Box`) and the reads of a `Nat`
# or `Int` element at its type (`l2r_view_take_as<Nat>`, `<Int>`), and rrc
# gives a texture's import trampoline no inline attribute (Reussir issue
# 36, not patched: its patch 36-a is parked). So in RtReadsDeep, whose
# reads all sit at cold call sites, the calls of these three symbols
# (COLD_ALLOWED) are allowed and counted.
# For RtArraySets (array sets and reads in loops at ordinary call sites), it
# fails on any call left of an array set's or read's texture or function
# (`l2r_array_set`, `lean_array_set`, `l2r_view_take`, ...), with no
# exception: at an ordinary call site LLVM inlines a texture up to cost
# 250 (RtArraySets reads a box there). The set of an `Array` of a structure
# released the replaced element with the structure's whole release in line,
# and LLVM kept the texture out of line (unionfind's `l2r_array_set`;
# docs/implementation/ownership.md, "A set releases a replaced record with
# its decrement in line").
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
# generic function, its type arguments after the name). `deep_calls FILE
# KINDS [SYMBOL...]` counts the calls of the read functions (KINDS `reads`)
# or of the read and set functions (`reads,sets`); a call of one of the
# SYMBOLs is printed as `allowed`.
deep_calls() {
  python3 - "$@" <<'PY'
import re, sys
kinds, allow = sys.argv[2].split(","), set(sys.argv[3:])
names = set()
if "reads" in kinds:
    names |= {"l2r_array_give", "l2r_view_size", "l2r_view_take", "l2r_view_end",
              "l2r_array_get", "l2r_array_get_word", "l2r_consume",
              "l2r_view_take_as", "l2r_any_take_as", "l2r_array_get_as", "l2r_array_get_word_as"}
    names |= {f"lean_{a}_{op}" for a in ("array", "byte_array", "float_array")
              for op in ("fget", "fget_borrowed", "uget", "uget_borrowed", "get", "get_borrowed")}
    # The reads of an element at a type (an immediate without a copy of its
    # box: lean2rr's boxWordRead?).
    names |= {f"lean_array_{op}_as" for op in ("fget", "fget_borrowed", "uget", "uget_borrowed", "get", "get_borrowed")}
if "sets" in kinds:
    names |= {"l2r_array_set"}
    names |= {f"lean_{a}_{op}" for a in ("array", "byte_array", "float_array")
              for op in ("set", "fset", "uset")}
seen = {}
for m in re.finditer(r'call [^@\n]*@"?(_RI?C(\d+)([A-Za-z0-9_]+))\(', open(sys.argv[1]).read()):
    n = m.group(3)[:int(m.group(2))]
    if n in names:
        k = ("allowed", m.group(1)) if m.group(1) in allow else ("", n)
        seen[k] = seen.get(k, 0) + 1
for (a, n), k in sorted(seen.items()):
    print(f"{a + ' ' if a else ''}{k:7d} x {n}")
PY
}
# The reads that Reussir issue 36 (not patched) keeps as calls at a cold
# call site: `l2r_view_take<LAny>`, `l2r_view_take_as<Nat>`,
# `l2r_view_take_as<Int>`.
COLD_ALLOWED="_RIC13l2r_view_takeC4LAnyE _RIC16l2r_view_take_asC3NatE _RIC16l2r_view_take_asC3IntE"
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
  deep=""
  [ "$t" = RtReadsDeep ] && deep=$(deep_calls "$t.ll" reads $COLD_ALLOWED)
  [ "$t" = RtArraySets ] && deep=$(deep_calls "$t.ll" reads,sets)
  reads=$(printf '%s\n' "$deep" | grep -v -e '^allowed' -e '^$' || true)
  allowed=$(printf '%s\n' "$deep" | grep '^allowed' | sed 's/^allowed */  /' || true)
  if [ -n "$calls" ]; then
    echo "FAIL $t: calls through the FFI boundary (not inlined):"; echo "$calls"; status=1
  elif [ -n "$reads" ]; then
    echo "FAIL $t: array reads or sets left as calls (a texture LLVM did not inline):"; echo "$reads"; status=1
  elif [ -n "$barriers" ]; then
    echo "FAIL $t: black_box barriers inlined into Reussir functions:"; echo "$barriers"; status=1
  else
    echo "PASS  $t"
    [ -z "$allowed" ] || { echo "      allowed at cold call sites (Reussir issue 36, not patched):"; echo "$allowed"; }
  fi
done
[ $status -eq 0 ] && echo "PASS  ffi-inline-check"
exit $status
