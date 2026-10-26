#!/usr/bin/env bash
# Translation-level checks of `Nat` and `Int` as Reussir's built-in integers
# (rcgmp; `lean2rr --emit rr`, no Reussir build). (Until 2026-10-26 it also
# checked that the leanrt representation had none of these shapes.)
# `boxed-consts` under rcgmp, on tests/runtime/RtNatBoxedConsts (`Nat`
# and `Int` constants at the edges of the box's immediates, stored in
# lists): only the constants whose box is a cell (`2^63 : Nat`; `2^31`,
# `3000000000`, `2^32 - 1`, `2^62` and `-2^62 - 1 : Int`) get a once-cell
# `l2r_boxed_N`; the others are boxed in line (`constIsImmediate`; review of
# step D: `k5 : Nat := 5` had one).
# Also the reads at an index word (lean2rr's `bindReadIndex`) on
# tests/runtime/RtNatIdxWord, with its .opts (`typed-arrays` and
# `compact-arrays` off): under rcgmp each of the ten `_w` reads of the prelude is
# called (`Array` fget/get! and their reads at a type, `ByteArray`
# fget/get!, `String.Pos.Raw` get, get', next', atEnd), each call's index
# is the variable of the `let ixN : u64 = l2r_nat_index(...)` on the line
# before it, and the generated code calls none of the reads at a `Nat`
# that have a twin (RtNatIdxWord passes run.sh without the lowering too, so
# only this pins it).
# Also the boxes of big `Nat` and `Int` values (lean2rr's `natIntBoxFns?`)
# on tests/runtime/RtNatBoxBig: under rcgmp the generated code boxes through
# `l2r_any_of_nat`/`l2r_any_of_int`, whose heap path is the owned
# `l2r_any_of_big<Nat>`/`<Int>` (the cell takes the handle; leanrt's
# `box_owned`). (Until 2026-10-25 this script also checked guard mode, a
# lowering for measurements, chosen by leaving out `--rcgmp-type-args`, that
# kept `Nat` and `Int` out of type arguments, and its check
# `IntBackendCheck`; it ran on a Reussir with patch R2 and did not use it.)
# Also the index after an access that a proof keeps in range (lean2rr's
# `rebindIndex`, Lower/Code) on tests/runtime/RtNatIdxRebind, translated
# with the default passes and with `compact-arrays` off (its arrays of
# `UInt32` then hold boxes, read at a type: `lean_array_fget_as_w`): under
# rcgmp each `let ibN : Nat = l2r_nat_of_index(ixM);` comes right after the
# access at `ixM` (one of the `_w` accesses that return only below the
# size: `Array` fget, its read at a type, `ByteArray` fget, `Array` fset,
# `ByteArray` fset, `Array` fswap), the variable whose word `ixM` is does
# not occur again in the rest of the enclosing block (nested blocks
# included), each kind has a rebinding (the read at a type in the second
# translation), and the generated code calls no update at a `Nat` (`fset`,
# `fswap`, `ByteArray` `fset`: they have twins at index words). The
# outputs are the same either way (RtNatIdxRebind passes run.sh without
# the rebinding), so only this pins it.
#   tests/runtime/int-backend-check.sh
# Environment: as determinism-check.sh (L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
LEAN2RR=${L2R_LEAN2RR:-$ROOT/lean2rr/.lake/build/bin/lean2rr}
BASE=${L2R_TEST_BUILD:-$HERE/build}/int-backend-check
rm -rf "$BASE"
# translate OUT.rr [lean2rr flags...]
translate() {
  local o=$1; shift
  (cd "$OUT" && LEAN_PATH="$OUT" L2R_SHIM_DIR="$ROOT/lean2rr/.lake/build/lib/lean" LEAN_STACK_SIZE_KB=1048576 \
     "$LEAN2RR" "$P" --emit rr --prelude "$ROOT/runtime/prelude.rr" -o "$o" "$@") > "$o.log" 2>&1
}
status=0
# The constants that `boxed-consts` boxes once (the constants read by the
# `l2r_boxed_N_init` functions of OUT.rr).
boxed() { grep -A3 '^fn l2r_boxed_[0-9]*_init' "$1" | grep -o 'l_k[A-Za-z0-9]*___l2r_0_' | LC_ALL=C sort | tr '\n' ' '; }
P=RtNatBoxedConsts
OUT=$BASE/$P
mkdir -p "$OUT"
cp "$HERE/$P.lean" "$OUT/"
if ! (cd "$OUT" && lean -o "$P.olean" "$P.lean") > "$OUT/lean.log" 2>&1; then
  echo "FAIL $P: lean failed (see $OUT/lean.log)"; status=1
else
  # Cells: the Nat 2^63; the Ints 2^31, 3000000000, 2^32 - 1 ([2^31, 2^32)),
  # 2^62 and -2^62 - 1. Immediates: the other Nats; the Ints -2^31 and
  # 2^31 - 1 (int32), 2^32, 2^62 - 1, -2^31 - 1, -3000000000 and -2^62
  # ([2^32, 2^62) and [-2^62, -2^31)).
  want="l_kB___l2r_0_ l_kBn___l2r_0_ l_kI31p___l2r_0_ l_kM___l2r_0_ l_kN64___l2r_0_ l_kU32___l2r_0_ "
  if ! translate "$OUT/rcgmp.rr"; then
    echo "FAIL $P: did not translate $P (see $OUT/rcgmp.rr.log)"; status=1
  elif [ "$(boxed "$OUT/rcgmp.rr")" != "$want" ]; then
    echo "FAIL $P: boxed once: $(boxed "$OUT/rcgmp.rr")(expected $want)"; status=1
  else
    echo "ok   $P: once-cells only for the constants whose box is a cell"
  fi
fi
# The reads at an index word. idxword OUT.rr BACKEND: the shape of
# RtNatIdxWord's generated code (after `// ---- generated types ----`).
idxword() {
  python3 - "$1" "$2" <<'EOF'
import re, sys
rr, backend = sys.argv[1], sys.argv[2]
text = open(rr).read()
parts = text.split("// ---- generated types ----\n", 1)
if len(parts) != 2:
    print("no generated part"); sys.exit(1)
gen = parts[1]
twins = ["lean_array_fget_w", "lean_array_get_w", "lean_array_fget_as_w", "lean_array_get_as_w",
         "lean_byte_array_fget_w", "lean_byte_array_get_w", "lean_string_utf8_get_w",
         "lean_string_utf8_get_fast_w", "lean_string_utf8_next_fast_w", "lean_string_utf8_at_end_w"]
call = re.compile(r"\b(" + "|".join(twins) + r")\b(<[^()]*>)?\(")
errs = []
if True:
    # The reads at a Nat that have a twin (lean2rr's wordReadSym?, and the
    # reads at a type of the array reads).
    nat = re.compile(r"\b(lean_array_(fget|get)(_borrowed)?(_as)?<|lean_byte_array_(fget|get)\(|"
                     r"lean_string_utf8_(get|get_fast|next_fast|at_end)\()")
    seen = dict.fromkeys(twins, 0)
    lines = gen.split("\n")
    for i, l in enumerate(lines):
        m = nat.search(l)
        if m:
            errs.append(f"a read at a Nat: {l.strip()}")
        for m in call.finditer(l):
            seen[m.group(1)] += 1
            # The arguments, to the matching parenthesis; the index is the last.
            depth, j = 1, m.end()
            while j < len(l) and depth:
                depth += {"(": 1, ")": -1}.get(l[j], 0); j += 1
            last = l[m.end():j - 1].split(",")[-1].strip()
            prev = lines[i - 1].strip() if i else ""
            if not re.fullmatch(r"ix\d+", last) or not prev.startswith(f"let {last} : u64 = l2r_nat_index("):
                errs.append(f"{m.group(1)} without the index word on the line before: {prev} / {l.strip()}")
    errs += [f"no call of {t}" for t, k in seen.items() if k == 0]
    if not errs:
        print(f"{sum(seen.values())} reads at an index word, each after its l2r_nat_index")
for e in errs:
    print(e)
sys.exit(1 if errs else 0)
EOF
}
P=RtNatIdxWord
OUT=$BASE/$P
mkdir -p "$OUT"
cp "$HERE/$P.lean" "$OUT/"
opts=()
for o in $(tr ', \n' '   ' < "$HERE/$P.opts"); do opts+=(--disable-opt "$o"); done
if ! (cd "$OUT" && lean -o "$P.olean" "$P.lean") > "$OUT/lean.log" 2>&1; then
  echo "FAIL $P: lean failed (see $OUT/lean.log)"; status=1
else
  for be in rcgmp; do
    if ! translate "$OUT/$be.rr" "${opts[@]}"; then
      echo "FAIL $P: did not translate $P (see $OUT/$be.rr.log)"; status=1
    elif ! idxword "$OUT/$be.rr" "$be" > "$OUT/$be.shape" 2>&1; then
      echo "FAIL $P: the reads at an index word, $(wc -l < "$OUT/$be.shape") problems (see $OUT/$be.shape), the first and last:"
      awk -v n="$(wc -l < "$OUT/$be.shape")" 'NR <= 3 || NR > n - 3 { print "  " $0 }' "$OUT/$be.shape"; status=1
    else
      echo "ok   $P: $(cat "$OUT/$be.shape"), no read at a Nat with a twin"
    fi
  done
fi
# The boxes of big values: through the owned box.
# calls FILE NAME: whether the generated part of FILE calls NAME.
calls() { awk 'f; /^\/\/ ---- generated types ----$/ { f = 1 }' "$1" | grep -q "\b$2("; }
P=RtNatBoxBig
OUT=$BASE/$P
mkdir -p "$OUT"
cp "$HERE/$P.lean" "$OUT/"
if ! (cd "$OUT" && lean -o "$P.olean" "$P.lean") > "$OUT/lean.log" 2>&1; then
  echo "FAIL $P: lean failed (see $OUT/lean.log)"; status=1
elif ! translate "$OUT/rcgmp.rr"; then
  echo "FAIL $P: did not translate $P (see $OUT/rcgmp.rr.log)"; status=1
elif ! calls "$OUT/rcgmp.rr" l2r_any_of_nat || ! calls "$OUT/rcgmp.rr" l2r_any_of_int \
    || ! grep -q 'l2r_any_of_big<Nat>(' "$OUT/rcgmp.rr" || ! grep -q 'l2r_any_of_big<Int>(' "$OUT/rcgmp.rr"; then
  echo "FAIL $P: expected boxes through l2r_any_of_nat/_int and their owned l2r_any_of_big<Nat>/<Int> (see $OUT/rcgmp.rr)"; status=1
else
  echo "ok   $P: big values boxed through the owned l2r_any_of_big"
fi
# The index after a proved access. rebind OUT.rr BACKEND KINDS: the shape
# of RtNatIdxRebind's generated code; KINDS, the accesses (comma-separated)
# that must each have a rebinding.
rebind() {
  python3 - "$1" "$2" "$3" <<'EOF'
import re, sys
rr, backend, kinds = sys.argv[1], sys.argv[2], sys.argv[3].split(",")
text = open(rr).read()
parts = text.split("// ---- generated types ----\n", 1)
if len(parts) != 2:
    print("no generated part"); sys.exit(1)
gen = parts[1]
bounded = ["lean_array_fget_w", "lean_array_fget_as_w", "lean_byte_array_fget_w",
           "lean_array_fset_w", "lean_byte_array_fset_w", "lean_array_fswap_w"]
updates = ["lean_array_fset_w", "lean_byte_array_fset_w", "lean_array_fswap_w"]
errs = []
if True:
    lines = gen.split("\n")
    for l in lines:
        if re.search(r"\b(lean_array_fset<|lean_array_fswap<|lean_byte_array_fset\()", l):
            errs.append(f"an update at a Nat: {l.strip()}")
    word_of = {}
    rebinds = dict.fromkeys(bounded, 0)
    for i, l in enumerate(lines):
        m = re.match(r"\s*let (ix\d+) : u64 = l2r_nat_index\((\w+)\);", l)
        if m:
            word_of[m.group(1)] = m.group(2)
        m = re.match(r"\s*let (ib\d+) : Nat = l2r_nat_of_index\((ix\d+)\);$", l)
        if not m:
            continue
        ib, ix = m.groups()
        # The access: the nearest line before that is not a rebinding (a
        # block-valued `let` from its first line).
        j = i - 1
        while j >= 0 and re.match(r"\s*let ib\d+ : Nat = l2r_nat_of_index\(", lines[j]):
            j -= 1
        acc = lines[j] if j >= 0 else ""
        if acc.strip() == "};":
            d, k = 0, j
            while k >= 0:
                d += lines[k].count("}") - lines[k].count("{")
                if d <= 0:
                    break
                k -= 1
            acc = " ".join(x.strip() for x in lines[max(k, 0):j + 1])
        calls = [b for b in bounded if re.search(r"\b" + b + r"\b(<[^()]*>)?\([^;]*\b" + ix + r"\b", acc)]
        if not calls:
            errs.append(f"{ib} not right after an access at {ix}: {acc.strip()}")
            continue
        rebinds[calls[0]] += 1
        v = word_of.get(ix)
        if v is None:
            errs.append(f"{ib}: no `let {ix} : u64 = l2r_nat_index(...)` before it")
            continue
        # The rest of the enclosing block, nested blocks included, reads
        # the rebinding.
        depth = 0
        for k in range(i + 1, len(lines)):
            s = lines[k]
            if depth == 0 and s.strip().startswith("}"):
                break
            if re.search(r"\b" + re.escape(v) + r"\b", s):
                errs.append(f"{v} used after {ib} in its block: {s.strip()}")
                break
            depth += s.count("{") - s.count("}")
            if depth < 0:
                break
    for k in kinds:
        if rebinds[k] == 0:
            errs.append(f"no rebinding after {k}")
    if not errs:
        print(f"{sum(rebinds.values())} indices rebound right after their access ("
              + ", ".join(f"{k} {n}" for k, n in rebinds.items() if n) + ")")
for e in errs:
    print(e)
sys.exit(1 if errs else 0)
EOF
}
P=RtNatIdxRebind
OUT=$BASE/$P
mkdir -p "$OUT"
cp "$HERE/$P.lean" "$OUT/"
if ! (cd "$OUT" && lean -o "$P.olean" "$P.lean") > "$OUT/lean.log" 2>&1; then
  echo "FAIL $P: lean failed (see $OUT/lean.log)"; status=1
else
  # NAME BACKEND KINDS FLAGS...: the default passes, and `compact-arrays` off.
  for run in "rcgmp rcgmp lean_array_fget_w,lean_byte_array_fget_w,lean_array_fset_w,lean_byte_array_fset_w,lean_array_fswap_w" \
             "rcgmp-boxed rcgmp lean_array_fget_as_w,lean_array_fswap_w --disable-opt compact-arrays"; do
    read -r name be kinds flags <<< "$run"
    if ! translate "$OUT/$name.rr" $flags; then
      echo "FAIL $P: $name did not translate $P (see $OUT/$name.rr.log)"; status=1
    elif ! rebind "$OUT/$name.rr" "$be" "$kinds" > "$OUT/$name.shape" 2>&1; then
      echo "FAIL $P $name: the indices after a proved access, $(wc -l < "$OUT/$name.shape") problems (see $OUT/$name.shape), the first and last:"
      awk -v n="$(wc -l < "$OUT/$name.shape")" 'NR <= 3 || NR > n - 3 { print "  " $0 }' "$OUT/$name.shape"; status=1
    else
      echo "ok   $P $name: $(cat "$OUT/$name.shape"), no update at a Nat"
    fi
  done
fi
[ $status -eq 0 ] && echo "PASS  int-backend-check"
exit $status
