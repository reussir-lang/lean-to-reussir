#!/usr/bin/env bash
# The optimization `prelude-liveness` (lean2rr/LeanToReussir/PreludePrune.lean)
# changes only the prelude part of the program text, and leaves most of the
# prelude's textures out of a small program. Translates RtIO.lean (files,
# streams, processes, strings, numbers; lean2rr only, `--emit rr`) with the
# pass and with `--disable-opt prelude-liveness`, and checks:
# - the two texts are equal from the line `// ---- generated types ----` on
#   (the generated part);
# - without the pass the text starts with the whole prelude, byte for byte;
# - with the pass it keeps at most half of the prelude's `#[ffi(import)]`
#   functions (each is one rustc run of rrc when its texture cache misses;
#   RtIO kept 86 of 493 when the pass came in), and says how many functions
#   it left out;
# - with the pass the prelude part (before that line) has no line that is a
#   `//` comment as a whole outside a texture (`[{ ... }]`), and its lines
#   but blank ones are lines of the prelude, in the prelude's order (nothing
#   is changed or added, a texture's comments stay).
# run.sh builds and runs every runtime test with the pass on (the default).
#   tests/runtime/prelude-liveness-check.sh
# Environment: as run.sh (L2R_LEAN2RR, L2R_TEST_BUILD, L2R_LEAN_TOOLCHAIN).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
LEAN2RR=${L2R_LEAN2RR:-$ROOT/lean2rr/.lake/build/bin/lean2rr}
PRELUDE=$ROOT/runtime/prelude.rr
OUT=${L2R_TEST_BUILD:-$HERE/build}/prelude-liveness-check
rm -rf "$OUT"; mkdir -p "$OUT"
cd "$OUT" || exit 2
status=0
fail() { echo "FAIL prelude-liveness: $1"; status=1; }
t=RtIO
cp "$HERE/$t.lean" .
lean -o "$t.olean" "$t.lean" > lean.log 2>&1 || { echo "FAIL prelude-liveness: lean (see $OUT/lean.log)"; exit 1; }
# translate OUT.rr [lean2rr flags]
translate() {
  local o=$1; shift
  LEAN_PATH="$OUT" L2R_SHIM_DIR="$ROOT/lean2rr/.lake/build/lib/lean" LEAN_STACK_SIZE_KB=1048576 \
    "$LEAN2RR" "$t" --root main --emit rr --prelude "$PRELUDE" -o "$o" "$@" > "$o.log" 2>&1
}
translate on.rr || { echo "FAIL prelude-liveness: lean2rr failed (see $OUT/on.rr.log)"; exit 1; }
translate off.rr --disable-opt prelude-liveness \
  || { echo "FAIL prelude-liveness: lean2rr failed (see $OUT/off.rr.log)"; exit 1; }
gen() { sed -n '/^\/\/ ---- generated types ----$/,$p' "$1"; }
gen on.rr > on.gen; gen off.rr > off.gen
[ -s on.gen ] || fail "no generated part in on.rr"
cmp -s on.gen off.gen || fail "the generated parts differ (diff $OUT/off.gen $OUT/on.gen)"
cmp -s <(head -c "$(stat -c %s "$PRELUDE")" off.rr) "$PRELUDE" \
  || fail "without the pass the text does not start with the whole prelude"
all=$(grep -c '^#\[ffi(import)\]$' "$PRELUDE")
kept=$(sed '/^\/\/ ---- generated types ----$/q' on.rr | grep -c '^#\[ffi(import)\]$')
echo "$t: the prelude's #[ffi(import)] functions kept: $kept of $all"
[ $((2 * kept)) -le "$all" ] || fail "$kept of the prelude's $all #[ffi(import)] functions kept (more than half)"
grep -q '^// lean2rr: [0-9]* functions of the prelude that this program does not use are left out' on.rr \
  || fail "on.rr does not say how many prelude functions it left out"
sed '/^\/\/ lean2rr: [0-9]* functions of the prelude/,$d' on.rr > on.prelude
python3 - "$PRELUDE" on.prelude > comments.log <<'PY' || fail "the prelude part of on.rr: $(head -1 comments.log) (see $OUT/comments.log)"
import sys
full = open(sys.argv[1]).read().split('\n')
kept = open(sys.argv[2]).read().split('\n')
depth, bad = 0, []
for i, l in enumerate(kept):
    if depth == 0 and l.lstrip().startswith('//'):
        bad.append(f'line {i + 1}: {l[:80]}')
    code = l.split('//')[0]
    depth += code.count('[{') - code.count('}]')
# Blank lines aside (the line before the count is one).
full = [l for l in full if l.strip()]
kept = [l for l in kept if l.strip()]
j = 0
for l in full:
    if j < len(kept) and l == kept[j]:
        j += 1
if bad:
    print(f'{len(bad)} whole-line comments outside textures, the first {bad[0]}')
    sys.exit(1)
if j < len(kept):
    print(f'line {j + 1} is not a line of the prelude in order: {kept[j][:80]}')
    sys.exit(1)
PY
[ $status -eq 0 ] && echo "PASS  prelude-liveness"
exit $status
