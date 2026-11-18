#!/usr/bin/env bash
# rrc's texture cache never gives a program a texture that was compiled
# against another build of leanrt, and an unchanged leanrt keeps its
# entries.
#
# rrc keeps the bitcode of each compiled texture in a store and keys an
# entry by the request: rustc's path, the texture's source, rustc's options
# and the paths of the library directories. The bytes of the libraries are
# not in the key, and scripts/l2r.py rebuilds libleanrt.rlib in place. So
# the driver names leanrt's build in the rustc script it gives rrc, whose
# name is a hash of its text (l2r.py: rustc_wrapper, rrc_env). This check
# fails when that link is broken: the program would then run old inlined
# leanrt code (or read a field at an old offset) with no error.
#
# The check builds one program four times with one cache directory, in a
# copy of the driver and the runtime sources (scripts/, runtime/prelude.rr,
# runtime/leanrt/src; nothing in the checkout is changed). The program
# prints `String.length` of its argument; leanrt's `string::length` is
# `#[inline(always)]`, so its code is in the texture's bitcode, not in the
# rlib that is linked.
#   1. the sources as they are: the program prints 3;
#   2. the same again: the store has no new entry (every texture was found);
#   3. `string::length` answers 1000 more: the program must print 1003 (a
#      stale texture prints 3), and the store has new entries;
#   4. the first sources again: the program prints 3, and the store has no
#      new entry (the entries of step 1 are found again).
# Cost: one cargo build of lean-runtime and three rustc builds of leanrt in
# the copy's own build directory, and the textures of a small program twice.
#   tests/runtime/texture-cache-check.sh
# Environment: as run.sh (L2R_REUSSIR, L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN, L2R_LEAN_RUNTIME, L2R_RUSTC).
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
OUT=${L2R_TEST_BUILD:-$HERE/build}/texture-cache-check
rm -rf "$OUT"
mkdir -p "$OUT"
cd "$OUT"
# The copy: the driver takes the runtime sources and its build directory
# from its own checkout (the directory above scripts/). lean2rr (the binary,
# the shim, the toolchain file) and lean-runtime are the checkout's.
T=$OUT/tree
mkdir -p "$T/runtime/leanrt" "$T/third_party"
cp -r "$ROOT/scripts" "$T/scripts"
cp "$ROOT/runtime/prelude.rr" "$T/runtime/"
cp -r "$ROOT/runtime/leanrt/src" "$T/runtime/leanrt/src"
ln -s "$ROOT/lean2rr" "$T/lean2rr"
export L2R_REUSSIR=${L2R_REUSSIR:-$ROOT/reussir}
export L2R_LEAN2RR=${L2R_LEAN2RR:-$ROOT/lean2rr/.lake/build/bin/lean2rr}
export L2R_LEAN_RUNTIME=${L2R_LEAN_RUNTIME:-$ROOT/third_party/lean-runtime}
export L2R_POLYFFI_CACHE=$OUT/cache
cat > TexCache.lean <<'EOF'
def main (args : List String) : IO Unit := do
  for a in args do
    IO.println a.length
EOF
lean -o TexCache.olean TexCache.lean
SRC=$T/runtime/leanrt/src/string.rs
cp "$SRC" string.rs.orig
grep -q '^    unsafe { (\*s\.0)\.chars }$' "$SRC" \
  || { echo "FAIL the check does not find string::length's body in $SRC (update the check)"; exit 1; }
# The number of bitcode entries in the store.
entries() {
  python3 -c 'import sqlite3, sys
db = sqlite3.connect("file:" + sys.argv[1] + "?mode=ro", uri=True)
print(db.execute("select count(*) from entries where payload is not null").fetchone()[0])' "$OUT/cache/rrc/cache.db"
}
status=0
# step N WANT: build with the copy's sources, run, compare the output.
step() {
  python3 "$T/scripts/l2r.py" TexCache --lean-path "$OUT" -o "$OUT/prog$1" > "build$1.log" 2>&1 \
    || { echo "FAIL step $1: build failed (see $OUT/build$1.log)"; exit 1; }
  got=$("./prog$1" abc)
  if [ "$got" != "$2" ]; then echo "FAIL step $1: the program prints $got, expected $2"; status=1; fi
}
step 1 3
n1=$(entries)
[ "$n1" -gt 0 ] || { echo "FAIL step 1: the store $OUT/cache/rrc/cache.db has no entry (is the cache in use?)"; status=1; }
step 2 3
n2=$(entries)
[ "$n2" = "$n1" ] || { echo "FAIL step 2: $((n2 - n1)) new entries for an unchanged runtime ($n1 before)"; status=1; }
sed -i 's|^    unsafe { (\*s\.0)\.chars }$|    unsafe { (*s.0).chars + 1000 }|' "$SRC"
step 3 1003
n3=$(entries)
[ "$n3" -gt "$n2" ] || { echo "FAIL step 3: no new entry after a change of leanrt"; status=1; }
cp string.rs.orig "$SRC"
step 4 3
n4=$(entries)
[ "$n4" = "$n3" ] || { echo "FAIL step 4: $((n4 - n3)) new entries for a runtime that was built before"; status=1; }
[ -e "$HOME/.cache/rrc" ] && [ "$HOME/.cache/rrc" -nt "$OUT/TexCache.olean" ] && [ -z "${L2R_TEXCACHE_QUIET:-}" ] \
  && echo "note: ~/.cache/rrc changed during the check (another rrc of this user, or the driver's cache directory is not in use)"
[ $status = 0 ] && echo "texture-cache-check: a changed leanrt gets new textures ($n1 entries, then $n3), an unchanged one keeps its entries"
exit $status
