#!/usr/bin/env bash
# Loader tests: which program modules lean2rr accepts (lean2rr/LeanToReussir/
# Env.lean, translation plan §10 "Module names"). lean2rr takes the modules
# named Init.*, Std.*, Lean.*, Lake.* for Lean's library and L2RShim.* for
# its own shim, so it must reject a program module named like them, and
# accept Lean's library however it is reached (a symbolic link, hard links,
# from a working directory whose lean-toolchain names another Lean). It must
# also stop when its shim directory has no shim.
# Translation only (`lean2rr --emit mono`): a few seconds per case.
#
#   tests/env/run.sh
#
# Environment: L2R_LEAN2RR (the lean2rr binary; default: this checkout's
# build), L2R_TEST_BUILD (scratch directory, default tests/env/build).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
LEAN2RR=${L2R_LEAN2RR:-$ROOT/lean2rr/.lake/build/bin/lean2rr}
export L2R_SHIM_DIR=$ROOT/lean2rr/.lake/build/lib/lean
W=${L2R_TEST_BUILD:-$HERE/build}
rm -rf "$W"; mkdir -p "$W/src"
LIB=$(lean --print-prefix)/lib/lean

# The program modules (compiled natively, in dependency order).
# One directory per program (a directory `L2RShim` on the search path
# replaces lean2rr's shim for every program, also one that does not import it).
mkdir -p "$W/shimdir/L2RShim" "$W/shimfile" "$W/src/Lean"
cd "$W/src" || exit 1
echo 'def main : IO Unit := IO.println "plain"' > Plain.lean
echo 'def leanFoo (n : Nat) : Nat := n + 1' > Lean/L2rFoo.lean
printf 'import Lean.L2rFoo\ndef main : IO Unit := IO.println s!"{leanFoo 1}"\n' > MLean.lean
echo 'def shimFoo (n : Nat) : Nat := n + 2' > ../shimdir/L2RShim/Evil.lean
printf 'import L2RShim.Evil\ndef main : IO Unit := IO.println s!"{shimFoo 1}"\n' > ../shimdir/MShimDir.lean
echo 'def shimBar (n : Nat) : Nat := n + 3' > ../shimfile/L2RShim.lean
printf 'import L2RShim\ndef main : IO Unit := IO.println s!"{shimBar 1}"\n' > ../shimfile/MShimFile.lean
for f in src/Plain src/Lean/L2rFoo src/MLean shimdir/L2RShim/Evil shimdir/MShimDir shimfile/L2RShim shimfile/MShimFile; do
  d=${f%%/*}; m=${f#*/}
  (cd "$W/$d" && LEAN_PATH=$W/$d lean -o "$m.olean" "$m.lean") || { echo "native build of $f failed"; exit 1; }
done

# Lean's library reached through a symbolic link, through hard links, and
# through hard links with one file of a module (its `.olean`, or the
# `.olean.private` part lean2rr reads) replaced by a different file of the
# same size.
# (Hard links need the build directory on the toolchain's file system.)
ln -s "$LIB" "$W/symlink"
links=yes
for d in hardlinks altered altered-private; do
  cp -al "$LIB" "$W/$d" 2> /dev/null || links=no
done
if [ $links = yes ]; then
  for f in altered/Init/Data/Repr.olean altered-private/Init/Data/Repr.olean.private; do
    rm "$W/$f"
    python3 -c 'import sys; b = bytearray(open(sys.argv[1], "rb").read()); b[-1] ^= 1; open(sys.argv[2], "wb").write(b)' \
      "$LIB/${f#*/}" "$W/$f"
  done
fi
# lean2rr moved away from its build directory (a link, else a copy).
mkdir -p "$W/moved/bin"
ln "$LEAN2RR" "$W/moved/bin/lean2rr" 2> /dev/null || cp "$LEAN2RR" "$W/moved/bin/lean2rr"
# A working directory whose lean-toolchain names another Lean.
mkdir -p "$W/othertc" && echo "leanprover/lean4:v4.34.0" > "$W/othertc/lean-toolchain"

pass=0; fail=0
# [CHECK_BIN=lean2rr] check NAME accept|reject PATTERN DIR LEAN_PATH MODULE [ENV-ARGS...]
# (ENV-ARGS: for env, e.g. VAR=VALUE or -u VAR)
check() {
  local name=$1 want=$2 pat=$3 dir=$4 lp=$5 mod=$6 out code
  shift 6
  out=$(cd "$dir" && env "$@" LEAN_PATH="$lp" timeout 600 "${CHECK_BIN:-$LEAN2RR}" "$mod" --emit mono \
          -o /dev/null 2>&1)
  code=$?
  if { [ "$want" = accept ] && [ $code -eq 0 ]; } ||
     { [ "$want" = reject ] && [ $code -ne 0 ] && grep -q -- "$pat" <<< "$out"; }; then
    pass=$((pass + 1)); echo "PASS  $name"
  else
    fail=$((fail + 1)); echo "FAIL  $name (exit $code, wanted $want): $(head -c 600 <<< "$out")"
  fi
}
S=$W/src
check plain              accept "" "$S" "$S" Plain
check lean-named-module  reject "module Lean.L2rFoo .* is named like a module of Lean's library" "$S" "$S" MLean
check shim-named-dir     reject "holds program modules named L2RShim" "$W/shimdir" "$W/shimdir" MShimDir
check shim-named-module  reject "holds program modules named L2RShim" "$W/shimfile" "$W/shimfile" MShimFile
check lib-symlink        accept "" "$S" "$W/symlink:$S" Plain
if [ $links = yes ]; then
  check lib-hardlinks    accept "" "$S" "$W/hardlinks:$S" Plain
  check lib-altered      reject "module Init.Data.Repr .* but differs from it in .*/Init/Data/Repr.olean:" \
    "$S" "$W/altered:$S" Plain
  check lib-altered-private reject "module Init.Data.Repr .* but differs from it in .*/Repr.olean.private" \
    "$S" "$W/altered-private:$S" Plain
else
  echo "SKIP  lib-hardlinks, lib-altered, lib-altered-private (no hard links to $LIB from $W)"
fi
check other-toolchain    accept "" "$W/othertc" "$LIB:$S" Plain
check other-toolchain-nolib accept "" "$W/othertc" "$S" Plain
check shim-default       accept "" "$S" "$S" Plain -u L2R_SHIM_DIR
check shim-dir-missing   reject "shim library (L2RShim.olean) is not in $W/nosuchdir (L2R_SHIM_DIR=" "$S" "$S" Plain \
  L2R_SHIM_DIR="$W/nosuchdir"
check shim-dir-empty     reject "shim library (L2RShim.olean) is not in  (L2R_SHIM_DIR=''" "$S" "$S" Plain L2R_SHIM_DIR=
CHECK_BIN=$W/moved/bin/lean2rr check shim-moved-binary reject \
  "shim library (L2RShim.olean) is not in .*moved/lib/lean (L2R_SHIM_DIR is unset" "$S" "$S" Plain \
  -u L2R_SHIM_DIR
CHECK_BIN=$W/moved/bin/lean2rr check shim-moved-binary-dir accept "" "$S" "$S" Plain
echo "passed $pass, failed $fail"
[ $fail -eq 0 ]
