#!/usr/bin/env bash
# The one-word box (leanrt::any::LAny, the prelude's `LAny`), probed by a
# hand-written Reussir program (any-probe/probe.rr) before lean2rr
# generates it (the scenarios are listed below). The probe is
# appended to lean2rr's translation of any-probe/AnyHost.lean and called
# first in `main`; it is linked with an allocation tracker
# (any-probe/alloclive.c: -Wl,--wrap on mimalloc's allocation entry points
# and mi_free, a set of live blocks) and run on the initializers' thread
# with a 1 MiB stack, built with Reussir's default nullary-variant encoding
# and with the arch-independent one. Each scenario runs twice; the second
# run must give its expected result and free every block it allocates,
# exactly once (live blocks before = after, no free of a block that is not
# live). A third run unboxes at the wrong number and must end with Lean's
# internal panic (exit 1).
# Needs a Reussir with patch 38-a (reussir-bugs/38-tagged-top-bits.md);
# without it the program is killed by SIGSEGV at the first copy of a
# boxed pointer. Scenarios: records, enums with nullary variants (at
# indices 0, 1, 2; all-nullary), function values with closures (one
# capturing a box), strings, big numbers, f64/u64 cells, a [value] record
# in a cell and one holding a box, an array of boxes (copy on write), a
# reference record, an LCell, chains of 10^6 nested boxes, boxes in records
# freed by drop glue, the shared check, box(0) at every kind of type, the
# generic textures at scalars and at leanrt's kinds, the record-address
# texture at a box, and the order of observable releases (o1, o4, o5:
# native Lean's orders, from any-probe/Order.lean built natively).
#   tests/runtime/any-probe.sh
# Environment: L2R_REUSSIR, L2R_LEAN2RR, L2R_TEST_BUILD, L2R_LEAN_TOOLCHAIN
# (as run.sh).
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
OUT=${L2R_TEST_BUILD:-$HERE/build}/any-probe
mkdir -p "$OUT"
cd "$OUT"
LEAN2RR=${L2R_LEAN2RR:-$ROOT/lean2rr/.lake/build/bin/lean2rr}
cp "$HERE/any-probe/AnyHost.lean" .
lean -o AnyHost.olean AnyHost.lean
# The whole prelude (`--disable-opt prelude-liveness`): the probe calls
# prelude functions that the host does not use.
LEAN_PATH=. L2R_SHIM_DIR=${L2R_SHIM_DIR:-$(dirname "$LEAN2RR")/../lib/lean} "$LEAN2RR" AnyHost --root main --emit rr \
  --prelude "$ROOT/runtime/prelude.rr" -o host.rr --disable-opt prelude-liveness
python3 - "$HERE/any-probe/probe.rr" <<'PY'
import sys
s = open('host.rr').read()
old = "let se : u64 = l2r_std_enter_if(mt);\n"
assert s.count(old) == 1, "no l2r_std_enter_if in main's body"
s = s.replace(old, old + "let probe_failures : u64 = anyprobe_main();\n")
# The host installs the releases of its own payloads before main
# (l2r_any_init_c), the probe those of its numbers first (probe_install).
assert s.count('extern "C" trampoline "l2r_any_init_c" = l2r_any_init;') == 1, "no l2r_any_init in the host"
open('prog.rr', 'w').write(s + open(sys.argv[1]).read())
PY
"${CC:-cc}" -O2 -fPIC -c "$HERE/any-probe/alloclive.c" -o alloclive.o
WRAP=-Wl
for s in mi_malloc mi_malloc_small mi_zalloc mi_zalloc_small mi_calloc mi_mallocn mi_malloc_aligned \
         mi_zalloc_aligned mi_realloc mi_realloc_aligned mi_free; do WRAP="$WRAP,--wrap=$s"; done
# build OUT [RRC FLAGS...]: scripts/l2r.py's build of prog.rr (leanrt,
# lean-runtime, GMP, lean2rr's rrc flags), plus the tracker.
build() {
python3 - "$ROOT/scripts" "$WRAP" "$@" <<'PY'
import os, subprocess, sys, tempfile
sys.path.insert(0, sys.argv[1]); import l2r
env = dict(os.environ)
env.setdefault("REUSSIR_FFI_CACHE_DIR", str(l2r.LEANRT_OUT / "polyffi-cache"))
rlib, lr = l2r.build_leanrt()
rt, deps = l2r.rt_dirs()
tl = l2r.run([str(l2r.RUSTC), "--print", "target-libdir"]).stdout.strip()
cmd = ([str(l2r.REUSSIR / "build" / "bin" / "rrc"), os.path.abspath("prog.rr"), "-o", os.path.abspath(sys.argv[3]),
        "--emit", "executable", "-O", "aggressive", "--polyffi-rust-path", str(l2r.rustc_wrapper(rlib, lr)),
        "--polyffi-libdir", str(rt), "--polyffi-libdir", str(deps), "--polyffi-libdir", tl,
        "--polyffi-libdir", str(rlib.parent), "--link-lib", str(rlib)]
       + [a for r in lr.rlibs for a in ("--link-lib", str(r))]
       + ["--link-lib", str(l2r.gmp_archive()), "--no-pack-record-members", "--no-closure-wpd",
          "--relocation-mode", "pic", "--reuse-across-call",
          "--link-arg=" + sys.argv[2], "--link-arg=" + os.path.abspath("alloclive.o")] + sys.argv[4:])
with tempfile.TemporaryDirectory(dir=".") as tmp:
    sys.exit(subprocess.run(cmd, env=env, cwd=tmp).returncode)
PY
}
SCENARIOS=19
status=0
# check NAME: run probe-NAME; every scenario's second run must pass.
check() {
  ( ulimit -s 1024; LEAN_MAIN_USE_THREAD=0 ./"probe-$1" ) > "probe-$1.out" 2>&1 || { echo "FAIL $1: the probe exited with $?"; status=1; }
  grep -E '^(PASS|FAIL|NOTE) ' "probe-$1.out" | sed "s/^/$1: /" || true
  local n
  n=$(grep -c '^PASS .*(run 2)' "probe-$1.out" || true)
  if [ "$n" != $SCENARIOS ]; then echo "FAIL $1: $((SCENARIOS - n)) of $SCENARIOS scenarios failed their second run"; status=1; fi
  grep -q '^host$' "probe-$1.out" || { echo "FAIL $1: the host program did not run after the probe"; status=1; }
}
# Reussir's default nullary-variant encoding (tbi on aarch64), and the
# arch-independent one (immortal dummy boxes).
build probe-default
check default
build probe-immortal --nullary-variant-encoding arch-independent
check immortal
# An unboxing at the wrong number is Lean's internal panic (exit 1), never
# a read.
code=0
( ulimit -s 1024; ANY_PROBE_MISMATCH=1 LEAN_MAIN_USE_THREAD=0 ./probe-default ) > probe-mismatch.out 2>&1 || code=$?
if [ $code = 1 ] && grep -q 'INTERNAL PANIC' probe-mismatch.out; then echo "mismatch: exit 1, $(grep -m1 'INTERNAL PANIC' probe-mismatch.out)"
else echo "FAIL mismatch: exit $code, expected 1 with Lean's internal panic"; status=1; fi
# box(0) through the generic unbox at a record type: a message that names
# the split rule, then the internal panic.
code=0
( ulimit -s 1024; ANY_PROBE_UNIT_AT_RECORD=1 LEAN_MAIN_USE_THREAD=0 ./probe-default ) > probe-unit-at-record.out 2>&1 || code=$?
if [ $code = 1 ] && grep -q 'a generated unbox must split immediates first' probe-unit-at-record.out; then echo "box(0) at a record by l2r_any_as: exit 1 with the split rule's message"
else echo "FAIL box(0) at a record by l2r_any_as: exit $code, expected 1 with the split rule's message"; status=1; fi
# The order scenarios' expectations are native Lean's: any-probe/Order.lean,
# built natively, must print them.
cp "$HERE/any-probe/Order.lean" .
lean -c Order.c Order.lean && leanc -O2 Order.c -o order-native
./order-native > order-native.out 2>&1 || true
for want in "o1 box of H2(A, B) dropped = BA" "o4 chain C(1, C(2, C(3))) dropped = 321" "o5 IO.Ref set over a box of H2(A, B) = BA"; do
  grep -qF "native $want" order-native.out || { echo "FAIL native Lean does not print '$want' (see order-native.out)"; status=1; }
done
[ $status = 0 ] && echo "any-probe: all $SCENARIOS scenarios pass under both nullary encodings (the release orders as native Lean's); a mismatch panics"
exit $status
