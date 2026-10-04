#!/usr/bin/env bash
# lean-runtime's row cases through lean2rr. lean-runtime's row oracle
# (scripts/oracle/Oracle.lean: a Lean program that evaluates the functions of
# tests/cases/<area>/<area>.rows.toml on inputs read from stdin) is built
# with lean2rr, and lean-runtime's scripts/gen_rows.py --check compares every
# row's expected value (recorded from native Lean 4.34.0) with its answers.
# This checks the prelude's inline code and its glue around lean-runtime on
# lean-runtime's own rows. Nothing in the lean-runtime checkout is written.
#
#   tests/runtime/rows-check.sh [ROWS FILE...]   (default: every rows file)
#
# Environment: L2R_LEAN_RUNTIME (the lean-runtime checkout, default the
# submodule third_party/lean-runtime), L2R_TEST_BUILD (build directory,
# default tests/runtime/build), and those of scripts/l2r.py.
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
LR=${L2R_LEAN_RUNTIME:-$ROOT/third_party/lean-runtime}
if [ ! -f "$LR/Cargo.toml" ]; then
  echo "no lean-runtime at $LR: run \`git submodule update --init third_party/lean-runtime\` (or set L2R_LEAN_RUNTIME)" >&2
  exit 2
fi
if [ ! -f "$LR/scripts/oracle/Oracle.lean" ] || [ ! -f "$LR/scripts/gen_rows.py" ]; then
  echo "rows-check: $LR has no row oracle (scripts/oracle, scripts/gen_rows.py)" >&2
  exit 1
fi
OUT=${L2R_TEST_BUILD:-$HERE/build}/rows
mkdir -p "$OUT"
cp "$LR/scripts/oracle/Oracle.lean" "$OUT/Oracle.lean"
(cd "$OUT" && lean -o Oracle.olean Oracle.lean \
  && python3 "$ROOT/scripts/l2r.py" Oracle.lean -o oracle-l2r > build-l2r.log 2>&1) \
  || { echo "rows-check: building the oracle with lean2rr failed (see $OUT/build-l2r.log)"; exit 1; }
[ $# -gt 0 ] || set -- "$LR"/tests/cases/*/*.rows.toml
# gen_rows.py with its oracle replaced by the lean2rr build.
PYTHONDONTWRITEBYTECODE=1 python3 - "$LR/scripts" "$OUT/oracle-l2r" "$@" <<'PY'
import pathlib, sys
sys.path.insert(0, sys.argv[1])
import gen_rows
exe = pathlib.Path(sys.argv[2])
gen_rows.oracle_binary = lambda toolchain: ([], exe)
sys.argv = ["gen_rows.py", "--check", "--toolchain", "lean2rr", *sys.argv[3:]]
try:
    gen_rows.main()
except gen_rows.RowError as e:
    print(f"rows-check: {e}", file=sys.stderr)
    sys.exit(2)
print("rows-check: every row agrees")
PY
