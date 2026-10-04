#!/usr/bin/env bash
# lean-runtime's row cases through lean2rr. lean-runtime's row oracle
# (scripts/oracle/Oracle.lean: a Lean program that evaluates the functions of
# tests/cases/<area>/<area>.rows.toml on inputs read from stdin) is built
# with lean2rr, and its answers are compared, with lean-runtime's
# scripts/gen_rows.py (`run_oracle`, `apply`), with every row's expected
# outcome: native Lean 4.34.0's (a value, a panic's text and default, or the
# end of the process), except for the rows whose `deviations` name an
# `LB-nn` of lean-runtime's docs/lean-bugs.md (a Lean runtime bug or limit
# that neither translator reproduces), whose `expected` is the Lean
# definition's result (native's own outcome is in `native`, not compared).
# A row whose `deviations` name a difference of lean2rr's own (`lean2rr =`
# something other than an `LB-nn`) is listed, not failed. This checks the
# prelude's inline code and its glue around lean-runtime (hashes, strings,
# floats, fixed-width integers, libm, Nat and Int, arrays, panics, the text
# of numbers) on lean-runtime's own rows. Nothing in the lean-runtime
# checkout is written.
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
# Compared: the fields of the outcome. `apply` treats every row as one that
# expects the toolchain's own outcome: an LB-nn row's `expected` is then
# compared too (lean2rr gives the definition's result there), and `native`
# is kept as it is.
fields = ("expected", "default", "stderr", "bits", "ends")
gen_rows.shared_deviation = lambda row: False
def own(row):
    d = row.get("deviations", {}).get("lean2rr")
    return d is not None and not str(d).startswith("LB-")
failed = 0
try:
    for path in map(pathlib.Path, sys.argv[3:]):
        header, rows = gen_rows.read_rows(path)
        results = gen_rows.run_oracle("lean2rr", rows)
        bad = [(r["id"], res["value"]) for r, res in zip(rows, results) if res.get("value", "").startswith("!")]
        for rid, res in bad:
            print(f"rows-check: {path}: {rid}: the oracle has no such function: {res}", file=sys.stderr)
        if bad:
            sys.exit(2)
        lb = listed = 0
        for row, res in zip(rows, results):
            new = gen_rows.apply(row, res)
            same = all(row.get(f) == new.get(f) for f in fields)
            if own(row):
                listed += 1
                print(f"rows-check: {path}: {row['id']}: lean2rr's own difference "
                      f"{row['deviations']['lean2rr']}: {'agrees' if same else 'differs'} "
                      f"(lean2rr {[new.get(f) for f in fields]})")
            elif not same:
                failed += 1
                print(f"{path}: {row['id']}: expected {[row.get(f) for f in fields]}, "
                      f"lean2rr {[new.get(f) for f in fields]}")
            elif any(str(v).startswith("LB-") for v in row.get("deviations", {}).values()):
                lb += 1
        print(f"rows-check: {path}: {len(rows)} rows, {lb} of them LB-nn rows (the definition's "
              f"result), {listed} listed", file=sys.stderr)
except gen_rows.RowError as e:
    print(f"rows-check: {e}", file=sys.stderr)
    sys.exit(2)
if failed:
    print(f"rows-check: {failed} rows differ")
    sys.exit(1)
print("rows-check: every row agrees")
PY
