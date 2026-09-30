#!/usr/bin/env python3
"""Compile a compiled Lean module to a native executable through Reussir.

    l2r.py MODULE -o EXE [--lean-path DIR[:DIR...]] [-O LEVEL] [--keep-rr FILE]

MODULE must already be compiled by Lean 4.33 (its .olean on LEAN_PATH, or in
--lean-path). Steps: lean2rr (Lean LCNF -> .rr, with the runtime prelude),
then rrc (Reussir -> executable).

Environment overrides: L2R_REUSSIR (Reussir checkout with build/), L2R_RUSTC
(the rustc that built Reussir's runtime rlibs).
"""
import argparse, os, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REUSSIR = Path(os.environ.get("L2R_REUSSIR", ROOT / "reussir"))
RUSTC = Path(os.environ.get(
    "L2R_RUSTC",
    Path.home() / ".rustup/toolchains/nightly-2026-08-31-aarch64-unknown-linux-gnu/bin/rustc"))
LEAN2RR = ROOT / "lean2rr" / ".lake" / "build" / "bin" / "lean2rr"
PRELUDE = ROOT / "runtime" / "prelude.rr"


def run(cmd, env=None):
    res = subprocess.run(cmd, env=env, capture_output=True, text=True)
    if res.returncode != 0:
        sys.stderr.write(res.stdout + res.stderr)
        sys.exit(res.returncode or 1)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("module")
    ap.add_argument("-o", "--output", required=True)
    ap.add_argument("--lean-path", default=None, help="extra LEAN_PATH entries")
    ap.add_argument("-O", "--opt", default="default", choices=["none", "default", "aggressive", "size"])
    ap.add_argument("--keep-rr", default=None, help="also write the generated .rr here")
    ap.add_argument("--root", default="main")
    args = ap.parse_args()

    env = dict(os.environ)
    if args.lean_path:
        env["LEAN_PATH"] = args.lean_path + (":" + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")

    with tempfile.TemporaryDirectory() as tmp:
        rr = Path(args.keep_rr) if args.keep_rr else Path(tmp) / "prog.rr"
        run([str(LEAN2RR), args.module, "--root", args.root, "--emit", "rr",
             "--prelude", str(PRELUDE), "-o", str(rr)], env=env)
        rt = REUSSIR / "build" / "target-rt" / "release"
        target_libdir = run([str(RUSTC), "--print", "target-libdir"]).stdout.strip()
        run([str(REUSSIR / "build" / "bin" / "rrc"), str(rr), "-o", args.output,
             "--emit", "executable", "-O", args.opt,
             "--polyffi-rust-path", str(RUSTC),
             "--polyffi-libdir", str(rt), "--polyffi-libdir", str(rt / "deps"),
             "--polyffi-libdir", target_libdir])


if __name__ == "__main__":
    main()
