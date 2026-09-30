#!/usr/bin/env python3
"""Compile a compiled Lean module to a native executable through Reussir.

    l2r.py MODULE -o EXE [--lean-path DIR[:DIR...]] [-O LEVEL] [--keep-rr FILE]

MODULE must already be compiled by Lean 4.33 (its .olean on LEAN_PATH, or in
--lean-path). Steps: lean2rr (Lean LCNF -> .rr, with the runtime prelude),
then rrc (Reussir -> executable), linking the runtime crate `leanrt`
(runtime/leanrt, rebuilt here when its sources change) and GMP.

Environment overrides: L2R_REUSSIR (Reussir checkout with build/), L2R_RUSTC
(the rustc that built Reussir's runtime rlibs), L2R_GMP (path of libgmp.a;
default: the one shipped with the Lean toolchain).
"""
import argparse, fcntl, hashlib, os, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REUSSIR = Path(os.environ.get("L2R_REUSSIR", ROOT / "reussir"))
RUSTC = Path(os.environ.get(
    "L2R_RUSTC",
    Path.home() / ".rustup/toolchains/nightly-2026-08-31-aarch64-unknown-linux-gnu/bin/rustc"))
LEAN2RR = Path(os.environ.get("L2R_LEAN2RR", ROOT / "lean2rr" / ".lake" / "build" / "bin" / "lean2rr"))
PRELUDE = ROOT / "runtime" / "prelude.rr"
LEANRT_SRC = ROOT / "runtime" / "leanrt" / "src"
LEANRT_OUT = ROOT / "runtime" / "leanrt" / "target"

# Textures and leanrt are compiled for the host CPU and without outline
# atomics so their target attributes are a subset of rrc's native ones:
# LLVM can then inline textures into Reussir code. Without this, calls
# through the packed-argument FFI boundary (float or `str` arguments, four or
# more parameters) keep an escaping stack slot in the caller and block
# tail-call elimination of Reussir loops.
NATIVE_FLAGS = ["-C", "target-cpu=native", "-C", "target-feature=-outline-atomics"]


def run(cmd, env=None):
    res = subprocess.run(cmd, env=env, capture_output=True, text=True)
    if res.returncode != 0:
        sys.stderr.write(res.stdout + res.stderr)
        sys.exit(res.returncode or 1)
    return res


def rt_dirs():
    rt = REUSSIR / "build" / "target-rt" / "release"
    return rt, rt / "deps"


def rustc_wrapper():
    """A rustc wrapper script adding NATIVE_FLAGS (rrc takes one executable)."""
    LEANRT_OUT.mkdir(parents=True, exist_ok=True)
    w = LEANRT_OUT / "rustc-native"
    text = "#!/bin/sh\nexec '%s' \"$@\" %s\n" % (RUSTC, " ".join(NATIVE_FLAGS))
    if not w.exists() or w.read_text() != text:
        w.write_text(text)
        w.chmod(0o755)
    return w


def build_leanrt():
    """Build runtime/leanrt as an rlib (cached by a hash of its sources)."""
    rt, deps = rt_dirs()
    h = hashlib.sha256()
    for f in sorted(LEANRT_SRC.rglob("*.rs")):
        h.update(f.name.encode())
        h.update(f.read_bytes())
    h.update(str(RUSTC).encode())
    h.update(" ".join(NATIVE_FLAGS).encode())
    stamp = LEANRT_OUT / "libleanrt.stamp"
    rlib = LEANRT_OUT / "libleanrt.rlib"
    digest = h.hexdigest()
    LEANRT_OUT.mkdir(parents=True, exist_ok=True)
    # Concurrent drivers share the output directory: one builds, the others
    # wait for it and then find the stamp up to date.
    with open(LEANRT_OUT / "libleanrt.lock", "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if rlib.exists() and stamp.exists() and stamp.read_text() == digest:
            return rlib
        run([str(RUSTC), "--edition", "2021", "--crate-type", "rlib", "--crate-name", "leanrt",
             "-C", "opt-level=3", *NATIVE_FLAGS, "-L", str(rt), "-L", str(deps),
             str(LEANRT_SRC / "lib.rs"), "-o", str(rlib)])
        stamp.write_text(digest)
        return rlib


def gmp_archive():
    if os.environ.get("L2R_GMP"):
        return Path(os.environ["L2R_GMP"])
    prefix = subprocess.run(["lean", "--print-prefix"], capture_output=True, text=True).stdout.strip()
    return Path(prefix) / "lib" / "libgmp.a"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("module")
    ap.add_argument("-o", "--output", required=True)
    ap.add_argument("--lean-path", default=None, help="extra LEAN_PATH entries")
    ap.add_argument("-O", "--opt", default="default", choices=["none", "default", "aggressive", "size"])
    ap.add_argument("--keep-rr", default=None, help="also write the generated .rr here")
    ap.add_argument("--root", default="main")
    # Reuse a matched cell for a constructor after intervening calls (like
    # Lean's reset/reuse); `--no-reuse-across-call` turns it off.
    ap.add_argument("--no-reuse-across-call", action="store_true")
    args = ap.parse_args()

    env = dict(os.environ)
    if args.lean_path:
        env["LEAN_PATH"] = args.lean_path + (":" + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")

    rlib = build_leanrt()
    with tempfile.TemporaryDirectory() as tmp:
        rr = Path(args.keep_rr) if args.keep_rr else Path(tmp) / "prog.rr"
        run([str(LEAN2RR), args.module, "--root", args.root, "--emit", "rr",
             "--prelude", str(PRELUDE), "-o", str(rr)], env=env)
        rt, deps = rt_dirs()
        target_libdir = run([str(RUSTC), "--print", "target-libdir"]).stdout.strip()
        rrc = ([str(REUSSIR / "build" / "bin" / "rrc"), str(rr), "-o", args.output,
                "--emit", "executable", "-O", args.opt,
                "--polyffi-rust-path", str(rustc_wrapper()),
                "--polyffi-libdir", str(rt), "--polyffi-libdir", str(deps),
                "--polyffi-libdir", target_libdir, "--polyffi-libdir", str(LEANRT_OUT),
                "--link-lib", str(rlib), "--link-lib", str(gmp_archive())]
               # Reussir's in-place variant reuse skips stores of fields that
               # the packed record layout moves (RcCreateFusion copy
               # avoidance): keep declaration-order layouts until that is fixed.
               + ["--no-pack-record-members"])
        if args.no_reuse_across_call:
            run(rrc)
        else:
            res = subprocess.run(rrc + ["--reuse-across-call"], env=env, capture_output=True, text=True)
            if res.returncode < 0:
                # rrc crashed (RcCreateFusion's structural type comparison
                # recurses forever on two structurally equal recursive types,
                # e.g. a user list and `List`): retry without reuse across calls.
                sys.stderr.write(f"l2r: rrc crashed (signal {-res.returncode}); retrying without --reuse-across-call\n")
                run(rrc)
            elif res.returncode != 0:
                sys.stderr.write(res.stdout + res.stderr)
                sys.exit(res.returncode)


if __name__ == "__main__":
    main()
