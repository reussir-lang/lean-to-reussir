#!/usr/bin/env python3
"""Compile a compiled Lean module to a native executable through Reussir.

    l2r.py MODULE -o EXE [--lean-path DIR[:DIR...]] [-O LEVEL] [--keep-rr FILE]
           [--disable-opt NAME]... [--enable-opt NAME]...
    l2r.py path/to/File.lean -o EXE [...]

MODULE must already be compiled by Lean 4.33 (its .olean on LEAN_PATH, or in
--lean-path). A module name may contain characters that are not identifier
characters (`rbtree-zipper`, or Lean's escaped `«rbtree-zipper»`). Given a
.lean file instead, the module is the file's name without `.lean`, compiled
in the file's directory (`lean -o File.olean File.lean` there), and its
.olean is looked for next to the file.

Steps: lean2rr (Lean LCNF -> .rr, with the runtime prelude), then rrc
(Reussir -> executable), linking the runtime crate `leanrt` (runtime/leanrt,
rebuilt here when its sources change) and GMP.

Environment overrides: L2R_REUSSIR (Reussir checkout with build/), L2R_RUSTC
(the rustc that built Reussir's runtime rlibs), L2R_GMP (path of libgmp.a;
default: the one shipped with the Lean toolchain), L2R_LEAN2RR (the lean2rr
binary), L2R_DISABLE_OPTS and L2R_ENABLE_OPTS (comma-separated lean2rr
optimizations to turn off or on, as --disable-opt/--enable-opt; spaces
around the names are ignored; `lean2rr --list-opts` lists them),
L2R_RRC_FLAGS (extra rrc flags, split on spaces, for experiments such as
`--nullary-variant-encoding arch-independent`).
"""
import argparse, fcntl, hashlib, os, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REUSSIR = Path(os.environ.get("L2R_REUSSIR", ROOT / "reussir")).resolve()
RUSTC = Path(os.environ.get(
    "L2R_RUSTC",
    Path.home() / ".rustup/toolchains/nightly-2026-08-31-aarch64-unknown-linux-gnu/bin/rustc")).resolve()
LEAN2RR = Path(os.environ.get("L2R_LEAN2RR", ROOT / "lean2rr" / ".lake" / "build" / "bin" / "lean2rr")).resolve()
PRELUDE = ROOT / "runtime" / "prelude.rr"
SHIM_DIR = ROOT / "lean2rr" / ".lake" / "build" / "lib" / "lean"
LEANRT_SRC = ROOT / "runtime" / "leanrt" / "src"
LEANRT_OUT = ROOT / "runtime" / "leanrt" / "target"

# Textures and leanrt are compiled for the host CPU and without outline
# atomics so their target attributes are a subset of rrc's native ones:
# LLVM can then inline textures into Reussir code. Without this, calls
# through the packed-argument FFI boundary (float or `str` arguments, four or
# more parameters) keep an escaping stack slot in the caller and block
# tail-call elimination of Reussir loops.
NATIVE_FLAGS = ["-C", "target-cpu=native", "-C", "target-feature=-outline-atomics"]


def run(cmd, env=None, cwd=None, show_stderr=False):
    res = subprocess.run(cmd, env=env, cwd=cwd, capture_output=True, text=True)
    if res.returncode != 0:
        sys.stderr.write(res.stdout + res.stderr)
        sys.exit(res.returncode or 1)
    if show_stderr and res.stderr:
        # Diagnostics of a successful step (lean2rr's warnings: a cast with no
        # representation conversion panics at run time).
        sys.stderr.write(res.stderr)
    return res


def rt_dirs():
    rt = REUSSIR / "build" / "target-rt" / "release"
    return rt, rt / "deps"


def rustc_wrapper(rlib):
    """A rustc wrapper script adding NATIVE_FLAGS (rrc takes one executable)
    and `leanrt` as an extern crate (and edition 2018 when rrc gives none,
    so that `::leanrt` resolves without `extern crate`): the drop hooks Reussir generates for
    the prelude's opaque types have no prelude block, and name the runtime's
    container types (`::leanrt::drop::Vec`, `::leanrt::drop::Cell`). One
    per `leanrt` build directory (per Reussir checkout)."""
    w = rlib.parent / "rustc-native"
    flags = "%s --extern leanrt='%s'" % (" ".join(NATIVE_FLAGS), rlib)
    text = ("#!/bin/sh\ncase \" $* \" in *--edition*) exec '%s' \"$@\" %s ;; esac\n"
            "exec '%s' \"$@\" %s --edition 2018\n" % (RUSTC, flags, RUSTC, flags))
    if not w.exists() or w.read_text() != text:
        tmp = w.with_name(w.name + ".%d" % os.getpid())
        tmp.write_text(text)
        tmp.chmod(0o755)
        os.replace(tmp, w)
    return w


def leanrt_out():
    """Where leanrt is built: it links against the Reussir checkout's runtime
    crates, so another checkout (L2R_REUSSIR, e.g. a patched Reussir) gets
    its own directory."""
    if REUSSIR.resolve() == (ROOT / "reussir").resolve():
        return LEANRT_OUT
    return LEANRT_OUT / ("rt-" + hashlib.sha256(str(REUSSIR.resolve()).encode()).hexdigest()[:12])


def build_leanrt():
    """Build runtime/leanrt as an rlib (cached by a hash of its sources and
    of the Reussir runtime it links against)."""
    rt, deps = rt_dirs()
    out = leanrt_out()
    h = hashlib.sha256()
    for f in sorted(LEANRT_SRC.rglob("*.rs")):
        h.update(f.name.encode())
        h.update(f.read_bytes())
    h.update(str(RUSTC).encode())
    h.update(" ".join(NATIVE_FLAGS).encode())
    for f in sorted(deps.glob("libreussir_rt*.rlib")):
        h.update(f.name.encode())
        h.update(str(f.stat().st_mtime_ns).encode())
    stamp = out / "libleanrt.stamp"
    rlib = out / "libleanrt.rlib"
    digest = h.hexdigest()
    out.mkdir(parents=True, exist_ok=True)
    # Concurrent drivers share the output directory: one builds, the others
    # wait for it and then find the stamp up to date.
    with open(out / "libleanrt.lock", "w") as lock:
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
        return Path(os.environ["L2R_GMP"]).resolve()
    prefix = subprocess.run(["lean", "--print-prefix"], capture_output=True, text=True).stdout.strip()
    return Path(prefix) / "lib" / "libgmp.a"


def module_and_path(arg, lean_path):
    """The module to translate and the LEAN_PATH entries to add: `arg` is a
    module name (passed on as it is: lean2rr reads non-identifier
    characters and `«»`), or a .lean file, whose module is its file name
    without `.lean` and whose .olean lies next to it (`lean -o File.olean
    File.lean`, run in its directory)."""
    if not arg.endswith(".lean"):
        return arg, lean_path
    src = Path(arg).resolve()
    olean = src.with_suffix(".olean")
    if not olean.exists():
        sys.exit(f"l2r: {olean} not found; compile the file first, in its directory: "
                 f"lean -o {olean.name} {src.name}")
    if src.exists() and olean.stat().st_mtime < src.stat().st_mtime:
        sys.exit(f"l2r: {olean} is older than {src}; recompile it: lean -o {olean.name} {src.name}")
    return src.stem, str(src.parent) + (":" + lean_path if lean_path else "")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("module")
    ap.add_argument("-o", "--output", required=True)
    ap.add_argument("--lean-path", default=None, help="extra LEAN_PATH entries")
    ap.add_argument("-O", "--opt", default="aggressive", choices=["none", "default", "aggressive", "size"])
    ap.add_argument("--keep-rr", default=None, help="also write the generated .rr here")
    ap.add_argument("--root", default="main")
    # Reuse a matched cell for a constructor after intervening calls (like
    # Lean's reset/reuse); `--no-reuse-across-call` turns it off.
    ap.add_argument("--no-reuse-across-call", action="store_true")
    # lean2rr optimizations to turn off or on (see `lean2rr --list-opts`);
    # also from L2R_DISABLE_OPTS / L2R_ENABLE_OPTS (comma-separated), for
    # test runners.
    ap.add_argument("--disable-opt", action="append", default=[], metavar="NAME")
    ap.add_argument("--enable-opt", action="append", default=[], metavar="NAME")
    args = ap.parse_args()
    module, lean_path = module_and_path(args.module, args.lean_path)

    env = dict(os.environ)
    # lean2rr runs Lean's compiler passes, which recurse once per nested
    # `let` (a 60000-element list literal needs more than 64 MiB of stack,
    # a 100000-element array literal translates in 1 GiB): the 1 GiB stack
    # Lean's own compiler runs on, set explicitly. A bigger stack is more
    # reserved address space: with 4 GiB, a 1500-line recursive `do` block
    # (adv5 OlRecLongDo) peaked at 16.6 GB of address space for 1.2 GB
    # resident and failed under `ulimit -v 16000000`; with 1 GiB, 13.6 GB.
    env.setdefault("LEAN_STACK_SIZE_KB", str(1024 * 1024))
    if lean_path:
        env["LEAN_PATH"] = lean_path + (":" + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
    # lean2rr's shim library (lean2rr/L2RShim.lean, built with lean2rr):
    # Lean implementations of Std.Internal.UV's externs, which lean2rr
    # compiles with the program. Last, so that the program's modules come
    # first.
    if SHIM_DIR.joinpath("L2RShim.olean").exists():
        env["LEAN_PATH"] = (env["LEAN_PATH"] + ":" if env.get("LEAN_PATH") else "") + str(SHIM_DIR)

    rlib = build_leanrt()
    with tempfile.TemporaryDirectory() as tmp:
        rr = Path(args.keep_rr).resolve() if args.keep_rr else Path(tmp) / "prog.rr"
        def env_names(var):
            return [n.strip() for n in os.environ.get(var, "").split(",") if n.strip()]
        disabled = args.disable_opt + env_names("L2R_DISABLE_OPTS")
        enabled = args.enable_opt + env_names("L2R_ENABLE_OPTS")
        run([str(LEAN2RR), module, "--root", args.root, "--emit", "rr",
             "--prelude", str(PRELUDE), "-o", str(rr)]
            + [a for n in disabled for a in ("--disable-opt", n)]
            + [a for n in enabled for a in ("--enable-opt", n)], env=env, show_stderr=True)
        rt, deps = rt_dirs()
        target_libdir = run([str(RUSTC), "--print", "target-libdir"]).stdout.strip()
        # rrc runs in the temporary directory: it leaves its polymorphic-FFI
        # scratch files (reussir_rust_module_*) in the current directory.
        rrc = ([str(REUSSIR / "build" / "bin" / "rrc"), str(rr), "-o", str(Path(args.output).resolve()),
                "--emit", "executable", "-O", args.opt,
                "--polyffi-rust-path", str(rustc_wrapper(rlib)),
                "--polyffi-libdir", str(rt), "--polyffi-libdir", str(deps),
                "--polyffi-libdir", target_libdir, "--polyffi-libdir", str(rlib.parent),
                "--link-lib", str(rlib), "--link-lib", str(gmp_archive())]
               # Reussir's in-place variant reuse skips stores of fields that
               # the packed record layout moves (RcCreateFusion copy
               # avoidance): keep declaration-order layouts until that is fixed.
               + ["--no-pack-record-members"]
               # -O aggressive enables closure devirtualization, which prints
               # each closure's result type, every named type expanded, at
               # every vtable and indirect call site: build time and memory
               # grow with the nesting of lean2rr's function representations
               # (3x on an interpreter, out of memory at 16 GB on polymorphic
               # recursion through monad transformers), while it changes no
               # classic benchmark by more than 1% (lean2rr dispatches
               # function values itself).
               + ["--no-closure-wpd"]
               # Extra rrc flags for experiments (L2R_RRC_FLAGS, split on spaces).
               + os.environ.get("L2R_RRC_FLAGS", "").split())
        if args.no_reuse_across_call:
            run(rrc, cwd=tmp)
        else:
            res = subprocess.run(rrc + ["--reuse-across-call"], env=env, cwd=tmp, capture_output=True, text=True)
            if res.returncode < 0:
                # rrc crashed (RcCreateFusion's structural type comparison
                # recurses forever on two structurally equal recursive types,
                # e.g. a user list and `List`): retry without reuse across calls.
                sys.stderr.write(f"l2r: rrc crashed (signal {-res.returncode}); retrying without --reuse-across-call\n")
                run(rrc, cwd=tmp)
            elif res.returncode != 0:
                sys.stderr.write(res.stdout + res.stderr)
                sys.exit(res.returncode)


if __name__ == "__main__":
    main()
