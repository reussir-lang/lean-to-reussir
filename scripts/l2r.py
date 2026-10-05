#!/usr/bin/env python3
"""Compile a compiled Lean module to a native executable through Reussir.

    l2r.py MODULE -o EXE [--lean-path DIR[:DIR...]] [-O LEVEL] [--keep-rr FILE]
           [--disable-opt NAME]... [--enable-opt NAME]... [--emit llvm-ir]
    l2r.py path/to/File.lean -o EXE [...]

MODULE must already be compiled by the Lean toolchain lean2rr is built with
(lean2rr/lean-toolchain: v4.34.0; its .olean on LEAN_PATH, or in --lean-path). A module name may contain characters that are not identifier
characters (`rbtree-zipper`, or Lean's escaped `«rbtree-zipper»`). Given a
.lean file instead, the module is the file's name without `.lean`, compiled
in the file's directory (`lean -o File.olean File.lean` there), and its
.olean is looked for next to the file.

Steps: lean2rr (Lean LCNF -> .rr, with the runtime prelude), then rrc
(Reussir -> executable), linking the runtime crate `leanrt` (runtime/leanrt),
the shared runtime crate `lean_runtime` it uses (third_party/lean-runtime, a
git submodule), both rebuilt here when their sources change, and GMP.

Environment overrides: L2R_REUSSIR (Reussir checkout with build/), L2R_RUSTC
(the rustc that built Reussir's runtime rlibs), L2R_LEAN_TOOLCHAIN (the Lean
toolchain directory; default: the elan toolchain lean2rr/lean-toolchain
names), L2R_GMP (path of libgmp.a; default: the one shipped with that
toolchain), L2R_LEAN2RR (the lean2rr
binary), L2R_DISABLE_OPTS and L2R_ENABLE_OPTS (comma-separated lean2rr
optimizations to turn off or on, as --disable-opt/--enable-opt; spaces
around the names are ignored; `lean2rr --list-opts` lists them),
L2R_LEANRT_RUSTFLAGS (extra rustc flags for leanrt and lean-runtime, split
on spaces; e.g. `--cfg leanrt_count_bigs`), L2R_LEAN_RUNTIME (another
lean-runtime checkout, e.g. a branch under review; default: the submodule
third_party/lean-runtime, whose checked-out commit must be the pinned one),
L2R_LEAN_RUNTIME_FEATURES (comma-separated lean-runtime features to add, to
try a branch), L2R_RRC_FLAGS (extra rrc flags, split on spaces, for experiments such as
`--nullary-variant-encoding arch-independent`), REUSSIR_FFI_CACHE_DIR
(where rrc keeps the compiled textures; default
runtime/leanrt/target/polyffi-cache, empty to turn the cache off).
"""
import argparse, fcntl, hashlib, json, os, subprocess, sys, tempfile, tomllib
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
# The shared runtime crate, the lean-runtime crate (repo lean-runtime-rs,
# github.com/QueClr/lean-runtime-rs), pinned by commit
# as a git submodule; built below with the same rustc and flags as leanrt.
LEAN_RUNTIME_PIN = ROOT / "third_party" / "lean-runtime"
LEAN_RUNTIME = Path(os.environ.get("L2R_LEAN_RUNTIME", LEAN_RUNTIME_PIN)).resolve()

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


def rustc_wrapper(rlib, lr):
    """A rustc wrapper script adding NATIVE_FLAGS (rrc takes one executable)
    and `leanrt` as an extern crate (and edition 2018 when rrc gives none,
    so that `::leanrt` resolves without `extern crate`): the drop hooks Reussir generates for
    the prelude's opaque types have no prelude block, and name the runtime's
    container types (`::leanrt::drop::Vec`, `::leanrt::drop::Cell`). It also
    adds `lean_runtime` (`lr`, a LeanRuntime), which leanrt depends on, as an
    extern crate (the prelude's textures call it as `sem`) and the
    directories of its rlibs as dependency search paths (where rustc finds
    it, and its own dependencies, when it loads leanrt). One per `leanrt`
    build directory (per Reussir checkout).

    The script's text names lean-runtime's build (`lr.digest`): rrc's
    texture cache (`REUSSIR_FFI_CACHE_DIR`, Reussir issue 35) hashes the
    script's text and the libraries in the `--polyffi-libdir` directories,
    and cargo's build of lean-runtime puts its rlibs in none of them."""
    w = rlib.parent / "rustc-native"
    flags = "%s --extern leanrt='%s'%s%s" % (
        " ".join(NATIVE_FLAGS), rlib, "".join(" --extern '%s'" % e for e in lr.externs),
        "".join(" -L dependency='%s'" % d for d in lr.dirs))
    text = ("#!/bin/sh\n# lean-runtime build %s\n"
            "case \" $* \" in *--edition*) exec '%s' \"$@\" %s ;; esac\n"
            "exec '%s' \"$@\" %s --edition 2018\n" % (lr.digest, RUSTC, flags, RUSTC, flags))
    if not w.exists() or w.read_text() != text:
        tmp = w.with_name(w.name + ".%d" % os.getpid())
        tmp.write_text(text)
        tmp.chmod(0o755)
        os.replace(tmp, w)
    return w


# Extra rustc flags for leanrt and lean-runtime (L2R_LEANRT_RUSTFLAGS, split
# on spaces), for test builds such as `--cfg leanrt_count_bigs`
# (tests/runtime/nat-alloc-check.sh). lean-runtime gets them too so that both
# crates are always compiled alike (a `-C` flag such as `panic=abort` must
# agree between them). rustc runs in the crate's directory (`build_locked`):
# a relative path in these flags is relative to it.
LEANRT_FLAGS = os.environ.get("L2R_LEANRT_RUSTFLAGS", "").split()

# The features of lean-runtime lean2rr builds: `io` (leanrt's files,
# streams, processes, system queries, startup and exit glue call
# lean_runtime::io), `proc-title` (`setProcessTitle` writes the title into
# the arguments' memory, as libuv does: the crate's ELF constructor keeps that
# memory), `startup-fds` (native Lean's startup descriptors, libuv's loop,
# opened by the crate's ELF constructor before Rust's runtime starts, so a
# closed standard descriptor is taken by the first of them, as natively;
# `rt::run_main2` calls `io::startup::ensure_native_descriptors`), `sched`
# (the task scheduler: tasks, promises, Std.Sync, the event loop with
# Std.Internal.UV's timers and signals, `main`'s thread; leanrt keeps the
# glue), `stack-overflow` (Lean's stack-overflow report for the scheduler's
# contexts and lean2rr's threads; named on its own, as lean-runtime's newer
# branches no longer turn it on with `sched`) and `net` (Std.Internal.UV's
# sockets and name resolution on the same event loop).
# L2R_LEAN_RUNTIME_FEATURES (comma-separated) adds others, to try a
# lean-runtime branch.
LEAN_RUNTIME_BASE_FEATURES = ["io", "proc-title", "startup-fds", "sched", "stack-overflow", "net"]
LEAN_RUNTIME_EXTRA_FEATURES = [f.strip() for f in os.environ.get("L2R_LEAN_RUNTIME_FEATURES", "").split(",") if f.strip()]
LEAN_RUNTIME_FEATURES = LEAN_RUNTIME_BASE_FEATURES + [f for f in LEAN_RUNTIME_EXTRA_FEATURES if f not in LEAN_RUNTIME_BASE_FEATURES]


def leanrt_out():
    """Where leanrt and lean-runtime are built: leanrt links against the
    Reussir checkout's runtime crates, so another checkout (L2R_REUSSIR, e.g.
    a patched Reussir) gets its own directory, and so do extra flags
    (L2R_LEANRT_RUSTFLAGS), another lean-runtime checkout (L2R_LEAN_RUNTIME)
    and extra features (L2R_LEAN_RUNTIME_FEATURES)."""
    def key(text):
        return hashlib.sha256(text.encode()).hexdigest()[:12]
    out = LEANRT_OUT
    if REUSSIR.resolve() != (ROOT / "reussir").resolve():
        out = out / ("rt-" + key(str(REUSSIR.resolve())))
    if LEANRT_FLAGS:
        out = out / ("flags-" + key(" ".join(LEANRT_FLAGS)))
    if LEAN_RUNTIME != LEAN_RUNTIME_PIN.resolve():
        out = out / ("lr-" + key(str(LEAN_RUNTIME)))
    if LEAN_RUNTIME_EXTRA_FEATURES:
        out = out / ("feat-" + key(",".join(LEAN_RUNTIME_EXTRA_FEATURES)))
    return out


def build_locked(out, stamp, outputs, digest, cmd, cwd, digest_after=None):
    """Run `cmd` (a rustc command building `outputs`) in `cwd` unless `stamp`
    records `digest`; then record `digest_after()` (default: `digest`), for a
    digest that depends on what the build found (its dep-info). Concurrent
    drivers share the output directory: one builds, the others wait for it
    and then find the stamp up to date.

    `cwd` is the crate's directory, not the caller's: rustc records its
    working directory in the rlib's metadata, so a rebuild from another
    directory would give an rlib with other bytes, and rrc's texture cache
    (Reussir issue 35), which hashes the rlibs, would miss on every texture.
    The paths in `cmd` are absolute (so are the source paths rustc records,
    which panic messages show)."""
    out.mkdir(parents=True, exist_ok=True)
    with open(out / "libleanrt.lock", "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if all(o.exists() for o in outputs) and stamp.exists() and stamp.read_text() == digest:
            return
        run(cmd, cwd=cwd)
        stamp.write_text(digest_after() if digest_after else digest)


class LeanRuntime:
    """A build of lean-runtime: its rlib, every rlib to link in link order
    (lean_runtime first, then its dependencies, dependents before
    dependencies), the directories rustc searches for them, and a digest
    that changes whenever any of them is rebuilt. `externs` are the
    `--extern lean_runtime=...` arguments: the rlib, and its `.rmeta` when
    the rlib holds only a metadata stub (cargo's)."""

    def __init__(self, rlib, rlibs, digest, rmeta=None):
        self.rlib, self.rlibs, self.digest = rlib, rlibs, digest
        self.dirs = list(dict.fromkeys(r.parent for r in rlibs))
        self.externs = [f"lean_runtime={rlib}"] + ([f"lean_runtime={rmeta}"] if rmeta else [])


def check_pin():
    """The submodule must have the pinned commit checked out: git does not
    update a submodule when a checkout, merge or pull moves its gitlink, and
    the suite would then run against the old commit. The pin is the gitlink
    in the index (`git ls-files -s`), so that a new pin staged with `git add
    third_party/lean-runtime` can be tested before it is committed.
    L2R_LEAN_RUNTIME (another checkout) skips this on purpose, and so does a
    lean2rr tree without git."""
    if LEAN_RUNTIME != LEAN_RUNTIME_PIN.resolve() or not (ROOT / ".git").exists():
        return
    def git(*args):
        res = subprocess.run(["git", *args], capture_output=True, text=True)
        return res.stdout.strip() if res.returncode == 0 else None
    try:
        staged = (git("-C", str(ROOT), "ls-files", "-s", "--", "third_party/lean-runtime") or "").split()
        top = git("-C", str(LEAN_RUNTIME), "rev-parse", "--show-toplevel")
        head = git("-C", str(LEAN_RUNTIME), "rev-parse", "HEAD")
    except OSError:
        return
    if len(staged) < 2 or staged[0] != "160000" or not top or Path(top).resolve() != LEAN_RUNTIME:
        return
    if head != staged[1]:
        sys.exit(f"l2r: third_party/lean-runtime has {head[:12] if head else 'no commit'} checked out, "
                 f"but lean2rr pins {staged[1][:12]}: run `git submodule update third_party/lean-runtime` "
                 "(or set L2R_LEAN_RUNTIME to build another lean-runtime checkout)")


def lean_runtime_manifest():
    """lean-runtime's Cargo.toml (its library must be `lean_runtime`)."""
    manifest = LEAN_RUNTIME / "Cargo.toml"
    if not manifest.is_file():
        sys.exit(f"l2r: no {manifest}: run `git submodule update --init third_party/lean-runtime` "
                 "in the lean2rr checkout (or set L2R_LEAN_RUNTIME to a lean-runtime checkout)")
    check_pin()
    with open(manifest, "rb") as f:
        cargo = tomllib.load(f)
    pkg, lib = cargo["package"], cargo.get("lib", {})
    if lib.get("name", pkg["name"].replace("-", "_")) != "lean_runtime":
        sys.exit(f"l2r: {manifest}: the library is no longer called lean_runtime")
    return cargo


def build_lean_runtime_cargo(out, cargo):
    """lean-runtime with the features lean2rr enables
    (`LEAN_RUNTIME_BASE_FEATURES`, whose dependencies have build scripts): the pinned
    toolchain's cargo builds it
    offline (`--offline --locked`) from the crates in cargo's registry cache,
    at the versions its committed Cargo.lock names (so nothing is written in
    the checkout); `cargo fetch --locked` in the checkout fills the cache
    once (lean-runtime has no vendor/ directory: shared-runtime decision "io-1
    packaging"). RUSTC and RUSTFLAGS are leanrt's rustc and flags (the
    environment's cargo rustflags are removed). The rlibs come from cargo's
    JSON messages; those of packages lean-runtime's normal dependencies
    reach are linked, in the order of its dependency graph
    (`cargo_link_order`). Cargo's fingerprints are the cache."""
    if not (LEAN_RUNTIME / "Cargo.lock").is_file():
        sys.exit(f"l2r: lean-runtime ({LEAN_RUNTIME}) has dependencies but no Cargo.lock "
                 "(the offline --locked build needs it)")
    cargo_bin = RUSTC.parent / "cargo"
    if not cargo_bin.is_file():
        sys.exit(f"l2r: no {cargo_bin} next to the pinned rustc (lean-runtime has dependencies)")
    # leanrt's rustc and flags; nothing in the environment may override them
    # (CARGO_ENCODED_RUSTFLAGS and the build/target rustflags win over
    # RUSTFLAGS) or move the build.
    env = dict(os.environ, RUSTC=str(RUSTC), RUSTFLAGS=" ".join(NATIVE_FLAGS + LEANRT_FLAGS))
    for v in list(env):
        if v in ("RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "CARGO_TARGET_DIR", "CARGO_BUILD_TARGET",
                 "CARGO_ENCODED_RUSTFLAGS", "CARGO_BUILD_RUSTFLAGS", "CARGO_BUILD_RUSTC",
                 "CARGO_BUILD_RUSTC_WRAPPER") or (v.startswith("CARGO_TARGET_") and v.endswith("_RUSTFLAGS")):
            del env[v]
    features = ["--features", ",".join(LEAN_RUNTIME_FEATURES)] if LEAN_RUNTIME_FEATURES else []
    cmd = [str(cargo_bin), "build", "--offline", "--locked", "--release", "--lib",
           "--target-dir", str(out / "lr-cargo"), "--message-format=json-render-diagnostics"] + features
    out.mkdir(parents=True, exist_ok=True)
    with open(out / "libleanrt.lock", "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        res = subprocess.run(cmd, env=env, cwd=LEAN_RUNTIME, capture_output=True, text=True)
    if res.returncode != 0:
        sys.stderr.write(res.stderr)
        # Offline, a crate missing from the registry cache is an error that
        # names offline mode.
        if "offline" in res.stderr:
            sys.stderr.write(f"l2r: a crate lean-runtime needs is not in cargo's registry cache: run "
                             f"`{cargo_bin} fetch --locked` in {LEAN_RUNTIME} once (it downloads the "
                             "crates Cargo.lock names; every build after it is offline)\n")
        sys.exit(res.returncode or 1)
    # Each library unit's rlib and .rmeta, by package. Cargo's rlibs hold a
    # metadata stub; the full metadata is the .rmeta next to the rlib in the
    # unit's directory (the rlib cargo copies to release/ has none next to
    # it, so the unit's own rlib is taken).
    units, own = {}, None
    for line in res.stdout.split("\n"):
        if not line.startswith("{"):
            continue
        msg = json.loads(line)
        if msg.get("reason") == "build-script-executed" and msg.get("linked_libs"):
            sys.exit(f"l2r: {msg['package_id']} links native libraries {msg['linked_libs']}, "
                     "which scripts/l2r.py does not pass on yet")
        if msg.get("reason") != "compiler-artifact":
            continue
        files = [Path(f) for f in msg.get("filenames", [])]
        rmeta = next((f for f in files if f.suffix == ".rmeta"), None)
        rlib = next((f for f in files if f.suffix == ".rlib"), None)
        if rmeta and rmeta.with_suffix(".rlib").is_file():
            rlib = rmeta.with_suffix(".rlib")
        if rlib is None:
            continue
        if msg["target"]["name"] == "lean_runtime":
            own = (rlib, rmeta)
        else:
            units.setdefault(msg["package_id"], []).append(rlib)
    if own is None:
        sys.exit("l2r: cargo built no lean_runtime rlib")
    # Linked: the packages lean-runtime's normal dependencies reach on this
    # host (not build scripts' dependencies such as cfg_aliases), dependents
    # before their dependencies, as GNU ld needs (cargo's build order is
    # only one of the orders its graph allows).
    rlibs = [own[0]] + [r for pkg in cargo_link_order(cargo_bin, env, features)[1:] for r in units.get(pkg, [])]
    h = hashlib.sha256()
    for r in rlibs:
        st = r.stat()
        h.update(f"{r} {st.st_size} {st.st_mtime_ns}\n".encode())
    return LeanRuntime(own[0], rlibs, h.hexdigest(), own[1])


def cargo_link_order(cargo_bin, env, features):
    """lean-runtime's package and the packages its normal dependencies reach
    on this host (`cargo metadata --filter-platform`), each before the
    packages it depends on (a reverse post-order of the dependency graph)."""
    host = next(l.split(": ", 1)[1] for l in run([str(RUSTC), "-vV"]).stdout.split("\n")
                if l.startswith("host: "))
    meta = json.loads(run([str(cargo_bin), "metadata", "--offline", "--locked", "--format-version", "1",
                           "--filter-platform", host] + features, env=env, cwd=LEAN_RUNTIME).stdout)
    deps = {n["id"]: [d["pkg"] for d in n["deps"] if any(k["kind"] is None for k in d["dep_kinds"])]
            for n in meta["resolve"]["nodes"]}
    order, seen = [], set()
    def visit(p):
        if p not in seen:
            seen.add(p)
            for q in deps.get(p, []):
                visit(q)
            order.append(p)
    visit(meta["resolve"]["root"])
    return order[::-1]


def build_lean_runtime(out):
    """Build lean-runtime (LEAN_RUNTIME, default the submodule) into `out`
    with leanrt's rustc and flags, through the pinned toolchain's cargo
    (`build_lean_runtime_cargo`). Returns a LeanRuntime."""
    return build_lean_runtime_cargo(out, lean_runtime_manifest())


# Local Reussir patches whose absence would not show as a build error at the
# right place: (patch, file of the Reussir checkout, a symbol the patch adds
# there). 0040: every drain that released something calls the function the
# host stores in `__reussir_drop_drained` once it is over; leanrt resolves
# the promises a free dropped there (runtime/README.md, "The scheduler").
# leanrt's reference to the symbol would also fail to compile without it.
REQUIRED_REUSSIR_PATCHES = [
    ("0040", "crates/reussir-rt/src/drop.rs", "__reussir_drop_drained"),
]


def check_reussir_patches():
    """The Reussir checkout (L2R_REUSSIR) is one, and has the local patches
    lean2rr requires (REQUIRED_REUSSIR_PATCHES)."""
    if not (REUSSIR / "crates" / "reussir-rt" / "src").is_dir():
        sys.exit(f"l2r: no Reussir checkout at {REUSSIR} (no crates/reussir-rt/src there): "
                 "set L2R_REUSSIR to a Reussir checkout (default: reussir/ in the lean2rr checkout)")
    for patch, rel, symbol in REQUIRED_REUSSIR_PATCHES:
        src = REUSSIR / rel
        if not src.is_file() or symbol not in src.read_text():
            sys.exit(f"l2r: the Reussir checkout {REUSSIR} lacks the local Reussir patch {patch} "
                     f"(`{symbol}` in {rel}), which lean2rr requires: build with a Reussir that has it "
                     "(runtime/README.md, \"The scheduler\")")


def build_leanrt():
    """Build lean-runtime, then runtime/leanrt against it, as rlibs (leanrt
    cached by a hash of its sources, of lean-runtime's build and of the
    Reussir runtime it links against). Returns leanrt's rlib and the
    LeanRuntime."""
    check_reussir_patches()
    rt, deps = rt_dirs()
    out = leanrt_out()
    lr = build_lean_runtime(out)
    h = hashlib.sha256()
    for f in sorted(LEANRT_SRC.rglob("*.rs")):
        h.update(f.name.encode())
        h.update(f.read_bytes())
    h.update(str(RUSTC).encode())
    h.update(" ".join(NATIVE_FLAGS + LEANRT_FLAGS).encode())
    h.update(lr.digest.encode())
    for f in sorted(deps.glob("libreussir_rt*.rlib")):
        h.update(f.name.encode())
        h.update(str(f.stat().st_mtime_ns).encode())
    rlib = out / "libleanrt.rlib"
    build_locked(out, out / "libleanrt.stamp", [rlib], h.hexdigest(),
                 [str(RUSTC), "--edition", "2021", "--crate-type", "rlib", "--crate-name", "leanrt",
                  "-C", "opt-level=3", *NATIVE_FLAGS, *LEANRT_FLAGS, "-L", str(rt), "-L", str(deps),
                  *[a for e in lr.externs for a in ("--extern", e)],
                  *[a for d in lr.dirs for a in ("-L", f"dependency={d}")],
                  str(LEANRT_SRC / "lib.rs"), "-o", str(rlib)],
                 LEANRT_SRC.parent)
    return rlib, lr


def lean_toolchain():
    """The Lean toolchain directory: L2R_LEAN_TOOLCHAIN, else the elan
    toolchain that lean2rr/lean-toolchain pins (as scripts/toolchain.sh)."""
    if os.environ.get("L2R_LEAN_TOOLCHAIN"):
        return Path(os.environ["L2R_LEAN_TOOLCHAIN"])
    pin = "".join((ROOT / "lean2rr" / "lean-toolchain").read_text().split())
    elan = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
    return elan / "toolchains" / pin.replace("/", "--").replace(":", "---")


def gmp_archive():
    """The GMP that native Lean links: the one shipped with the toolchain."""
    if os.environ.get("L2R_GMP"):
        return Path(os.environ["L2R_GMP"]).resolve()
    gmp = lean_toolchain() / "lib" / "libgmp.a"
    if not gmp.exists():
        sys.exit(f"l2r: no {gmp}: set L2R_LEAN_TOOLCHAIN (or L2R_GMP)")
    return gmp


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
    # What rrc writes to -o: the executable, or the program's LLVM IR (after
    # rrc's optimizations, textures linked in), for checks such as
    # tests/runtime/ffi-inline-check.sh.
    ap.add_argument("--emit", default="executable", choices=["executable", "llvm-ir"])
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
    # compiles with the program. lean2rr looks for it there only (after the
    # program's modules and Lean's library), also when L2R_LEAN2RR is a copy
    # of the binary elsewhere.
    env["L2R_SHIM_DIR"] = str(SHIM_DIR)
    # rrc compiles each of the prelude's textures with its own rustc run,
    # most of its time on a small program; this directory keeps the bitcode
    # (Reussir issue 35, a cost; patch 0066; an rrc without the patch ignores
    # the variable). rrc keys each entry by everything the bitcode depends on,
    # the texture, rustc (here the rustc-native script, whose text names the
    # rlibs and the flags), its options and the libraries in the
    # --polyffi-libdir directories (leanrt's build directory among them), so
    # all builds share one directory. Nothing removes old entries: delete the
    # directory to reclaim the space. An empty value turns the cache off.
    env.setdefault("REUSSIR_FFI_CACHE_DIR", str(LEANRT_OUT / "polyffi-cache"))

    rlib, lr = build_leanrt()
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
                "--emit", args.emit, "-O", args.opt,
                "--polyffi-rust-path", str(rustc_wrapper(rlib, lr)),
                "--polyffi-libdir", str(rt), "--polyffi-libdir", str(deps),
                "--polyffi-libdir", target_libdir, "--polyffi-libdir", str(rlib.parent),
                # In dependency order (GNU ld reads each archive once):
                # leanrt, then lean-runtime, which leanrt calls, and its
                # dependencies, then GMP.
                "--link-lib", str(rlib)]
               + [a for r in lr.rlibs for a in ("--link-lib", str(r))]
               + ["--link-lib", str(gmp_archive())]
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
               # rrc compiles with LLVM's static relocation model unless told
               # otherwise, but links a position-independent executable, so
               # read-only data with absolute addresses (closure vtables) needs
               # text relocations (DT_TEXTREL) with GNU ld and fails with lld
               # (Reussir bug 34, patch 0065). Native Lean executables are PIEs
               # without text relocations.
               + ["--relocation-mode", "pic"]
               # Extra rrc flags for experiments (L2R_RRC_FLAGS, split on spaces).
               + os.environ.get("L2R_RRC_FLAGS", "").split())
        if args.no_reuse_across_call:
            run(rrc, env=env, cwd=tmp)
        else:
            res = subprocess.run(rrc + ["--reuse-across-call"], env=env, cwd=tmp, capture_output=True, text=True)
            if res.returncode < 0:
                # rrc crashed (RcCreateFusion's structural type comparison
                # recurses forever on two structurally equal recursive types,
                # e.g. a user list and `List`): retry without reuse across calls.
                sys.stderr.write(f"l2r: rrc crashed (signal {-res.returncode}); retrying without --reuse-across-call\n")
                run(rrc, env=env, cwd=tmp)
            elif res.returncode != 0:
                sys.stderr.write(res.stdout + res.stderr)
                sys.exit(res.returncode)


if __name__ == "__main__":
    main()
