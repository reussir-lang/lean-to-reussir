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
binary; another checkout's build gets the shim built with it, and the
driver names on stderr the checkouts the build's parts come from),
L2R_DISABLE_OPTS and L2R_ENABLE_OPTS (comma-separated lean2rr
optimizations to turn off or on, as --disable-opt/--enable-opt; spaces
around the names are ignored; `lean2rr --list-opts` lists them),
L2R_LEANRT_RUSTFLAGS (extra rustc flags for leanrt and lean-runtime, split
on spaces; e.g. `-C debug-assertions`), L2R_TEXTURE_RUSTFLAGS (extra
rustc flags for the textures rrc compiles, after the native ones, split on
spaces; e.g. `-C target-feature=-sve,-sve2,-dotprod` with the same in
L2R_LEANRT_RUSTFLAGS and L2R_RRC_FLAGS for a build valgrind can run),
L2R_LEAN_RUNTIME (another
lean-runtime checkout, e.g. a branch under review; default: the submodule
third_party/lean-runtime, whose checked-out commit must be the pinned one),
L2R_LEAN_RUNTIME_FEATURES (comma-separated lean-runtime features to add, to
try a branch), L2R_INT_BACKEND (unset, empty or `rcgmp`: `Nat` and `Int`
are Reussir's built-in integers; `leanrt`, removed on 2026-10-26 by
clean-integration D8, is refused),
L2R_RRC_FLAGS (extra rrc flags, split on spaces, for experiments such as
`--nullary-variant-encoding arch-independent`), REUSSIR_FFI_CACHE_DIR
(where rrc keeps the compiled textures; default
runtime/leanrt/target/polyffi-cache, empty to turn the cache off).
"""
import argparse, fcntl, hashlib, json, os, subprocess, sys, tempfile, tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REUSSIR = Path(os.environ.get("L2R_REUSSIR", ROOT / "reussir")).resolve()
DEFAULT_RUSTC = Path.home() / ".rustup/toolchains/nightly-2026-08-31-aarch64-unknown-linux-gnu/bin/rustc"
RUSTC = Path(os.environ.get("L2R_RUSTC", DEFAULT_RUSTC)).resolve()
# This checkout's lean2rr build: the binary and its shim library.
OWN_LEAN2RR = ROOT / "lean2rr" / ".lake" / "build" / "bin" / "lean2rr"
OWN_SHIM_DIR = ROOT / "lean2rr" / ".lake" / "build" / "lib" / "lean"
LEAN2RR = Path(os.environ.get("L2R_LEAN2RR", OWN_LEAN2RR)).resolve()
PRELUDE = ROOT / "runtime" / "prelude.rr"
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
    """A rustc wrapper script adding NATIVE_FLAGS and L2R_TEXTURE_RUSTFLAGS (rrc takes one executable)
    and `leanrt` as an extern crate (and edition 2018 when rrc gives none,
    so that `::leanrt` resolves without `extern crate`): the drop hooks Reussir generates for
    the prelude's opaque types have no prelude block, and name the runtime's
    container types (`::leanrt::drop::Vec`, `::leanrt::drop::Cell`). It also
    adds `lean_runtime` (`lr`, a LeanRuntime), which leanrt depends on, as an
    extern crate (the prelude's textures call it as `sem`) and the
    directories of its rlibs as dependency search paths (where rustc finds
    it, and its own dependencies, when it loads leanrt).

    The script's text names lean-runtime's build (`lr.digest`): rrc's
    texture cache (`REUSSIR_FFI_CACHE_DIR`) hashes the
    script's text and the libraries in the `--polyffi-libdir` directories,
    and cargo's build of lean-runtime puts its rlibs in none of them.

    The script is named after a hash of its text (`rustc-native-<sha12>` in
    leanrt's build directory) and written only when it is missing (or does
    not hold that text), atomically (a temporary file renamed), so a script
    never changes once written: rrc runs it by path for every texture and for
    the final link, so each build's rrc runs a script with its own settings
    while another build (other L2R_TEXTURE_RUSTFLAGS, another lean-runtime
    build) writes its own. Until 2026-10-27 the script was one
    `rustc-native` per directory, rewritten by the last build: a build
    paused at rrc's start while another ran with L2R_TEXTURE_RUSTFLAGS
    compiled its textures with the other build's target features."""
    flags = "%s --extern leanrt='%s'%s%s" % (
        " ".join(NATIVE_FLAGS + TEXTURE_FLAGS), rlib, "".join(" --extern '%s'" % e for e in lr.externs),
        "".join(" -L dependency='%s'" % d for d in lr.dirs))
    text = ("#!/bin/sh\n# lean-runtime build %s\n"
            "case \" $* \" in *--edition*) exec '%s' \"$@\" %s ;; esac\n"
            "exec '%s' \"$@\" %s --edition 2018\n" % (lr.digest, RUSTC, flags, RUSTC, flags))
    w = rlib.parent / ("rustc-native-" + hashlib.sha256(text.encode()).hexdigest()[:12])
    if not w.exists() or w.read_text() != text:
        fd, tmp = tempfile.mkstemp(dir=rlib.parent, prefix=".rustc-native-")
        try:
            with os.fdopen(fd, "w") as f:
                f.write(text)
            os.chmod(tmp, 0o755)
            os.replace(tmp, w)
        except BaseException:
            Path(tmp).unlink(missing_ok=True)
            raise
    return w


# Extra rustc flags for leanrt and lean-runtime (L2R_LEANRT_RUSTFLAGS, split
# on spaces), for test builds such as `-C debug-assertions` (leanrt's
# invariant checks). lean-runtime gets them too so that both
# crates are always compiled alike (a `-C` flag such as `panic=abort` must
# agree between them). rustc runs in the crate's directory (`build_locked`):
# a relative path in these flags is relative to it.
LEANRT_FLAGS = os.environ.get("L2R_LEANRT_RUSTFLAGS", "").split()

# `Nat` and `Int` are Reussir's built-in integers (rcgmp; needs a Reussir
# built with rcgmp and the patches `check_rcgmp` checks). Until 2026-10-26
# L2R_INT_BACKEND=leanrt chose leanrt's own words and GMP numbers instead
# (clean-integration D8 removed it); the variable may still say `rcgmp`.
INT_BACKEND = os.environ.get("L2R_INT_BACKEND") or "rcgmp"
if INT_BACKEND == "leanrt":
    sys.exit("l2r: L2R_INT_BACKEND=leanrt: the leanrt representation of Nat and Int was removed on "
             "2026-10-26 (clean-integration D8); Nat and Int are Reussir's built-in integers (rcgmp)")
if INT_BACKEND != "rcgmp":
    sys.exit(f"l2r: L2R_INT_BACKEND={INT_BACKEND}: Nat and Int have one representation, rcgmp")
# Under rcgmp, `Nat` and `Int` are type arguments of the runtime's generic
# textures (typed arrays and cells of them, once-cell constants, the boxes
# of big values): the Reussir that rcgmp needs renders them there as an
# owned handle (local patch R2, which `check_rcgmp` requires). (Until
# 2026-10-25, L2R_RCGMP_TYPE_ARGS=0 kept them out, for measurements; the
# variable is ignored now, with a warning.)
if os.environ.get("L2R_RCGMP_TYPE_ARGS") is not None:
    sys.stderr.write("l2r: warning: L2R_RCGMP_TYPE_ARGS: guard mode was removed on 2026-10-25; "
                     "the variable is ignored\n")

# Extra rustc flags for the textures rrc compiles (L2R_TEXTURE_RUSTFLAGS,
# split on spaces), added after NATIVE_FLAGS in the rustc wrapper rrc runs
# (`rustc_wrapper`): L2R_LEANRT_RUSTFLAGS does not reach the textures, and a
# build for valgrind needs `-C target-feature=-sve,-sve2,-dotprod` in both.
# The wrapper's text names them, so rrc's texture cache keeps such builds
# apart.
TEXTURE_FLAGS = os.environ.get("L2R_TEXTURE_RUSTFLAGS", "").split()

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
    a patched Reussir) gets its own directory, and so do another rustc
    (L2R_RUSTC), extra flags (L2R_LEANRT_RUSTFLAGS), another lean-runtime
    checkout (L2R_LEAN_RUNTIME) and extra features
    (L2R_LEAN_RUNTIME_FEATURES): a build with other settings never rebuilds
    the rlibs that a concurrent build's rrc is reading or linking."""
    def key(text):
        return hashlib.sha256(text.encode()).hexdigest()[:12]
    out = LEANRT_OUT
    if REUSSIR.resolve() != (ROOT / "reussir").resolve():
        out = out / ("rt-" + key(str(REUSSIR.resolve())))
    if RUSTC != DEFAULT_RUSTC.resolve():
        out = out / ("rustc-" + key(str(RUSTC)))
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
    directory would give an rlib with other bytes, and rrc's texture cache,
    which hashes the rlibs, would miss on every texture.
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
    # RUSTFLAGS), change the release profile (CARGO_PROFILE_*: leanrt, a
    # plain rustc build, never sees them, so the two crates would be
    # compiled differently, e.g. lean-runtime at another opt-level), turn on
    # unstable cargo features (CARGO_UNSTABLE_*), wrap rustc, or move the
    # build (CARGO_BUILD_BUILD_DIR moves its intermediate files out of the
    # target directory). Also used for `cargo metadata` (cargo_link_order).
    env = dict(os.environ, RUSTC=str(RUSTC), RUSTFLAGS=" ".join(NATIVE_FLAGS + LEANRT_FLAGS))
    for v in list(env):
        if v in ("RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "CARGO_TARGET_DIR", "CARGO_BUILD_TARGET",
                 "CARGO_ENCODED_RUSTFLAGS", "CARGO_BUILD_RUSTFLAGS", "CARGO_BUILD_RUSTC",
                 "CARGO_BUILD_RUSTC_WRAPPER", "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
                 "CARGO_BUILD_BUILD_DIR", "CARGO_INCREMENTAL") \
                or v.startswith(("CARGO_PROFILE_", "CARGO_UNSTABLE_")) \
                or (v.startswith("CARGO_TARGET_") and v.endswith("_RUSTFLAGS")):
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
# right place: (patch, file of the Reussir checkout, a text the patch adds
# there). A patch is named NN-x, as its file reussir-bugs/patches/NN-x-*.patch
# (NN: its entry, reussir-bugs/NN-*.md); the base is upstream Reussir
# 95d9a1c8 plus reussir-bugs/patches/series. Plain upstream fails the first
# check. 23-f: rrc's lowering pipeline (through the C API; the C++ bridge
# has a copy) frees the records of a recursive type that is neither Direct
# nor TailLoop through the per-thread drop stack of 23-a to 23-e (worklist
# drops), not through upstream's retcon coroutines, whose memory grows by
# one suspended frame per level of the value being freed
# (reussir-bugs/23-worklist-drops.md). The check also refuses the checkout
# of a base before Phase 2, whose drop glue pushed onto a stack that leanrt
# no longer reads (patches 02-a to 02-e and 09-a, now out of the series).
# 23-k and 23-m: that drop stack is shared with leanrt, whose pending stack
# is built on it (runtime/leanrt/src/pending.rs): the end work after the
# outermost drain (23-k: set_end_work, want_end_work) and steps, depth and
# drain for a host (23-m; 23-l, the runs of cells, comes between them).
# leanrt would also fail to compile without them.
# 21-a (entry 21, inc/dec cancellation of integer members of [value]
# records) is an optimization of code with rcgmp integers, 23-p (one
# release function's pending records as cells, fewer instructions than
# links) an optimization of the drops, and mlir-rcgmp's pin cc73b218
# (quotient-only division; upstream since #844, before as patch 20-f) a
# faster dependency: nothing needs them, so they are not checked.
REQUIRED_REUSSIR_PATCHES = [
    ("23-f", "lib/CAPI/Passes.cpp", "options.worklistDrops = worklistDrops"),
    ("23-k", "crates/reussir-rt/src/drop_stack.rs", "pub fn set_end_work"),
    ("23-m", "crates/reussir-rt/src/drop_stack.rs", "pub unsafe fn defer_step"),
    # 23-n and 23-o: the glue's pending records wait linked through their
    # own headers (defer_wide), not one stack entry each: without them a
    # chain whose levels each leave a record of another type pending takes
    # 24 bytes per level (RtAltTreeFree's bounds are native's).
    ("23-n", "crates/reussir-rt/src/drop_stack.rs", "pub unsafe fn defer_wide"),
    ("23-o", "lib/Conversion/BasicOpsLowering/DropStackLowering.cpp", "__reussir_drop_defer_wide"),
    # The one-word box `LAny` keeps its payload's type number in the top 16
    # bits of a tagged handle (reussir-bugs/07-tagged-top-bits.md).
    ("07-a", "lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp", "taggedBoxAddress"),
]
REUSSIR_HELP = ("build with upstream Reussir 95d9a1c8 plus the patches of "
                "reussir-bugs/patches/series (reussir-bugs/README.md)")


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
                     f"(`{symbol}` in {rel}), which lean2rr requires: {REUSSIR_HELP}")


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


# What Nat and Int (rcgmp) need of the Reussir checkout beyond its rcgmp
# feature: local patch R1 (20-a: Lean's division modes and `floormod2expi`
# as bigint intrinsics, which the prelude calls) and R2 (`Nat` and `Int` at
# polyffi type arguments as `reussir_rt::rcgmp::Mpz`, which leanrt
# re-exports; upstream since #824 and #843, so its marker is upstream code
# and refuses only a Reussir from before them): (patch, file, symbol), as
# REQUIRED_REUSSIR_PATCHES.
RCGMP_REUSSIR_PATCHES = [
    ("R1", "library/core/src/intrinsic/bigint.rr", "divsi_lean"),
    ("R2", "crates/reussir-rt/src/rcgmp.rs", "pub struct Mpz"),
]


def check_rcgmp():
    """Nat and Int (rcgmp) need a Reussir built with its `rcgmp` feature
    (`rrc --help` lists the features) and the changes of
    RCGMP_REUSSIR_PATCHES."""
    rrc = REUSSIR / "build" / "bin" / "rrc"
    help_text = subprocess.run([str(rrc), "--help"], capture_output=True, text=True).stdout
    if not any(l.split()[:2] == ["rcgmp", "enabled"] for l in help_text.splitlines()):
        sys.exit(f"l2r: lean2rr needs a Reussir built with its rcgmp feature (Nat and Int); "
                 f"{rrc} lists none enabled (rrc --help, Features)")
    for patch, rel, symbol in RCGMP_REUSSIR_PATCHES:
        src = REUSSIR / rel
        if not src.is_file() or symbol not in src.read_text():
            sys.exit(f"l2r: lean2rr needs the Reussir change {patch} (Nat and Int) "
                     f"(`{symbol}` in {rel}), which the Reussir checkout {REUSSIR} lacks")


def core_interface():
    """The interface (`.rri`) of Reussir's core
    package (`library/core`: the built-in `Nat` and `Int`, `core::num`, and
    `core::intrinsic::bigint`), which rrc loads with `--extern core=` in
    package mode (the core package compiled into rrc has no `core::num`).
    Built with the checkout's rrc, in leanrt's build directory (one per
    Reussir checkout), again when core's sources or rrc change."""
    out = leanrt_out()
    src = REUSSIR / "library" / "core" / "src"
    rrc = REUSSIR / "build" / "bin" / "rrc"
    h = hashlib.sha256()
    for f in sorted(src.rglob("*.rr")):
        h.update(str(f.relative_to(src)).encode())
        h.update(f.read_bytes())
    h.update(str(rrc.resolve()).encode())
    h.update(str(rrc.stat().st_mtime_ns).encode())
    rri = out / "core.rri"
    build_locked(out, out / "core.rri.stamp", [rri], h.hexdigest(),
                 [str(rrc), "--package-root", str(src), "--package-name", "core", "--builtin",
                  "--emit", "rri", "-o", str(rri)], src)
    return rri


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


# Reussir's integer runtime (rcgmp), the archive that rrc links when its
# rcgmp feature is on (RCGMP_RUNTIME_ARCHIVE, Reussir's driver/link.rs).
RCGMP_RUNTIME = "libRCGMPRuntime.a"


def rcgmp_runtime_link(libdirs, tmp):
    """Reussir's integer runtime as rrc finds it (in the first of the
    --polyffi-libdir directories `libdirs` that has it), under a name of
    its own, `libl2r_rcgmp.a` (a symbolic link in the build's temporary
    directory `tmp`), for a --link-lib before GMP's (main): rrc names the
    archive itself, and rustc refuses a library named twice on its command
    line."""
    for d in libdirs:
        archive = Path(d) / RCGMP_RUNTIME
        if archive.is_file():
            link = Path(tmp) / "libl2r_rcgmp.a"
            link.symlink_to(archive)
            return link
    sys.exit(f"l2r: no {RCGMP_RUNTIME} (Reussir's integer runtime) in "
             + ", ".join(str(d) for d in libdirs))


def checkout_of(lean2rr):
    """The lean2rr checkout whose build the binary `lean2rr` is
    (`<checkout>/lean2rr/.lake/build/bin/lean2rr`), or None."""
    tail = [p.name for p in lean2rr.parents[:4]]
    return lean2rr.parents[4] if len(lean2rr.parents) > 4 and tail == ["bin", "build", ".lake", "lean2rr"] else None


def shim_dir():
    """The directory of lean2rr's shim library (lean2rr/L2RShim.lean, built
    with lean2rr) to pass as L2R_SHIM_DIR: this checkout's build for this
    checkout's lean2rr; for another lean2rr binary (L2R_LEAN2RR) the
    `lib/lean` directory of that binary's own build (`../../lib/lean` from
    the binary, where lean2rr itself looks when L2R_SHIM_DIR is unset), so
    that a binary gets the shim built with it, and this checkout's only
    when that directory has no shim (a copy of the binary alone)."""
    if LEAN2RR == OWN_LEAN2RR.resolve():
        return OWN_SHIM_DIR
    own = LEAN2RR.parent.parent / "lib" / "lean"
    return own if (own / "L2RShim.olean").is_file() else OWN_SHIM_DIR


def note_mixed_checkouts(shim):
    """One line on stderr when the lean2rr binary is not this checkout's
    build: the driver, the prelude, leanrt and lean-runtime come from this
    checkout (L2R_LEAN_RUNTIME aside), so a build that mixes checkouts says
    which parts it took from where. Silent for this checkout's lean2rr."""
    if LEAN2RR == OWN_LEAN2RR.resolve():
        return
    co = checkout_of(LEAN2RR)
    sys.stderr.write(f"l2r: lean2rr {LEAN2RR} ({f'checkout {co}' if co else 'not in a lean2rr checkout'}) "
                     f"with the shim in {shim}, the prelude {PRELUDE}, leanrt {LEANRT_SRC.parent} "
                     f"and lean-runtime {LEAN_RUNTIME} (driver checkout {ROOT})\n")


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
    # program's modules and Lean's library): the build of the lean2rr binary
    # in use (`shim_dir`), also when L2R_LEAN2RR is a copy of the binary
    # elsewhere.
    shim = shim_dir()
    env["L2R_SHIM_DIR"] = str(shim)
    note_mixed_checkouts(shim)
    # rrc compiles each of the prelude's textures with its own rustc run,
    # most of its time on a small program; this directory keeps the bitcode
    # (rrc's texture cache, a local patch on the old stack and upstream
    # Reussir #690; an rrc without a cache ignores the variable). rrc keys
    # each entry by everything the bitcode depends on, the texture, rustc
    # (here the rustc-native script, whose text names the rlibs and the
    # flags), its options and the libraries in the --polyffi-libdir
    # directories (leanrt's build directory among them), so all builds share
    # one directory. rrc prunes it (llvm::pruneCache): it removes entries
    # (llvmcache-*) not read for a week and keeps the total at most 1 GiB.
    # It never removes other files, such as the <hex>.bc entries of the old
    # local patch. An empty value turns the cache off.
    env.setdefault("REUSSIR_FFI_CACHE_DIR", str(LEANRT_OUT / "polyffi-cache"))

    check_rcgmp()
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
        libdirs = [rt, deps, Path(target_libdir), rlib.parent]
        # rrc runs in the temporary directory: it leaves its polymorphic-FFI
        # scratch files (reussir_rust_module_*) in the current directory.
        rrc = ([str(REUSSIR / "build" / "bin" / "rrc"), str(rr), "-o", str(Path(args.output).resolve()),
                "--emit", args.emit, "-O", args.opt,
                "--polyffi-rust-path", str(rustc_wrapper(rlib, lr))]
               + [a for d in libdirs for a in ("--polyffi-libdir", str(d))]
               # In dependency order: GNU ld reads each archive once, where
               # it stands, and takes from it only the members that define
               # a symbol still undefined there. leanrt, then lean-runtime,
               # which leanrt calls, and its dependencies, then Reussir's
               # integer runtime, which the program and leanrt call, then
               # GMP, which that runtime calls. rrc links the integer
               # runtime itself, but after every --link-lib, followed by
               # `-l dylib=gmp` (`-Bdynamic -lgmp`, as needed): with GMP's
               # archive first, nothing took a member from it, the
               # runtime's GMP symbols stayed undefined until `-lgmp`, and
               # the first -L directory with a libgmp decided. That was
               # the toolchain's lib/, which has no libgmp.so, so GMP was
               # static by accident; with L2R_GMP=/usr/lib/<triple>/libgmp.a
               # (a directory that has libgmp.so too) the executable needed
               # libgmp.so.10. Passed here before GMP, the integer runtime
               # brings in its members, libgmp.a defines every GMP symbol
               # they use, and `-lgmp` and rrc's own copy of the runtime
               # add nothing: GMP is static whatever directories hold a
               # libgmp.so (tests/runtime/run.sh checks that an executable
               # needs no libgmp).
               + ["--link-lib", str(rlib)]
               + [a for r in lr.rlibs for a in ("--link-lib", str(r))]
               + ["--link-lib", str(rcgmp_runtime_link(libdirs, tmp))]
               + ["--link-lib", str(gmp_archive())]
               # Reussir's in-place variant reuse skips stores of fields that
               # the packed record layout moves (RcCreateFusion copy
               # avoidance): keep declaration-order layouts until that is fixed.
               + ["--no-pack-record-members"]
               # Before upstream Reussir ea240b19 (#758), rrc compiled with
               # LLVM's static relocation model unless told otherwise, but
               # linked a position-independent executable, so read-only data
               # with absolute addresses (closure vtables) needed text
               # relocations (DT_TEXTREL) with GNU ld and failed with lld
               # (Reussir issue 5, now retired; once patch 05-a). Since
               # ea240b19, PIC is rrc's default for executables: the flag is
               # redundant there but harmless, and kept for older bases.
               # Native Lean executables are PIEs without text relocations.
               + ["--relocation-mode", "pic"]
               # The built-in integers (Nat and Int) are declared in
               # Reussir's core package, which rrc loads as an interface in
               # package mode (`core_interface`).
               + ["--package-name", "prog", "--extern", f"core={core_interface()}"]
               # Extra rrc flags for experiments (L2R_RRC_FLAGS, split on spaces).
               + os.environ.get("L2R_RRC_FLAGS", "").split())
        if args.no_reuse_across_call:
            run(rrc, env=env, cwd=tmp)
        else:
            res = subprocess.run(rrc + ["--reuse-across-call"], env=env, cwd=tmp, capture_output=True, text=True)
            if res.returncode < 0:
                # rrc crashed (RcCreateFusion's structural type comparison
                # recursed forever on two structurally equal recursive types,
                # e.g. a user list and `List`; fixed in Reussir #654): retry
                # without reuse across calls, a fallback for unknown crashes.
                # tests/runtime/run.sh fails a test whose build log has this
                # line, so that a new Reussir crash is not hidden from a gate.
                sys.stderr.write(f"l2r: rrc crashed (signal {-res.returncode}); retrying without --reuse-across-call\n")
                run(rrc, env=env, cwd=tmp)
            elif res.returncode != 0:
                sys.stderr.write(res.stdout + res.stderr)
                sys.exit(res.returncode)


if __name__ == "__main__":
    main()
