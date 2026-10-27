# lean-to-reussir

A compiler from Lean 4 programs to [Reussir](https://github.com/reussir-lang/reussir),
an RC-based functional language with token-based memory reuse.

`lean2rr` reads the compiler's intermediate code (LCNF) of a compiled Lean
program, monomorphizes it, runs Lean's own mono-phase optimizations on it,
and lowers the result to typed Reussir source. Reussir then takes care of
ownership, reference counting and memory reuse. The design is described in
[`docs/translation-plan.md`](docs/translation-plan.md).

Status: see [`docs/implementation-status.md`](docs/implementation-status.md) (what is supported, how values are represented, test and benchmark results, known differences from native Lean).

Implementation notes: [`docs/implementation/`](docs/implementation/README.md) catalogs the implementation's tricks and special cases (why lean2rr does something, where, and what breaks without it).

Design site: [`docs/site/index.html`](docs/site/index.html) is an illustrated overview of the architecture and design (static HTML; open it from a clone).

## Requirements

- Lean v4.34.0 (via elan; `lean2rr/lean-toolchain`). lean2rr reads only
  `.olean` files of the toolchain it is built with, so programs are compiled
  with that toolchain too. The test runners and `scripts/l2r.py` take it
  from `L2R_LEAN_TOOLCHAIN` (a toolchain directory), by default the elan
  toolchain the pin names, whatever elan's default is
  (`scripts/toolchain.sh`).
- Reussir built from source (LLVM/MLIR 23, Clang 23), checked out into
  `reussir/`: upstream `95d9a1c8` plus the patches of
  `reussir-bugs/patches/series` (head `c1170ff9`: branch
  `l2r-base12`; see
  [`reussir-bugs/README.md`](reussir-bugs/README.md#applying-the-patches)).
  Its build needs GMP 6.2 or later (`gmp.h`, `libgmp`), a CMake that
  knows `cxx_std_26` for Clang (CMake 4.4.4 works; Ubuntu 24.04's 3.28
  does not) and the libstdc++ 14 headers (Ubuntu 24.04:
  `libstdc++-14-dev`). After a change of the C++ headers, delete the
  build directory and configure again
  ([building Reussir](reussir-bugs/README.md#building-reussir)).
- The shared runtime crate lean-runtime, a git submodule
  (`third_party/lean-runtime`): clone with `git clone --recurse-submodules`,
  or run `git submodule update --init` in a checkout, and again after a
  pull that moves its pin (see [`runtime/README.md`](runtime/README.md),
  "The shared crate lean-runtime"). `scripts/l2r.py` builds it offline.
- Python 3.11 or later (`scripts/l2r.py` reads lean-runtime's `Cargo.toml`
  with `tomllib`)

## Building

1. Build lean2rr: `cd lean2rr && lake build`. This builds the binary
   `lean2rr/.lake/build/bin/lean2rr` and its shim library `L2RShim`
   (`lean2rr/.lake/build/lib/lean`; both are default targets).
2. Once, fill cargo's registry cache with the crates that lean-runtime
   needs (the driver builds it offline): run `cargo fetch --locked` in
   `third_party/lean-runtime` with the cargo of the pinned Rust toolchain
   (next to the rustc that `scripts/l2r.py` uses: `L2R_RUSTC`, by default
   that of `nightly-2026-08-31`).
3. Translate and build a program. Compile it with the Lean toolchain that
   lean2rr is pinned to (in bash, `. scripts/toolchain.sh` puts it first on
   `PATH`), then run the driver, which runs lean2rr and rrc, and builds and
   links the runtime:

   ```
   lean -o Hello.olean Hello.lean
   python3 scripts/l2r.py Hello.lean -o hello    # or: scripts/l2r.py Hello --lean-path DIR -o hello
   ./hello
   ```

   Set `L2R_REUSSIR` when Reussir is not checked out in `reussir/`.
   `--keep-rr FILE` keeps the generated Reussir text, `--emit llvm-ir`
   writes LLVM IR instead of an executable, and `--disable-opt` and
   `--enable-opt` turn lean2rr's optional passes off or on. The driver's
   docstring lists its environment variables;
   [`runtime/README.md`](runtime/README.md#building-and-linking) describes
   its steps, and [`tests/README.md`](tests/README.md) the test runners
   (`tests/runtime/run.sh [NAME...]` builds programs both ways and
   compares their runs).

## Layout

- `lean2rr/` — the translator (a Lake package); its optional passes live in
  `lean2rr/LeanToReussir/Opt/`, listed in `Opt/Registry.lean`
  (`lean2rr --list-opts`)
- `runtime/` — the runtime: the prelude `prelude.rr` included in every
  program, and the Rust crate `leanrt` (see [`runtime/README.md`](runtime/README.md))
- `scripts/` — `l2r.py`, the driver (lean2rr, then rrc, linking the runtime)
- `third_party/lean-runtime` — the shared runtime crate (Lean's runtime
  rules, shared with another Lean translator), a submodule pinned by commit; `leanrt` and the
  prelude call it
- `reussir-bugs/` — the open Reussir issues lean2rr has met (one file per entry; bugs, costs and
  the other kinds; the ones fixed upstream are in git history), the local Reussir patches and the repros (see [`reussir-bugs/README.md`](reussir-bugs/README.md))
- `docs/` — design documents
- `tests/` — the classic test corpus and its native-Lean oracle (see [`tests/README.md`](tests/README.md))
