# 25. rrc's texture cache is keyed on paths, not on the contents of the libraries

**Kind:** sharp edge. Not a bug: upstream documents the rule that the
library directories given to rrc are fixed inputs, and that a changed
library gets a new path. A caller that rebuilds a library in place
breaks the rule, and rrc then reuses old texture code with no message.
lean2rr's driver keeps the rule; there is no Reussir patch.

## Summary

**Kind:** sharp edge (a documented rule that is easy to break).
**Status:** worked around in `scripts/l2r.py` since the move to
`36a55a0f` (2026-11-17). No patch. In the port's first gate
(2026-11-18), `tests/runtime/texture-cache-check.sh` passed, and the
747 runtime tests built with one shared store.

**Upstream (2026-11-17):** By design at `36a55a0f` (#852, `71142424`).
Upstream's own lit tests hit the same failure after a rebuild of the
runtime in place, and #967 (`579b25fa`) changed the test configuration,
not rrc.

## Context

- **Texture.** The Rust body of an `#[ffi(import)]` function. rrc gives
  it to rustc, once for each instance, and links the bitcode that rustc
  makes into the program. A texture can inline code of the Rust
  libraries that it uses (for lean2rr: `libleanrt.rlib` and Reussir's
  runtime `libreussir_rt.rlib`).
- **The cache.** rustc is slow, so rrc keeps each texture's bitcode. On
  the bases up to `95d9a1c8` (#690) the cache was off unless the
  variable `REUSSIR_FFI_CACHE_DIR` named a directory, and its key had
  the bytes of rustc, the report of `rustc -vV`, the host CPU, and the
  name and bytes of each library file in the `--polyffi-libdir`
  directories.
- **Since #852** the cache is a store for each user,
  `${XDG_CACHE_HOME:-~/.cache}/rrc/cache.db`. It is always on. rrc does
  not read `REUSSIR_FFI_CACHE_DIR` any more, and there is no switch that
  turns the cache off.

## What rrc does at 36a55a0f

The key (`lib/RustCompiler/RustCompiler.cpp`) is a hash of:

- the string `reussir-polyffi-bitcode-v2`;
- the absolute path of rustc (not its bytes, not its version);
- the texture's source;
- the rustc options: `-A warnings --crate-type cdylib --emit=llvm-bc`,
  one `-L <absolute directory>` for each library directory, and the
  additional arguments.

The contents of the libraries, the contents and version of rustc, and
the host CPU are not in the key. The comment in the source says so:
"Dependencies are baked by rene and fixed at the call boundary. Identify
the compilation request, without reading or watching the contents of
libraries." rrc makes a path absolute but does not resolve symbolic
links.

## Symptom and repro

The repro needs a Rust library built two times, so it is not in
[`repros/`](repros/) (`run.sh` builds plain Reussir programs). It was
run on pristine `36a55a0f` on 2026-11-17:

- A library crate, version 1: `#[repr(C)] struct S { a, b }`, a static
  `G = S { a: 1, b: 100 }`, `#[inline] fn k()` that returns 1111, and
  `#[inline] fn b()` that reads `G.b`.
- Version 2 of the same crate: `S { a, pad: [u64; 4], b }`,
  `G = S { a: 1, pad: [7; 4], b: 200 }`, and `k()` returns 2222.
- A Reussir program with two textures that call `k()` and `b()`. It
  prints `k * 1000000 + b`.

Steps, with the library file always at one path:

| Step | Library | Cache | Output |
|---|---|---|---|
| 1 | version 1 | empty | `1111000100` |
| 2 | version 2, built in place | the cache of step 1 | `1111000007` |
| 3 | version 2 | a new, empty cache | `2222000200` |

In step 2, `k` is the old 1111 (old code, inlined into the texture), and
`b` is 7: the old texture reads offset 8 of the new static, which is
`pad[0]`. So the result is not only an old value: with a changed layout
it is a read at a wrong offset. There is no message, and the link
succeeds, because the names of the symbols do not depend on the
contents.

## Why it is not a bug

Upstream's rule is written down:

- #852 changed the design document of the polymorphic FFI: "The key
  identifies the Rust source, effective compiler options and selected
  compiler/library paths. Rene bakes dependencies with locked, offline
  builds; these inputs are fixed at the compilation call boundary."
- #852 deleted the test of a library replaced in place
  (`polyffi_cache_swap.rr`) and added `polyffi_cache_deps.rr`, which
  uses two directories for two versions of a library.
- rene, Reussir's package manager, gives rrc directories whose paths
  change when their contents change.
- #967 names this failure for upstream's lit tree ("rebuilds in place
  ... served bitcode referring to symbols the new runtime no longer
  has") and changes only the test configuration.

What is weak (an issue, not a bug): the help text of `--polyffi-libdir`
and the README of the cache crate do not say that a library directory
must not change. A user who gives rrc a cargo `target/.../deps`
directory by hand gets step 2. The same holds for a toolchain updated
in place: the key has the path of rustc, not its version (read, not
run).

## lean2rr

lean2rr rebuilds `libleanrt.rlib` in place, and a developer rebuilds
Reussir's runtime in place. So without a change in the driver, a build
after an edit of leanrt could use textures with the old leanrt code
inlined. This was shown on the port's Reussir build with a copy of the
driver without the fix: `leanrt::string::length` changed to answer 1000
more, and the program still printed the old length.

What `scripts/l2r.py` does (`rrc_env`, `rrc_command`):

- **The digest is in the path of rustc.** The driver gives rrc a small
  script as rustc, named `rustc-native-<hash of its text>`. The text has
  a line with the digest of the leanrt build. That digest covers
  leanrt's sources, the path of rustc, the report of `rustc -vV`, the
  host CPU's features as rustc sees them, the flags, lean-runtime's
  digest, and the name, size and modification time of
  `libreussir_rt*.rlib`. The driver stops when leanrt's sources change
  while leanrt is built, so a digest never names other sources than the
  ones that were compiled. A changed runtime gives another text,
  another script path, and so another key for every texture. An
  unchanged runtime gives the same path, and the cache stays warm.
- **The cache is in lean2rr's directory.** The driver sets
  `XDG_CACHE_HOME` for the rrc process only, to `L2R_POLYFFI_CACHE`
  (default `runtime/leanrt/target/rrc-cache`; empty: a directory inside
  the build's temporary directory, so every texture is compiled again).
  lean2rr's builds do not read or write `~/.cache/rrc`. The driver also
  sets `XDG_CONFIG_HOME` for rrc to a directory inside the cache
  directory, so the settings of the user's other rrc builds
  (`rrc/config.ncl`) do not change lean2rr's store.
- `REUSSIR/build/lib` is not a library directory of the textures (the
  maintainer's port had added it).

Test: `tests/runtime/texture-cache-check.sh` builds a program, builds it
again (no new cache entry), changes one `#[inline(always)]` function of
a copy of leanrt's sources (the program must print the new answer, and
the cache must get new entries), and puts the sources back (the old
answer, no new entry).

`reussir-bugs/repros/run.sh` runs rrc directly: it gives each run a
new, empty store in its work directory. Not covered: a run of rrc by
hand. After a rebuild of Reussir's runtime, such a run needs a new
`XDG_CACHE_HOME`.

## A cost of the same store

rrc opened the store once for each texture, and each open costs time
that grows with the store's size. That is
[entry 29](29-texture-store-open.md), with patch 29-a in the series.

## Upstream note

Not reported. A report would ask for one line in the help of
`--polyffi-libdir` ("a library directory is a fixed input: give a
changed library a new path"), and maybe a switch that turns the cache
off for measurements. Hashing the libraries again is what #852 removed
on purpose.
