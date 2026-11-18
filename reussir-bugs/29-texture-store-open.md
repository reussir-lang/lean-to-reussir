# 29. rrc opens the texture cache's store once for each texture

**Kind:** cost (build time). Not a bug: rrc's output is correct. rrc
keeps compiled textures in a store (entry 25). It opened and closed
that store for every texture of a program, and each open is expensive:
it syncs the store to disk and reads the whole database. Patch 29-a
opens the store once for a module's textures. It is an optimization.

## Summary

**Kind:** cost. **Status:** patched (29-a), patch 9 of the series on
upstream `36a55a0f` (Reussir branch `l2r-base13-final`, commit
`2b9d8ca0`; 4 files, +53/-9, without `tests/` 3 files, +35/-8).
`scripts/l2r.py` does not check for the patch: without it builds are
slower, with the same results.

**Upstream (2026-11-18):** Open at `36a55a0f`: new with #852, which put
the texture cache into a store of the compcache crate. Not reported:
the maintainer takes changes from this directory. The patch applies to
a clean `36a55a0f` alone.

## Context

- **Texture.** The Rust body of an `#[ffi(import)]` function. rrc gives
  each one to rustc and keeps the bitcode in a cache
  ([entry 25](25-texture-cache-key.md) describes the cache and its
  key). A small lean2rr program has about 75 to 130 textures, a large
  one more than 300.
- **The store.** Since #852 the cache is one SQLite database,
  `rrc/cache.db` under the user's cache directory, managed by the
  compcache crate (pinned by revision in Reussir's `Cargo.toml`).
- **What an open does** (compcache, `src/cache.rs` and `src/schema.rs`,
  read): it takes a lock that is global to the store's directory, opens
  SQLite in WAL mode with `synchronous=FULL`, runs and commits a
  transaction, runs `PRAGMA quick_check` over the whole database, syncs
  the directory, and runs recovery. A close checkpoints the WAL. The
  crate's configuration has no switch for the check or for the sync
  mode.

## Symptom

lean2rr's first gate on this base was slow to build, also when every
texture was in the cache: a sample of 20 small tests took 10.7 s for
each test with a warm store, where the last gate on `l2r-base12` took
about 7.1 s for each test with 8 runs in parallel.

Where the time goes, one program, the same `.rr` on both bases (RtNat,
124 textures, warm cache, rrc to an executable; one process at a time):

| Cache | wall | What `strace` shows |
|---|---|---|
| `l2r-base12`, the old file cache | 3.2 s | no fsync |
| `36a55a0f`, a store of 0.9 to 4 MB on disk | 5.0 s | 744 fsync (6 for each texture), 2.27 s |
| `36a55a0f`, the gate's store (140 MB, 19,254 entries) on disk | 9.8 s | 744 fsync, and 4,628,127 `pread64`: the whole database is read at every open |
| `36a55a0f`, a small store on a memory file system | 2.7 s | the fsync cost is gone |
| `36a55a0f`, the gate's store on a memory file system | 8.7 s | the read of the database stays |

In the first stage of rrc (to the end of texture gathering), a warm
lookup costs about 19 ms with a small store and about 53 ms with the
140 MB store; on `l2r-base12` about 1.5 ms. Texture gathering, warm:
RtNat 0.18 s to 2.41 s, a classic program (Rbtree, 66 textures) about
0.1 s to 1.28 s, RtTArrKinds (308 textures) 0.28 s to 7.47 s, lean-zip's
compress (227 textures) 0.24 s to 4.09 s.

## Cause

`lib/RustCompiler/RustCompiler.cpp:321` at `36a55a0f`:
`compileRustSourceToBitcode` calls `reussir_polyffi_cache_open` and
closes the handle again. `compilePolymorphicFFI`
(`lib/Conversion/CompilePolymorphicFFI/CompilePolymorphicFFI.cpp`) calls
that function once for each texture of the module. So each texture pays
one open and one close of the store.

The opens are serial inside rrc (texture gathering is one thread). They
are also serial across the rrc processes that share a store, because an
open holds the store-wide lock during the check and the syncs: two rrc
processes at once on one store were each slower than one alone
(measured, below).

## lean2rr

Every lean2rr build pays it, for each texture. `scripts/l2r.py` cannot
change it: the open is inside rrc. Two things that a caller can do were
measured: a store on a memory file system removes the sync cost, and a
small store removes the cost of the check. lean2rr's driver does
neither by itself (`L2R_POLYFFI_CACHE` can name such a directory); the
series has the patch.

## Patch

[`patches/29-a-polyffi-store-once.patch`](patches/29-a-polyffi-store-once.patch),
`[rrc] open the polyffi cache store once per module`.

- `include/Reussir/RustCompiler.h`: a handle type `PolyffiCache` (a
  `std::unique_ptr` with a closer) and `openPolyffiCache()`.
  `compileRustSourceToBitcode` gets a last parameter
  `const PolyffiCache *cache = nullptr`. Null: the function opens a
  store for this call, as before (unit tests and other callers do not
  change). A pointer to an empty handle: the open failed, compile
  directly.
- `compilePolymorphicFFI` opens the store before its loop, only when
  the module has a texture to compile, and passes the handle down. The
  handle closes when the function returns, also on an early return.
- Unchanged: the key, the lock for each key, WAL mode, and every
  fallback (a cache error still means "compile with rustc"). A failed
  open is reported once for a module, not once for each texture, and
  each texture then compiles directly.

Not changed, because it is in the compcache crate: the check at an open
(it runs once for a process now, so the store's size no longer matters:
below) and the sync when an entry that is read gets its access time
(129 fsync for 124 textures stay). A process that compiles several
modules opens the store once for each module.

**Tests.** `frontend/polyffi_cache_deps.rr` (two textures) has two new
cases: with a store that cannot be opened, exactly one `Polyffi cache:`
line (two before the patch), and the output equal to the cached build;
with a working store, `rrc -v` logs one `cache opened` line (two on
pristine upstream), and a second run that may not compile succeeds.
The second case depends on the text of compcache's debug log.

**The patch file and the gated compiler.** The file in `patches/` has
this test in its last form. The Reussir branch that the gate used
(`l2r-base13-final`, head `d62797ac`, tree `9066f3fc`) has the form
before it, in which the test made a lock file read-only. Only that one
test file differs (+6/-8); no compiler source differs. So the series of
this folder gives tree `ccdf369d`, not `9066f3fc`.

## Review

Two rounds by an independent reviewer (local notes
`port13/reviews/RV3`, the two "Store opened once" sections).

- Round 1, on a first form that kept the handle in a function-local
  static: correct for rrc, the measured claim reproduced, and the
  reviewer could not break it (no wrong texture, no failed build, no
  blocked second process). Verdict on the form: the handle must be
  owned by the caller, not by a static (a static is closed by a
  destructor at exit, keeps a connection for the life of a process that
  embeds the compiler, and does not try a failed open again).
- Round 2, on the caller-owned form: accepted. Checked by runs: the
  stale-library repro of entry 25 gives its three lines (the contract
  does not change); lean2rr's `texture-cache-check.sh` passes; a store
  that fails in the middle of the loop gives one diagnostic and rc 0;
  a rustc failure on the first texture closes the handle. One
  recommended change to the new lit case (a better thing to observe),
  which is the last form of the test, above.
- Not run: the whole lit suite, Windows and macOS, sanitizer builds.
  clang-format is not installed on the build machine.

## Measured claim

All numbers are wall seconds of one rrc run to an executable on a
shared machine, aarch64 Linux. Both sides run the same command of
lean2rr's driver with the same texture keys; only the rrc binary
differs (the series without and with the patch). No number is a run
time of a compiled program: the patch changes no generated code (the
objects of three lean2rr programs are byte-identical without and with
it, with one warm cache for both sides).

**The author's rows on the patch as it is in the series** (RtNat, 124
textures; 3 runs, min / median; load average 2 to 7):

| RtNat | without, min / median | with 29-a, min / median |
|---|---:|---:|
| warm, small store (0.9 MB) | 4.88 / 5.05 | 3.07 / 3.16 |
| warm, 140 MB store (a copy of the first gate's) | 9.86 / 10.21 | 3.05 / 3.09 |
| cold, empty store | 7.81 / 7.92 | 6.58 / 6.69 |
| cold textures in the 140 MB store (1 run) | 13.24 | 6.46 |
| two processes at once, warm, small store (3 pairs) | 6.08 / 7.00 | 3.24 / 3.46 |
| two processes at once, warm, 140 MB store (3 pairs) | 15.31 / 15.48 | 3.16 / 3.49 |
| two processes at once, cold, empty store (1 pair) | 7.91, 7.94 | 6.79, 6.80 |

System calls of the warm run (`strace -f -c`): fsync 744 to 129;
`pread64` 36,313 to 5,209 with the small store and 4,631,383 to 47,801
with the 140 MB store; `flock` 248 to 125.

**The author's rows on the first form** (the static handle; load
average 4 to 10; its two sides were one unrelated commit apart). The
larger program was measured only on this form; both forms open the
store once in an rrc process:

| Program | Store | without, min / median | with, min / median |
|---|---|---:|---:|
| RtTArrKinds (308 textures) | warm, small (2.4 MB) | 43.34 / 45.92 | 36.22 / 36.49 |
| RtTArrKinds | warm, 140 MB | 55.61 / 55.86 | 36.34 / 38.08 |
| RtTArrKinds | cold, empty store | 52.49 / 56.66 | 46.06 / 46.38 |
| RtTArrKinds | cold textures in the 140 MB store (1 run) | 65.48 | 47.58 |

**The reviewer's rows** (RtNat, a copy of the first gate's store,
134 MB; one priming run, then 3 warm runs, the sides in turn, one
process at a time):

| RtNat, 134 MB store | without | with |
|---|---:|---:|
| first form, load 2.2 to 2.5: warm, min / median of 3 | 9.36 / 9.79 | 3.19 / 3.34 |
| first form: warm, user + system CPU (median run) | 4.68 + 3.68 | 3.26 + 0.28 |
| first form: two processes at once, warm (1 pair) | 15.79, 15.80 | 3.31, 3.32 |
| the series' form, load 7 to 13: warm, min / median of 3 | 9.73 / 10.13 | 3.23 / 3.25 |
| the series' form: warm, user + system CPU (median run) | 4.66 + 3.67 | 3.13 + 0.27 |
| the series' form: priming run (cold textures, 1 run) | 13.40 | 6.59 |
| the series' form: two processes at once, warm (1 pair) | 15.69, 15.73 | 3.32, 3.42 |

The reviewer did not measure the small-store rows, the cold rows of an
empty store, the larger program or the system-call counts.

**What the claim is.** A warm rrc build of a program with 124 textures
goes from about 5 s to about 3.2 s with a small store and from about
10 s to about 3.1 s with a 140 MB store; two such builds at once on one
store no longer slow each other down. With the patch a warm RtNat build
is near the figure of `l2r-base12` (3.2 s, another session and another
build; not measured side by side).

**In lean2rr's final gate** (2026-11-18, the whole series, the store on
a memory file system, load 1.6): the runtime suite's 750 tests took
1582 s, and about 690 s without one outlier program; the first gate
took 4048 s for 747 tests, and the last gate on `l2r-base12` 671 s with
a warm cache. The first 20 tests of one shard took 4.8 s for each test
with a cold store (3.2 s of it rrc and the link), against 18.5 s cold
and 10.7 s warm in the first gate. That comparison mixes four things
that one run cannot separate: this patch, the store on a memory file
system, the six other patches that came after the first gate, and a
much quieter machine.

**Not measured:** the patch alone in a full suite run; the share of
each of the four things above; a store on disk in the final gate;
other platforms.

## What stays slower than on l2r-base12

Not this entry's cost, and not patched: on large programs rrc itself
uses more time than on `l2r-base12` (the MLIR pipeline 12.44 s to
14.73 s for RtTArrKinds and 15.03 s to 19.15 s for lean-zip's compress;
code generation 6.8 s to 11.2 s for lean-zip; one run each, before
this patch). The cause is not attributed to an upstream change. Small
programs do not show it. Measured not to be causes: the frontend and
the loading of core's interface, the borrow analysis, the link, and
rustc's time for a cold texture.

## Upstream note

Not reported. A report would give the system-call counts of one warm
build (744 fsync and 4.6 million `pread64` for 124 textures with a
140 MB store) and the patch. Two more candidates are on compcache's
side: run `quick_check` only when the database was not closed cleanly,
and do not sync when a read only updates an entry's access time.
