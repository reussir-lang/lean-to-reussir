# 35. rrc compiles every texture with rustc again on every build

**Kind:** cost (build time). Not a bug: rrc's output is correct; patch 35-a
is an optimization.

## Summary

**Kind:** cost (build time), with a small optimization.
**Status:** patched (35-a), applied in `./reussir` since 2026-10-04
(`l2r-local` commit `d79f8b70`; made on branch `l2r-polyffi-cache` of a
local Reussir build with the l2r-local patches applied, on `l2r-local`
cc8e5aa5 + 34-a); reviewed
(round FCR: one medium finding, a race, and small ones; a second look:
two more small ones; all fixed in the amended patch). lean2rr uses the
patch when it is there: its driver sets `REUSSIR_FFI_CACHE_DIR` (below).

**Verdict: cost (build time).** rrc compiles the Rust body of every
`#[ffi(import)]` instance (a "texture") with its own rustc process, one
after another: Reussir's documented design
(`docs/design/polymorphic-ffi.md`; [issue 23](23-polyffi-link.md) calls the
compiles "a cost, not part of this issue"). What is fixable is that nothing
is kept between builds: the bitcode of a texture depends only on inputs
rrc can name (the source, rustc, its options and the libraries rustc
reads), and these rarely change between two builds, but every build
compiles every texture again. Every lean2rr program carries the whole
prelude (473 imports), so every build pays for about 470 rustc runs, about
13 s of a small program's 16 s of rrc. Patch 35-a keeps the bitcode in a
content-addressed cache when `REUSSIR_FFI_CACHE_DIR` is set (3 s).

## Symptom and repro

Repro [`repros/bug35-texture-cache.rr`](repros/bug35-texture-cache.rr):
three non-generic imports (`say`, `seed`, `add_two`); the program prints
42. `run.sh` builds it twice with one new `REUSSIR_FFI_CACHE_DIR`, through
a rustc wrapper that counts texture compiles (a `reussir_rust_module_*.rs`
source; rrc's final link through rustc does not count).

**Command.** `rrc bug35-texture-cache.rr -o OUT --emit executable -O
aggressive`, twice.

**Expected.** The second build compiles no texture.

**Actual on ef922049** (and on `l2r-local` cc8e5aa5): the second build
compiles all three again. `run.sh` prints `issue 35   REPRODUCES  second
build: 3 of 3 textures compiled again; both print 42`.

**lean2rr.** `tests/runtime/RtBorrowReleaseOrder.lean` (a small test)
through `scripts/l2r.py`: lean2rr writes 478 imports (the prelude's 473
and the program's), and rrc runs rustc for 474 textures. rrc alone, from
its command line as `l2r.py` gives it, single runs on the loaded test
machine (2026-10-04, load about 9):

| rrc | wall | user | sys |
|---|---|---|---|
| without the cache | 16.1 s | 7.8 s | 9.9 s |
| 35-a, empty cache (fills it) | 16.5 s | 8.2 s | 9.9 s |
| 35-a, full cache | 3.2 s | 3.7 s | 0.4 s |

A rustc run costs about 30 ms, more than half of it in the kernel
(starting a process that maps rustc's 106 MB driver library and the rlibs
it loads).
The 474 runs are about 13 s of the 16 s. With `--emit llvm-ir` (no final
link): 14.6 s without the cache, 2.0 s with a full cache.

## Cause

Where it runs: `LlvmLowering::prepare` (`crates/reussir-backend/src/llvm.rs`)
calls `compilePolymorphicFFI`
(`lib/Conversion/CompilePolymorphicFFI/CompilePolymorphicFFI.cpp`) before
the MLIR lowering pipeline. For every `reussir.polyffi` operation not yet
compiled, it substitutes the texture's placeholders (`monomorphize`) and
calls `compileRustSourceToBitcode` (`lib/RustCompiler/RustCompiler.cpp`),
which writes the source to `reussir_rust_module_XXXXXX.rs` in the current
directory, runs

    rustc -A warnings SRC --crate-type cdylib --emit=llvm-bc -o OUT.bc -L DIR... [-O] [--target T]

with `llvm::sys::ExecuteAndWait`, and reads `OUT.bc` back. Nothing
remembers a result: not across builds, and not within a build (two
operations with the same source would run rustc twice). The temporary
file's random name is the texture's crate name, so even two builds of the
same program differ in the names of the texture's internal symbols; the
code is the same.

Why lean2rr hits it hard: lean2rr writes the whole prelude into every
program, and rrc compiles almost all of it (RtBorrowReleaseOrder: 478
imports, 474 textures), whether the program uses an import or not. So the
cost is almost the same for every program, and most textures are the same
from one program to the next: the eight runtime tests of the verification
below (478 imports each) fill the cache with 918 entries. (Since the
optimization `prelude-liveness`, 2026-10-08, lean2rr writes only the
prelude functions a program uses: a one-line program has 75 textures, not
484. The numbers in this file are from before it.)

## lean2rr

`scripts/l2r.py` sets `REUSSIR_FFI_CACHE_DIR` for rrc to
`runtime/leanrt/target/polyffi-cache` (ignored by git, like the rest of
`runtime/leanrt/target/`), unless the caller sets it; an empty value
turns the cache off. An rrc without 35-a ignores the variable, so nothing
changes there. One directory serves every build: rrc's key covers the
rustc wrapper (`rustc-native`, one per leanrt build directory, whose text
names the extern rlibs and the flags) and the libraries of the
`--polyffi-libdir` directories, which hold leanrt's and lean-runtime's
rlibs, Reussir's runtime and the toolchain's standard library.

One gap had to be closed on lean2rr's side: once lean-runtime gets
dependencies, cargo builds it into `lr-cargo/`, which is not a
`--polyffi-libdir` directory, so the wrapper script's text now also names
lean-runtime's build (`# lean-runtime build <digest>`, `LeanRuntime.digest`);
a new lean-runtime build changes the script and so every key. (leanrt's
rlib would change as well, since it records its dependency's hash, but the
key should not depend on that.)

The cache grows: nothing removes old entries. An entry is about 8 KB; a
leanrt change adds a new set of about 470 (4 MB). Delete the directory to
reclaim the space.

## Patch

Patch file
[`patches/35-a-texture-cache.patch`](patches/35-a-texture-cache.patch)
(commit `968c4b7d` on branch `l2r-polyffi-cache` of a local Reussir build
with the l2r-local patches applied, on 34-a; it touches none of 34-a's
files and applies after 33-a as well; in `./reussir` since 2026-10-04 as
`l2r-local` commit `d79f8b70`). In
`lib/RustCompiler/RustCompiler.cpp`, `compileRustSourceToBitcode` builds
rustc's options first (everything but the source and output files), and
when `REUSSIR_FFI_CACHE_DIR` is set and non-empty:

- **key**: a BLAKE3 digest (`llvm/Support/BLAKE3.h`) of a format tag,
  the toolchain digest (below), every option, and the texture's source,
  each field length-prefixed;
- **toolchain digest**, for each rustc and set of package directories:
  rustc's resolved path, the content of that file (a wrapper script such
  as lean2rr's `rustc-native` is told apart from another, and from
  rustc), its `rustc -vV` report (the toolchain a rustup proxy runs:
  release, commit hash, LLVM version), the host CPU's name and features
  (`llvm::sys::getHostCPUName`/`getHostCPUFeatures`, for `-C
  target-cpu=native`), and for each package directory (an `-L` kind
  such as `crate=DIR` stripped) the name and content of every `.rlib`,
  `.rmeta`, `.so`, `.dylib` and `.dll` in it (the files rustc loads
  crates from). Every file and directory read is *stamped* (device,
  inode, size, modification time and, on POSIX systems, status-change
  time, which no one can set back) just before it is read. A package
  directory's stamp changes with any entry added or removed there,
  also ones rustc never reads (rrc's temporary files when rrc runs in it,
  a cache directory made in it): a changed directory stamp counts only
  if the list of libraries in the directory changed, and is refreshed
  otherwise. The digest is computed once per process (one rrc run;
  hashing reads about 220 MB for lean2rr's directories, most of it the
  toolchain's standard library), and again when a stamp no longer
  matches;
- **caching off**: if rustc cannot be read or run, a library or a
  directory cannot be read, or a file changes while it is hashed, nothing
  is cached for the rest of the run (rustc runs as before), and rrc says
  so once on stderr (`warning: REUSSIR_FFI_CACHE_DIR: no polymorphic-FFI
  caching in this run: <reason>`). rrc's verbose flag lives in its Rust
  driver, out of this code's reach, so the warning is not tied to it; it
  appears only when the cache was asked for;
- **lookup**: the stamps are checked first (a mismatch recomputes the
  digest), then the file `<key in hex>.bc` in the directory is read. An
  entry is the BLAKE3 digest of the bitcode followed by the bitcode; one
  that cannot be read, is shorter than the digest, does not match it or
  does not start with a bitcode magic (raw or wrapper) is a miss. A hit
  returns a copy of the bitcode, and rustc is not run;
- **store**, after rustc succeeded and its bitcode was read, and only if
  every stamp still matches (else rustc may have read a newer library
  than the key describes, and the entry is not stored): write the entry
  to a new temporary file in the directory, `<key>.bc.tmp-<pid>-<random>`
  (created exclusively; the name is unique in its file-name part only, so
  a `%` in the directory is harmless), close it, and rename it over
  `<key>.bc` (atomic on POSIX). Any failure only loses the entry.

```c++
  std::optional<CacheEntry> cacheEntry =
      cacheEntryFor(sourceCode, options, rustcPath, rustcDepsPaths);
  if (cacheEntry)
    if (std::unique_ptr<llvm::MemoryBuffer> cached =
            readCacheEntry(cacheEntry->path))
      return cached;
  ... // the temporary files and the rustc run, as before
  if (cacheEntry && cacheEntry->toolchain->unchanged())
    writeCacheEntry(cacheEntry->path, buffer->getBuffer());
  return buffer;
```

Without the variable the only change is the order of rustc's arguments:
the source and `-o OUT` now come first, and the options keep their
relative order. The patch also adds `TargetParser` to the library's LLVM
components (the host CPU queries), a paragraph to
`docs/design/polymorphic-ffi.md`, and two lit tests.

**Why it is correct.** rustc's output is a function of its inputs: the
source, the command line, the compiler, the crates it loads, and the
target, which `-C target-cpu=native` takes from the host. The key covers
each of them as rrc sees it:

- the source and every option are hashed as they are given to rustc,
  except the two temporary file names. Their random names reach the
  output only as the crate's name, the module's source file name and the
  file names of panic locations, random in every build anyway, so any of
  them is as good as another;
- the compiler: path, file content and `-vV` report. A rustup proxy is the
  same file for every toolchain; its `-vV` report (run in the same
  directory and environment as the compiles) names the toolchain it
  selects. A wrapper script's content names what it adds (lean2rr's names
  its flags, the extern rlibs and lean-runtime's build). The standard
  library ships with the toolchain (its commit hash is in `-vV`), and
  lean2rr also passes its directory as a `--polyffi-libdir`, so its
  content is hashed;
- the crates: rustc looks for crates in the `-L` directories (and the
  sysroot) only, in files with these suffixes; their whole content is
  hashed;
- the host CPU, for `native`;
- and the key describes what rustc read: the stamps are taken before the
  files are read and checked after the compile, so a library replaced
  while rrc runs keeps the texture compiled meanwhile out of the cache,
  and the next texture gets a new digest. A replacement by rename changes
  the inode; a rewrite in place changes the status-change time, even when
  the size is the same and the modification time is put back (`cp -p`,
  `touch -r`); a library added or removed changes the directory's list.

Not covered: files and environment variables read at compile time by a
texture or by the macros of the crates it uses (`include!`, `env!`,
`option_env!`, procedural macros; lean2rr's prelude and runtime crates
have none), the content of files named by a path in an option (a custom
target specification), crates a wrapper script adds from other
directories (lean2rr's are all in hashed directories, or named by the
script's digest line), and a toolchain switched under a rustup proxy
during a run. On systems without POSIX `stat` (Windows), the stamp has no
status-change time, so an in-place rewrite with the same size and the old
modification time put back goes unseen. On POSIX systems, a rewrite
within the same timestamp tick as the stamp would too; on this machine's
kernel a file whose timestamps were just read gets a fine-grained one at
its next change. The first three and the Windows gap are written in the
patch's comment.

The cache directory must be trusted: entries are checked for damage (a
digest of the bitcode, a bitcode magic), not authenticated, so whoever can
write there chooses the code rrc links.

Concurrency: an entry appears only by a rename of a complete file, so a
reader sees an old complete entry, a new complete entry or none; two
writers of one key write the same bytes (up to the crate name). A
damaged entry (truncated, flipped bits, a crash before data reached the
disk) fails the digest check and is rebuilt.

**Verification.**

- Lit test `frontend/polyffi_cache.rr`: a build fills the cache; a
  second build with a rustc wrapper that fails every compile (but answers
  `-vV`) succeeds and gives the same IR; `-O none` (another option) fails
  with the wrapper, a miss; after every entry is truncated, the wrapper
  build fails (misses), a normal build rewrites the entries, and the
  wrapper build succeeds again. The unpatched rrc fails the second step.
- Lit test `frontend/polyffi_cache_swap.rr` (review FCR-01, FCR-02): a
  rustc wrapper replaces `libfcrdep.rlib` (whose `k()` returns 1111) by a
  version returning 2222 just before the first texture compile. That
  build gives 2222 (and stores only the texture compiled after the
  change, under the new library's key); with the 1111 version back, the
  next build gives 1111. Before the fix it gave 2222: both textures were
  stored under the old library's key. The same with the directory passed
  as `crate=DIR` in `REUSSIR_RUSTC_DEPS`, the library replaced between two
  builds: the second gives 2222 (before the fix 1111, the directory was
  not hashed). Since the second look (FCR2-01, FCR2-02): the same swap
  done in place, with the same size and the old modification time put
  back, then v1 put back the same way: the next build gives 1111; and rrc
  run in a package directory stores both entries.
- Both lit tests and `frontend/ffi_flags.rr`, run with a hand-written lit
  site configuration: pass. The 85 lit tests under `frontend/` and
  `codegen/` that use FFI and need only rrc (no `reussir-opt`, `rene` or
  `rrepl`): all pass. With the first version of the patch, the 84 of them
  then also passed with the cache on (the variable added to the site
  configuration), first empty (56 entries), then full.
- The review's race repro (a wrapper that swaps a library during the first
  compile, then a build with the original library back): the second build
  gives the original library's constants (1111, 1113), as without the
  cache; the old patch gave the swapped ones (2222, 2224). The `crate=DIR`
  case likewise.
- The second look's repros, on the amended patch: the in-place swap
  (`cp` over the library, `touch -r` to its old time) gives the restored
  library's constants (1111, 1113) once it is back, where `24ec14ae` gave
  the swapped ones; rrc run in a package directory (`Lcwd`) runs `-vV`
  once and stores both entries, the second build compiles nothing (with
  `24ec14ae` every lookup recomputed the digest and nothing was stored);
  a cache directory made inside a package directory (`Lsub`): one `-vV`,
  both entries stored; a library added to a package directory during the
  first compile: that texture is not stored. RtString, RtHashMap and
  RtBorrowReleaseOrder from an empty and then a full cache: pass, no
  entry added or replaced by the second run, byte-identical executables.
- Caching off, with the one warning: a dangling library symlink, an
  unreadable library (mode 000), an unreadable package directory, a rustc
  whose `-vV` fails; each build succeeds and stores nothing. Without
  `REUSSIR_FFI_CACHE_DIR` nothing is printed. A cache directory named
  `pct%dir`: entries are stored, no temporary file is left. An entry with
  a correct digest of a payload that is not bitcode: a miss, rewritten.
- lean2rr's runtime tests RtString, RtFloat, RtHashMap, RtTask,
  RtNatStress, RtBorrowReleaseOrder, RtStdioFiles and RtCslInsertion
  (`tests/runtime/run.sh` with `L2R_REUSSIR` at the patched checkout),
  from an empty cache (918 entries; 106 s, including the leanrt build) and
  again with the full cache (no entry added or replaced; 55 s): all pass
  both times, and each test's executable is byte-identical between the two
  runs. Again with the amended patch, lean2rr built from this branch and
  its builds of leanrt in the crate's directory, from a new cache
  directory: 90 s and 59 s, the same 918 entries, all pass,
  byte-identical executables.
- RtBorrowReleaseOrder's LLVM IR (`--emit llvm-ir`) without the cache and
  from the full cache: identical once the names that come from the
  textures' random crate names are normalized (crate name, crate
  disambiguator, legacy symbol hash, `alloc_` content hashes, GUID
  metadata); two builds from the full cache give byte-identical IR.
- Invalidation, RtBorrowReleaseOrder through `l2r.py`, counting the
  rustc-native runs under strace:

  | change | texture compiles | new entries |
  |---|---|---|
  | none | 0 | 0 |
  | `-O none` | 474 | 474 |
  | `-O none` again | 0 | 0 |
  | a function added to leanrt (`runtime/leanrt/src/lib.rs`) | 474 | 474 |
  | that function removed again | 474 | 474 |
  | the same build again | 0 | 0 |
  | a comment in one prelude texture (`l2r_argc`) | 1 | 1 |
  | the comment removed | 0 | 0 |

  Removing the function gave misses because the rebuilt `libleanrt.rlib`
  was not the original file: rustc records its working directory in the
  rlib's metadata (once per source file), and `l2r.py` ran rustc in the
  caller's directory, another one than for the original build. The key
  follows the bytes, not the build's history. `l2r.py` now runs rustc for
  leanrt and lean-runtime in the crate's directory (`build_locked`):
  RtBorrowReleaseOrder built from one directory, then its leanrt build
  directory deleted and the test built from another directory, gives
  byte-identical `libleanrt.rlib`, `liblean_runtime.rlib` and
  `rustc-native` (cmp), and the second build compiles no texture (0 rustc
  runs under strace, 0 new entries). The same leanrt command run by hand
  in two directories gives rlibs that differ. The source paths rustc
  records (and panic messages would show) are absolute and the same both
  ways (23 files under `runtime/leanrt/src/`); no runtime test's expected
  output names a Rust source file, and RtAllocOverflow, RtAbortPanic,
  RtPanicOrder and RtErrorNoFileName (internal panics, aborts, an
  expectation file) pass.
- Damaged entries (truncated, empty, one flipped bit, unreadable mode
  000): each a miss, rebuilt; the output is still right. Four rrc
  processes filling one empty directory at once: all succeed, the seven
  entries are complete, no temporary file is left.

**Review.** Round FCR (local review notes): no defect in normal
single-build use; findings, all fixed in the amended 35-a or in lean2rr:

- FCR-01 (medium): the toolchain digest was computed once per process, so
  a library replaced while rrc compiled textures (in lean2rr: another
  driver rebuilding leanrt) gave entries compiled against the new library
  but filed under the old one's key, wrong once the old bytes came back.
  Fixed by the stamps (above).
- FCR-02 (low): a package directory with an `-L` kind (`crate=DIR`) was
  taken for a missing directory and never hashed. The kind is stripped;
  a directory that cannot be listed turns caching off.
- FCR-03 (low): a `%` in `REUSSIR_FFI_CACHE_DIR` meant nothing was stored
  (`createUniqueFile` substitutes it in the directory too). The temporary
  name is now unique in its file-name part only.
- FCR-04: caching that turns itself off now says so once on stderr.
- FCR-05: a hit must also start with a bitcode magic.
- FCR-06, FCR-07 (documentation): the directory must be trusted; macros
  of upstream crates and procedural macros that read files or the
  environment are not covered either.
- FCR-08 to FCR-10 (lean2rr's documents and repro script): no local paths
  in committed files; `run.sh` turns the cache off for every repro but
  35's; wording of three claims.

A second look at the fixes found them sound and two more small issues,
fixed in the amended 35-a (`968c4b7d`):

- FCR2-01 (low): a package directory's stamp changes with any entry
  added or removed, so with rrc running in a package directory (its
  temporary files go there) every lookup recomputed the digest and every
  store was skipped, silently; a cache directory made inside a package
  directory cost one recompute. A changed directory stamp now counts only
  if the list of libraries changed.
- FCR2-02 (info, fixed): a rewrite in place with the same size and the
  modification time put back went unseen. The stamps now include the
  status-change time on POSIX systems; the remaining gap (systems without
  it) is listed above.

**Effect on lean2rr.** Build time only: rrc takes the same bitcode from
the cache instead of from rustc, and the executables are byte-identical.
A small program's rrc time goes from about 16 s to about 3 s once the
cache is full; the first build after a change of leanrt, lean-runtime,
Reussir's runtime or the toolchain pays the full cost once.

## Upstream note

`compileRustSourceToBitcode` runs rustc once per polyffi texture, serially,
on every build; with a large runtime crate on the `-L` path each run costs
about 30 ms, mostly process start-up, and a program with hundreds of
textures spends most of its build there. An opt-in content-addressed cache
(`REUSSIR_FFI_CACHE_DIR`): key = BLAKE3 of the texture, the rustc options,
rustc's path, content and `-vV`, the host CPU and the content of the
libraries in the `-L` directories (the files it reads stamped and checked
again before each store, so that a library replaced during a build does
not leave entries under the old key); entries written with a temporary
file and an atomic rename and checked against a stored digest and the
bitcode magic. A small lean2rr program: 16 s to 3 s.
