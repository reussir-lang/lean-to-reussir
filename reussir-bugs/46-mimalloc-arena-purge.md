# 46. Reussir's mimalloc (v2.2.4) runs no delayed arena purge

## Summary

**Kind:** issue (dependency). The error is in mimalloc, a library that
Reussir's runtime pins, not in Reussir's own code. In mimalloc it is a bug
(a comparison the wrong way round); for a Reussir program it is a memory
cost: the results are correct. **Status:** worked around in lean2rr's
runtime (leanrt); no Reussir patch. The change on Reussir's side, a newer
`libmimalloc-sys`, is parked ([parked option](#parked-option-b-a-newer-libmimalloc-sys)).

`crates/reussir-rt/Cargo.toml` pins `libmimalloc-sys = { version =
"0.1.44", optional = true, features = ["extended"] }` (`Cargo.lock`:
0.1.44). That crate bundles mimalloc v2.2.4, which reussir-rt builds by
default (feature `mimalloc-v2`; feature `mimalloc-v3` takes the crate's
v3.1.5, which does not have the error).

mimalloc gives the memory of a free range of an arena back to the OS (a
*purge*: decommit or reset) some time after the free: `purge_delay` x
`arena_purge_mult` ms, 10 x 10 by default. A range of an arena is a whole
segment (32 MiB) or the segment of a huge block (more than 16 MiB). In
v2.2.4 these delayed purges do not run: freed huge blocks and segments
stay in the process until mimalloc uses them again.

## Symptom and repro

Peak memory of programs that free big blocks. lean-zip's benchmark (a
zlib round trip at level 9 over four files of the Silesia corpus) has a
peak of 422 MiB; with the arena purges made at once
(`MIMALLOC_ARENA_PURGE_MULT=0`) 330 MiB; native Lean 394 MiB. Of 16
benchmark programs, no other program's peak changed.

No repro in [`repros/`](repros/): the repro is lean2rr's runtime test
`RtArenaPurge` (`tests/runtime/RtArenaPurge.lean`, bounds in
`RtArenaPurge.alloc`, checked by `tests/runtime/alloc-check.sh`): four
rounds of a `ByteArray` made with room for 2 * 10^7 bytes (a huge block),
grown by pushes to 5 * 10^7 bytes and dropped. The runtime doubles a full
block, so each growth frees a huge block. Peak 77,000 KB with mimalloc's
default, 56,400 KB with the arena purges at once.

## Cause

mimalloc v2.2.4, `src/arena.c`, `mi_arenas_try_purge`, line 624:

```c
  mi_msecs_t arenas_expire = mi_atomic_loadi64_acquire(&mi_arenas_purge_expire);
  if (!force && (arenas_expire == 0 || arenas_expire < now)) return;
```

`mi_arenas_purge_expire` is the time at which the first scheduled arena
purge is due. The test returns when that time has passed, which is when
the function should purge. It goes on only while the time is still to
come; then each arena's own test (`expire > now`, line 565) declines, every
arena is visited, and the function sets the global time to 0. A later free
finds its arena's time already set and does not set the global time
again, so from then on the function returns at its first test. The
scheduled purges run only by chance (in the millisecond in which they fall
due) or when forced (`mi_collect(true)`).

**Versions.** In the `src/arena.c` of each mimalloc tag: v2.1.7 and older
have no global time (each arena tests its own time, the right way round);
v2.1.8 added the global time with this test; v2.1.9 and v2.2.2 to v2.2.7
have it (`< now`); v2.3.0 fixed it (`> now`, mimalloc commit `acd6f6c`,
"fix inverted purge expire comparison", 2026-03-25; commit `4e50cec` also
keeps the global time when an arena's time has not come). v2.3.0 to
v2.3.2 have `> now`; v3 (v3.0.0 to v3.1.6) always had it. So the affected
versions are 218 to 227 by `mi_version()` (`MI_MALLOC_VERSION`); from
v2.3.0 the number also has two digits of patch (20300). `libmimalloc-sys`
0.1.49 bundles v2.3.2 (`src/arena.c` line 632: `arenas_expire > now`) and
v3.3.2.

## lean2rr

leanrt's `alloc::purge_arenas_at_once`, the first call of `rt::run_main2`
(before the module initializers), sets mimalloc's `arena_purge_mult` to 0
(`mi_option_set`, option 24 in the `include/mimalloc.h` of every affected
version) when `mi_version()` is 218 to 227 and the environment does not
set `MIMALLOC_ARENA_PURGE_MULT`. With the multiplier at 0 the arena
purges a range when it is freed; purges inside segments keep their 10 ms
delay. lean-zip's peak went from 422 to 330 MiB, its wall time up 0.9 %
(about 65 ms of system time); no other program's peak changed, and their
wall times stayed within noise. A Reussir with a mimalloc outside the
range turns the workaround off by itself. Remove it when Reussir's
mimalloc is v2.3.0 or later. Implementation notes:
[`docs/implementation/startup/entry.md`](../docs/implementation/startup/entry.md).

## Parked option (b): a newer libmimalloc-sys

Reussir's runtime could depend on `libmimalloc-sys` 0.1.49 or later
(mimalloc v2.3.2), which has the fixed test. Parked: lean2rr changes
Reussir only where it has no other way (owner, 2026-10-07), and the
runtime's option has the effect it needs. Measured for the choice (16
benchmark programs, peak by single runs, wall time median of 9):
`MIMALLOC_ARENA_PURGE_MULT=0` takes lean-zip from 422 to 330 MiB at
+0.9 % wall time, and changes no other program. A fixed v2.3.2 with its
default delay would purge 100 ms after a free; its peaks were not
measured.

## Upstream note

reussir-rt pins `libmimalloc-sys` 0.1.44 (mimalloc v2.2.4), whose
`mi_arenas_try_purge` (`src/arena.c:624`) tests the global purge time the
wrong way round (`arenas_expire < now`), so delayed arena purges do not
run and freed huge blocks and segments stay committed (a ZIP benchmark:
peak 422 MiB, 330 MiB with `MIMALLOC_ARENA_PURGE_MULT=0`). mimalloc fixed
it in v2.3.0; `libmimalloc-sys` 0.1.49 bundles v2.3.2. A bump of the
dependency fixes it.
