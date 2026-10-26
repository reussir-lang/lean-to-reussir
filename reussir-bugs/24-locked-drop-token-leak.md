# 24. A locked cell's payload leaks when its drop is expanded in the critical section

**Kind:** bug (a leak: memory that the program no longer reaches is
never freed). With the acquire/drop expansion's default options, both
tail-recursive and retcon drops off (TPDE mode's options), the drop of a
cell guarded by a lock (`mutex`, `rwlock`, `flatlock`) releases the
payload inside the critical section, and the payload's box is never
freed. Fixed inside patch 23-e, which uses the locked-drop function
under every option.

## Summary

**Kind:** bug. **Status:** fixed by 23-e
([issue 23](23-worklist-drops.md)), applied in `./reussir`'s series since
2026-10-25 (branch `l2r-base11`, commit `0fef47d1`). lean2rr does not
reach the bug: rrc's command line has no TPDE level (`-O` is `none`,
`default`, `aggressive` or `size`), and lean2rr does not use the JIT.

**Upstream (2026-10-25):** Open at 00906e38. Not reported. Found by the
review of 23-a to 23-j, which reached the path end to end with a local
switch of rrc's pipeline to TPDE's drop options: ASan reports
`24 byte(s) leaked in 1 allocation(s)` for a program that drops a
`Mutex<Arc<Tree>>` (an `Arc` box of a one-word record, allocated in
`__reussir_allocate_small`).

## Context

- **Lock-guarded cells.** A cell with a `mutex`, `rwlock` or `flatlock`
  holds its payload behind a lock header. The drop of such a cell, when
  its box count is zero, takes the lock (a critical section of MLIR's
  `sync` dialect: `sync.mutex.critical_section`,
  `sync.combining_lock.critical_section`, `sync.rwlock.write_critical_section`)
  and releases the payload inside it
  (`DropExpansionPattern::rewriteDropCell`,
  `lib/Conversion/AcquireDropExpansion/AcquireDropExpansion.cpp`).
- **Decrement tokens.** The expansion turns the release of a box into a
  decrement that yields a nullable token: the box's memory when the
  count reached zero. The token reuse pass
  (`lib/Transformation/TokenReuse/TokenReuse.cpp`, run after the
  expansion) gives each token to an allocation that can reuse it, or
  frees it (`reussir.token.free`).
- **Options.** rrc's pipeline passes tail-recursive and retcon drops on,
  except at `OptLevel::Tpde` (`crates/reussir-backend/src/pipeline.rs`),
  which rrepl selects by default when Reussir is built with TPDE, and
  which the JIT bridge has too. The pass itself has both off by
  default (`reussir-opt`).

## Symptom and repro

Repro [`repros/bug24-locked-drop-token.mlir`](repros/bug24-locked-drop-token.mlir):
one function that drops a `mutex` cell of an atomic `rc` box.

**Command.**
`reussir-opt bug24-locked-drop-token.mlir --reussir-acquire-drop-expansion='outline-record=true expand-decrement=true' --reussir-token-reuse`
(`run.sh` needs `reussir-opt` in the checkout's build: a build with the
tests on, or its target `reussir-opt`).

**Expected:** a `reussir.token.free` of the payload's token, as for the
same box dropped outside a cell.

**Actual on upstream** (00906e38, 2026-10-25): no `reussir.token.free`.
The decrement and its token are inside the critical section's region;
nothing frees the token. With 23-e: one `reussir.token.free`, in
`__reussir_locked_drop`, which the critical section calls. `run.sh`
prints `REPRODUCES` on upstream and `FIXED` on `l2r-base9`.

## Cause

`rewriteDropCell` releases the payload in the critical section's body
with a plain `reussir.ref.drop` unless retcon drops are on; with them on
(upstream #679, `20a6dd3d`) it calls a separate private function,
`__reussir_locked_drop`, whose body is the drop. The decrement expanded
inside the critical section's region gets a token that token reuse does
not free there (the plain function's token is freed, the one in the
region is not), so the payload's box leaks. Only the retcon path had
the separate function.

## Patch

Inside 23-e
([`patches/23-e-worklist-nullable-locked.patch`](patches/23-e-worklist-nullable-locked.patch),
commit `0fef47d1`): the critical section calls the locked-drop function
under every option, not only under retcon drops. Inside worklist glue
it calls a variant marked as glue, `__reussir_locked_drop.worklist`, so
that the payload's Worklist box is deferred like the glue's other boxes
(entry 23's reason for touching this code); elsewhere the ordinary one.
The payload's release, its decrement and the inner box's free now run in
that function, under the lock.

**Tests.** `conversion/locked_cell_drop.mlir` runs the expansion with
TPDE's options and checks that the locked-drop function frees its token;
`conversion/mutex_cell_drop.mlir`, `rwlock_cell_drop.mlir` and
`flatlock_cell_drop.mlir` check the critical section's call and, in the
locked-drop function, the payload's decrement and the inner box's free;
`conversion/retcon_drop.mlir`'s run without retcon drops no longer
excludes `__reussir_locked_drop`. The review's end-to-end program
(through the local TPDE switch) is ASan clean with 23-e, and so are its
chains of `Arc` boxes whose levels alternate the three lock kinds (2000
levels) and a cell's `set` of a live mutex that drops a locked chain
under its lock, in TPDE mode, retcon mode and worklist mode, at `-O none`
and `-O aggressive`.

## Upstream note

Not reported. A report would give the repro above: with retcon drops
off, `rewriteDropCell` expands the payload's drop inside the critical
section, where its token is never freed; calling `__reussir_locked_drop`
under every option, as the retcon path does, fixes it.
