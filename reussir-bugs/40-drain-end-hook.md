# 40. Reussir's runtime does not tell the host when a drain ends

**Kind:** missing feature. Not a bug: Reussir does not promise a hook at
the end of a drain. lean2rr's runtime needs one; patch 40-a adds it.

## Summary

**Kind:** missing feature (lean2rr's runtime needs it). **Status:**
patched (40-a), applied in `./reussir` (`l2r-local` commit `e3e267af`).
lean2rr requires the patch since its switch step 6: `scripts/l2r.py` stops
with an error when the Reussir checkout lacks it
(`REQUIRED_REUSSIR_PATCHES`), and leanrt names the patch's symbol.

Until 2026-10-06 this patch had no entry: it was one of the two "local
additions" (file `local-additions.md`, now entries 40 and
[41](41-tagged-ffi-objects.md)).

## What is missing

Natively, dropping the last reference to an unresolved promise resolves it
with `none` and runs its `sync` dependents at once, on the dropping thread,
also in the middle of freeing a container that holds the promise. lean2rr's
runtime runs every context of its scheduler on one thread, and the pending
stack of `reussir_rt::drop` (patches 13-b, 13-c of
[issue 13](13-long-list-drop.md)) is the thread's: a dependent may block (a
lock, a sleep), and a context suspended inside a drain would let the other
contexts push their frees onto that drain. So a promise released
unresolved inside a drain is resolved, its cell's store and the walk of its
dependents together, once the drain is over (since lean2rr's switch step 6
through lean-runtime's deferred resolutions:
`leanrt::task::defer_promise_drop`, run by `leanrt::task::drained`; before,
`leanrt::task::resolve` and `run_later`).

The runtime sees the end of a drain that it starts itself
(`leanrt::drop::run`, for arrays, reference cells and task cells, and for
the old value of a reference's `set`, `leanrt::drop::release`), but not of
one that the record glue starts (`drop_in_place`'s `__reussir_drop_drain`,
when the program's own code releases a structure, a list, an `Option`).
Reussir has no way to tell the host that such a drain ended. Without this
patch those resolutions would run only at the context's next output,
block, Std.Sync wait or question about a task: code in between would see
the old state, output their dependents print would escape
`IO.FS.withIsolatedStreams`, and a condition-variable loop that reads its
condition before waiting could wait forever. lean2rr's runtime had that
fallback until switch step 6; since then lean2rr requires the patch.

**Repro.** None in [`repros/`](repros/): the hook shows only through a
host that stores a function in it. The patch's unit test and lean2rr's
runtime tests show it (see [Checks](#checks)).

## Patch

Patch file
[`patches/40-a-drain-end-hook.patch`](patches/40-a-drain-end-hook.patch)
(`l2r-local` commit `e3e267af`, applied in `./reussir`; made as commit
`3aad05ae` in a scratch checkout on 91da4f80).

`crates/reussir-rt/src/drop.rs` exports
`pub static __reussir_drop_drained: AtomicPtr<()>` (`#[no_mangle]`, null
by default), the address of an `unsafe extern "C" fn()`. The general drain
loop (`State::drain`) and the one-cell path (`drain_one`) call it after
setting `draining` back to false, when nothing is pending. A drain with
nothing pending, or started inside a drain, returns before and calls
nothing. The cost is one relaxed load per drain that released something.
The function may release values (a new drain, which calls it again) and
switch coroutines.

lean2rr's runtime names the symbol
(`reussir_rt::drop::__reussir_drop_drained`) and stores
`leanrt::task::drained` there whenever it puts a promise's resolution off
inside a drain. Until switch step 6 it declared the symbol
`#[linkage = "extern_weak"]` and also built against a Reussir without the
patch; since then it does not link without it.

### Checks

- `cargo test -p reussir-rt --lib drop::` passes: the new test
  `drained_runs_after_the_outermost_drain` (the function runs once per
  outermost drain, after it, through both paths, and not for a drain with
  nothing to do or one started inside a drain) and the existing order
  tests.
- lean2rr against the patched build (`L2R_REUSSIR`): `RtPromiseFreeSync`,
  `RtPromiseFreeGlue`, `RtSyncLostWake` and the task, promise, sync, IO and
  net runtime tests pass. (`RtPromiseFreeGlue` was an expected failure
  without the patch until reference sets released their old value through
  the runtime, round 8; its cases are all references now covered without
  it. A free that the program's own code starts at a record has no test:
  where Lean drops a local is not fixed.)

### Review

Round RV8 (local review notes, `rv8/reussir/FINDINGS.txt`): no defect.
The hook is called at every drain exit that released something, after
`draining` is false and with nothing pending, as the last statement, so it
may start new drains, re-enter or switch coroutines; not for nested drains
or drains with nothing to do. A panic inside a drain aborts (the steps are
reached only through `extern "C"` frames), so no drain exits by unwinding.
A relaxed `AtomicPtr` is enough (it publishes a code pointer). Weak linking
(lean2rr's link until switch step 6) works both ways: a binary built with
40-a defines the symbol and `RtPromiseFreeGlue` passes; one built against
a Reussir without it shows a weak undefined symbol and runs. The drop unit
tests pass, the new one also under Miri. Side note (not introduced by
40-a): drop glue is marked `mustprogress nounwind willreturn`, and with
the hook (and already before, through `leanrt::drop::run`) it can run Lean
continuations that might not return; no concrete miscompile was found
(README, [Other observations](README.md#other-observations)).

## Upstream note

The hook is general: a host whose frees can start work that must wait
until the free is over (finalizers, promise resolution) can use it.
