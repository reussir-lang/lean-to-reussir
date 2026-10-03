# Patch 0040: a hook at the end of a drain (`__reussir_drop_drained`)

Patch file: `../0040-l2r-local-drop-call-the-host-s-function-when-a-drain.patch`
(made as commit `3aad05ae` on 91da4f80 in a scratch checkout; it applies to
`./reussir`'s `l2r-local` too, whose `crates/reussir-rt/src/drop.rs` is the
same). Not a Reussir bug: a hook that lean2rr's runtime needs. Review:
pending. Applied to `./reussir`: not yet.

## 1. Why

Natively, dropping the last reference to an unresolved promise resolves it
with `none` and runs its `sync` dependents at once, on the dropping thread,
also in the middle of freeing a container that holds the promise. lean2rr's
runtime runs every context of its scheduler on one thread, and the pending
stack of `reussir_rt::drop` (patches 0014, 0015) is the thread's: a
dependent may block (a lock, a sleep), and a context suspended inside a
drain would let the other contexts push their frees onto that drain. So a
promise resolved inside a drain has its dependents walked once the drain is
over (`leanrt::task::resolve`, `run_later_walks`).

The runtime sees the end of a drain that it starts itself (`leanrt::drop::run`,
for arrays, reference cells and task cells, and for the old value of a
reference's `set`, `leanrt::drop::release`), but not of one that the record
glue starts (`drop_in_place`'s `__reussir_drop_drain`, when the program's
own code releases a structure, a list, an `Option`). Without this patch
those dependents run only at the context's next output, block, Std.Sync
wait or question about a task: code in between sees the old state, output
they print escapes `IO.FS.withIsolatedStreams`, and a condition-variable
loop that reads its condition before waiting can wait forever (plan §10).

## 2. The change

`crates/reussir-rt/src/drop.rs` exports
`pub static __reussir_drop_drained: AtomicPtr<()>` (`#[no_mangle]`, null
by default), the address of an `unsafe extern "C" fn()`. The general drain
loop (`State::drain`) and the one-cell path (`drain_one`) call it after
setting `draining` back to false, when nothing is pending. A drain with
nothing pending, or started inside a drain, returns before and calls
nothing. The cost is one relaxed load per drain that released something.
The function may release values (a new drain, which calls it again) and
switch coroutines.

lean2rr's runtime declares the symbol `#[linkage = "extern_weak"]` and
stores `leanrt::task::drained` there whenever a promise is resolved inside
a drain. Against a Reussir without the patch the weak symbol is null
and nothing is stored: the runtime still builds and works as before.

## 3. Checks

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
