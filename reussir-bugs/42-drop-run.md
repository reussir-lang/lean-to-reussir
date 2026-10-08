# 42. A host frees one cell through the pending stack with two calls and a pop

**Kind:** cost (run time). Not a bug: the runtime's pending stack releases
the cell in the right order, and the program's results are correct. Its
patch, 42-a, was an optimization: one entry point that does the same work
with less bookkeeping. It is parked.

## Summary

**Kind:** cost (run time). **Status:** not patched: the gain is too small
for a local Reussir patch (owner, 2026-10-07). The patch 42-a is parked
outside the series ([parked option](#parked-option-42-a)); no build
applies it, and lean2rr does not need it.

The pending stack of issue 13 (patches 13-b and 13-c,
`crates/reussir-rt/src/drop.rs`) lets a host push a cell
(`__reussir_drop_defer`) and empty the stack (`__reussir_drop_drain`).
lean2rr's runtime frees the last reference to a record, and to a box's
program payload, as one cell of that stack (switch step 11). Outside a
drain this costs three calls: the deferral pushes the cell, the drain sees
one cell pending and calls `drain_one`, which pops the cell and releases
it inside a new drain. That is 17 + 18 + 26 instructions of bookkeeping
per freed cell (measured on unionfind), and about 5% of monadic-interp's
instructions at its small size.

## Symptom and repro

No repro in [`repros/`](repros/): the cost shows only through a host that
frees single cells through the stack. The instruction counts below show
it (cachegrind, lean2rr programs).

## Cause

The runtime has no entry point that releases a given cell at once inside
a drain. A host cannot do that itself: it cannot set the private
`draining` flag, and without it the cell's release would run outside a
drain. Then the record's own glue releases the record's members in line,
in field order (natively: the last field first), and the hook at the end
of the drain (issue 40) would not run.

## lean2rr

leanrt's `drop::free_deferred` (the last reference to a record that a
set, a pop or a reference's set gives up: `drop::free_unique`) and
`any::release_last` (the last reference to a box's program payload) call
`__reussir_drop_defer` (`__reussir_drop_defer_wide` for a payload whose
cell has a wide header: `drop::free_deferred_wide`) and then
`__reussir_drop_drain`. A leaf payload is released directly, never
deferred.

## Parked option: 42-a

Patch file
[`patches/parked/42-a-drop-run.patch`](patches/parked/42-a-drop-run.patch),
outside the series: no build applies it. It applies after the whole
series.

- **What it does.** It adds one entry point, `__reussir_drop_run(cell,
  release)`: inside a drain it defers the cell as `__reussir_drop_defer`
  does; outside one it releases the cell at once inside a drain of its
  own, then drains what the release pushed. That is
  `__reussir_drop_defer` and `__reussir_drop_drain` in one call, without
  the push and the pop. The order of releases is the same. leanrt would
  call it in `drop::free_deferred`, in place of the two calls.
- **Measured.** Cachegrind instruction counts at the small sizes, with
  leanrt calling `__reussir_drop_run` in `drop::free_deferred` and
  `any::release_last`: monadic-interp -4.99%, unionfind -2.52%;
  binarytrees, deriv and rbtree unchanged. Per boxed record that unionfind
  frees, 75 instructions became 39. The [details](#details-of-the-parked-patch)
  follow.
- **Why it is parked.** The gain is too small for a local Reussir patch
  (owner, 2026-10-07): a few percent on two programs.

### Details of the parked patch

The patch is commit `2ca1a7d3` on branch `l2r-droprun` of a scratch
Reussir worktree, made on `l2r-inline` `136d9a9f` (the series up to 13-d,
then 36-a, 03-a, 36-b and 03-b). It changes only `crates/reussir-rt/src/drop.rs` and its
tests, so it also applies right after 13-d and on d79f8b70 (checked with
`git apply`). It needs 13-c (the stack's current form; 13-c needs 13-b)
and 40-a (the hook).

`__reussir_drop_run(cell, release)` (C ABI, `#[no_mangle]`):

- Inside a drain, it defers the cell exactly as `__reussir_drop_defer`
  does (not `_wide`: nothing is written into the cell). The running drain
  releases it.
- Otherwise, it sets `draining`, calls `release(cell)`, and ends as
  `drain_one` ends once it has popped its cell: if nothing is pending, it
  clears `draining` and calls the hook of issue 40 (`drained`); else it
  runs the general loop (`drain_slow`), which empties the stack and then
  calls the hook. Unlike `drain_one` it does not set the run count `n` to
  0: it popped nothing, and a run pushed before it (outside a drain) must
  stay.

**Why the order is the same.** The stack is last in, first out. A cell
pushed on top is popped first, before anything pushed earlier, and what
its release pushes goes on top again. So releasing the cell at once, with
the pending work left where it is, gives the same releases and steps in
the same order, also when work is pending (cells or steps pushed outside a
drain, for example by a record's glue before it frees a container). The
`depth()` and `active()` seen at each event are the same too: a pushed
cell is popped before its release runs. Only the stack's own bookkeeping
differs: no entry is made for the cell, so a run on top stays in place
instead of going to the vector and back.

**Unwinding and the hook.** The function is `extern "C"`, as are the other
entry points: it cannot unwind; `release` cannot either, and a panic in a
step or in the hook aborts, as in any drain. The hook runs once per call
outside a drain, after the drain is over (`active()` false, nothing
pending), and not for a call inside a drain.

**Verification.**

- `cargo test -p reussir-rt` (51 tests) passes. New tests in
  `drop/tests.rs`: an action `Run`, made either through
  `__reussir_drop_run` or through `__reussir_drop_defer` and
  `__reussir_drop_drain`. `random_runs_match_defer_and_drain` runs 400
  random forests both ways, with their roots released by a run or in
  line, so that runs happen inside a drain, outside one with nothing
  pending and outside one with work pending (each kind is checked to
  occur). It asserts the same events with the same `depth()` and
  `active()`, the same calls of the drain-end hook (each after its drain:
  not active, nothing pending), and the model's order (one stack entry per
  pending cell).
  `run_outside_a_drain`, `run_with_pending_work` and `run_inside_a_drain`
  give hand-made forests and their expected orders.
  `drained_runs_once_per_run` checks that the hook runs once per run
  outside a drain: with nothing pushed, with a cell pushed, with a cell or
  a step pending before, with a release that pushes only a step, and with
  a run inside the drain. A run that tested only the run count (and not
  the vector) fails both tests.
- The existing scenarios are unchanged: the digest of the 400 scenarios
  (`drop::tests::digest`) is `5906a65ce6ae636a`, before and after.
- The drop tests pass in release mode, and under Miri with strict
  provenance, with stacked borrows and with tree borrows.
- lean2rr against the patched build: [Result](#result).

#### Result

Cachegrind instruction counts (`--cache-sim=no`) of the classic programs
at their small sizes. Each program is built twice against one Reussir build
(`l2r-droprun` at c1f8e3c5, the patch's first version; the reviewed
version 2ca1a7d3 changes only comments and tests): from lean2rr's branch
`deptypes-rtperf`
(6dfa33a, leanrt calls `__reussir_drop_defer` and `__reussir_drop_drain`)
and from the same tree with leanrt calling `__reussir_drop_run`. Both are
built with SVE and dotprod off, for valgrind 3.22. The counts are the
minimum of two runs (mimalloc's free path varies from run to run). The
generated `.rr` files are identical, and every output equals native's.

| Program (size) | Before | After | Change |
|---|---|---|---|
| monadic-interp (1000) | 1,062,161,119 | 1,009,210,812 | -4.99% |
| unionfind (70000) | 349,649,215 | 340,849,011 | -2.52% |
| binarytrees (14) | 285,673,026 | 285,673,441 | +0.00% |
| deriv (8) | 127,924,483 | 127,924,399 | -0.00% |
| rbtree (100000) | 140,472,886 | 140,468,188 | -0.00% |

Unionfind frees 245,000 boxed records through `leanrt::any::release_last`,
outside a free. Per freed record, before: `release_last` 14,
`__reussir_drop_defer` 17, `__reussir_drop_drain` 18, `drain_one` 26 (75
instructions); after: `release_last` 10, `__reussir_drop_run` 29 (39). The
record's own release and its `mi_free` are not counted; they do not
change. In monadic-interp these functions fell from 121.8 M to 68.8 M
instructions (`release_last` 29.5 M to 21.0 M; the three Reussir functions,
92.3 M, to `__reussir_drop_run`, 47.8 M); `drain_slow` stays at 49.9 M.
Deriv, rbtree and binarytrees free their records through Reussir's own
drop glue, which the patch does not change.

lean2rr's tests with this build: leanrt's unit tests (63), the free-order
runtime tests `RtArraySetFreeNested`, `RtArraySetFreeOrder`,
`RtArrayPopFreeOrder`, `RtArrayRecordFreeOrder`, `RtDropOrder`,
`RtDropOrderRec`, `RtPromiseNestedFreeOrder`,
`RtPromiseResolvedFreeOrder`, `RtRefSetOrder`, `RtDropSharedOrder`,
`RtDropDeep`, `RtDropGlue` and `RtDropMediated`, the box probe
(`tests/runtime/any-probe.sh`: 19 scenarios under both nullary encodings,
release orders as native's), and the 18 classic programs at their small
sizes (outputs and exit codes equal native's) pass.

**Review.** An independent review (local review notes `review-rtperf`,
2026-10-06) found the patch correct: equivalent to a deferral and a drain
in every state of the stack. Its three findings are fixed in 2ca1a7d3:
R42-01 (the module comment and the subject now say that inside a drain
the function only defers), R42-02 (a test gap: the hook checks did not
cover a stack with a step but no run, so a function that tested only the
run count passed them; `drained_runs_once_per_run` now has a step pending
before a run and a release that pushes only a step, and the random
forests compare the hook calls of both ways too, which leaves the digest
unchanged) and R42-03 (this file and the README named 13-b instead of
13-c as the stack it needs).

## Upstream note

Any host that frees objects of its own through the stack, one at a time,
can use the entry point. A general form would also take a wide header
(`__reussir_drop_run_wide`), for a host that knows its cells' layout.
