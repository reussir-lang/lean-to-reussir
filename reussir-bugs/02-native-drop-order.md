# 2. Drop glue does not free in native Lean's order or share its stack with a host

**Kind:** missing feature. Not a bug: Reussir does not promise an order of
releases inside one free, nor a stack of pending work that a host runtime
can share. lean2rr's runtime (leanrt) needs both. Patches 02-a to 02-e add
them.

## Summary

**Kind:** missing feature, partly fixed upstream. **Status:** patched
(02-a to 02-e). The part that upstream fixed (frees of bounded stack
depth) is described under [What upstream fixed](#what-upstream-fixed); the
rest of this entry is the part that remains.

This entry was entry 13 before 2026-10-19 ("drop glue recurses once per
cell of a long list"). It also covers the old entries 27 (a chain linked
through `Nullable`; patch 27-a is now 02-d) and 47 (a pointer provenance
bug in 13-c's own code, fixed inside 13-c, now 02-c). Their full texts are
in git history.

**What lean2rr needs.**

1. *Native release order.* Native Lean frees with one to-do stack per
   thread (`lean_del_core`): it decrements a cell's fields in order,
   pushes each field whose count reached zero, and pops the last pushed
   first. So a record's last field is released first, and a list's heads
   are released from the tail. A program sees the order when it frees
   resources at once: handles are closed (and flushed) and promises are
   resolved in that order. lean2rr's runtime tests check it
   (`RtDropOrderRec`, `RtNestedArrayFreeOrder`, `RtArrayRecordFreeOrder`,
   `RtRefSetOrder` and others).
2. *One stack for Reussir's glue and leanrt's containers.* leanrt frees
   arrays, references, thunk and task cells, handles and promises. When
   these are nested in records and records in them, one free must still
   use one stack, or the order breaks and deep values overflow the native
   stack. leanrt uses the stack through `reussir_rt::drop`: `active`,
   `depth`, `defer_step`, `run_step`, `__reussir_drop_defer`,
   `__reussir_drop_defer_wide` and `__reussir_drop_drain`. leanrt does not
   build without it.

**Upstream 7954a367.** Upstream frees deep values in bounded stack (below)
but releases a record's members first field first, and keeps the state of
each free local to that free. It has no API through which a host can push
work into a running free. So items 1 and 2 are not fixed upstream.

## What upstream fixed

Upstream's pull requests #675 to #682 (2026-10-12/13) give drop glue a
bounded stack depth:

- `RecordType::classifyRecordDrop` (#676, `27ed1367`) sorts each named
  record into *Direct* (no cycle), *TailLoop* (one recursive member, the
  last managed member) or *Worklist* (other cycles; #682, `1b7fbea8`, also
  puts here a cycle with a managed member after the recursive one).
- A TailLoop drop is a `musttail` loop (#677, `f5818312`): it drops the
  other members, frees the cell, then tail-calls itself on the last member.
  Links through `Nullable` are handled too (old entry 27).
- A Worklist drop is a retcon coroutine (#678 `58a6ce24`, #679
  `20a6dd3d`): a recursive member's drop suspends and yields a child task;
  a local executor (`crates/reussir-rt/src/dtor_executor.rs`) runs the
  child and then resumes the parent. A root that does not suspend never
  makes an executor.
- Order: source order, each member's whole subtree before the next member;
  the cell is freed after its children. #682's test says it covers the
  hazard of old patch 13-d "without importing its pending stack's
  different, last-pushed-first member policy".

Checked on 2026-10-19 with upstream alone (7954a367 plus 10-a, 05-a and
07-a, no 02-x): the plain repros of old entry 13 (a list, a snoc list and a
left spine of 1,000,000 cells on an 8 MB stack) and of old entry 27
(1,000,000 links through `Nullable`) print the right values. The Lean
repro (40,000,000 cells through lean2rr) needs leanrt, which does not
build there.

## Patch

The five patches are one mechanism. On upstream 7954a367 (the series in
[`patches/series`](patches/series)):

- **02-a** (was 13-a): inside drop glue, a release calls a per-type
  function, `drop_and_free_in_drain`, which frees the cell first and
  releases the member that continues the chain last (a tail call, so a
  loop). On 7954a367 it also turns off upstream's tail-recursive and retcon
  drop lowering in rrc's pipeline (`crates/reussir-backend/src/pipeline.rs`)
  and in the C++ bridge (`lib/Bridge/Bridge.cppm`), as upstream's TPDE mode
  does: this glue replaces both.
- **02-b** (was 13-b): a stack of pending releases per thread in Reussir's
  runtime (`crates/reussir-rt/src/drop.rs`). Inside drop glue, a record
  member whose count is 1 is pushed (`reussir.rc.defer_release`, lowered to
  `__reussir_drop_defer` or `_wide`) instead of freed by a call; the
  outermost non-atomic dtor drains the stack (`__reussir_drop_drain`), last
  pushed first. Hosts share the stack (`active`, `depth`, `defer_step`,
  `run_step`). On 7954a367 the declaration of `__reussir_drop_drain` is
  registered in the pass's shared symbol table when it is made (upstream
  #671 shares one table per pass; without the registration the second dtor
  declared the function again: "redefinition of symbol named
  `__reussir_drop_drain`"). That line was part of old 11-b.
- **02-c** (was 13-c): the same stack, cheaper. Consecutive deferred cells
  form one run linked through the cells' headers (no memory per pending
  cell; `_wide` deferrals only). It has the fix of old entry 47: `unlink`
  makes the earlier cell's pointer from its address with
  `with_exposed_provenance_mut` (the link exposed that provenance), not
  from the later cell's pointer plus an offset, so Miri reports no
  undefined behaviour (`repros/bug02-unlink-provenance.rs`).
- **02-d** (was 27-a): a `Nullable` member of a shared record is deferred
  like a plain one, so a chain through `Nullable` is a loop too.
- **02-e** (was 13-d): a cell's last record member is kept for last (the
  tail call) only when no managed member after it can push work; otherwise
  every record member is pushed in field order. Without it, a later
  container field's work came after the record member's contents (review
  RS11-01, test `RtNestedArrayFreeOrder`).

Reviews (on the old base): 13-a passed (extended after round 2); 13-b
passed (round 4, revised twice); 13-c passed (round 5); the fix of entry 47
checked with Miri (same machine code), not reviewed yet; 27-a passed
(rv7/p22 round 2, RV7P-05; rv8/reussir, RV8R-01 fixed); 13-d passed
(review-0069: no defect). The rebase onto 7954a367 (2026-10-19) had five
mechanical conflicts (the hooks in `rewriteDropRc` and the `Nullable` arm,
`createDtorIfNotExists`, the module lists of `lib.rs` and `symbols.rs`, the
converted-op list); it is not reviewed yet.

Tested on 7954a367 with the series (2026-10-19): the repros of this entry
(below) and 13 targeted lean2rr runtime tests pass, among them
`RtDropOrderRec`, `RtNestedArrayFreeOrder`, `RtArrayFreeDirectOrder`,
`RtPromiseFreeGlue`, `RtArrayDeepSharedFree` and `RtRefSetOrder`.

## lean2rr

- leanrt's `drop.rs`, `any.rs`, `array.rs`, `fs.rs` and `task.rs` use
  `reussir_rt::drop`; lean2rr's lowering mirrors 02-c's wide-header rule
  (`boxWideBit`, `boxIsWide`, `rrAlign8`, `boxWideMaxCtors` in
  `LowerBase.lean`); `scripts/l2r.py` requires 02-a's switch (its comment
  in `pipeline.rs`, `options.tailRecursiveDrops = false` in `Bridge.cppm`,
  and no `OptLevel::Tpde` argument left in the passes), 02-e and 09-a.
- A planned port of leanrt to upstream's drop design would drop 02-a to
  02-e and patch 09-a. Upstream's executor offers no host deferral, no
  "is a free running" test and no end-of-free hook; leanrt would keep its
  own stack for its own objects. Native order would then hold inside every
  free that starts at a leanrt object, but not among the members of a
  record that user code drops by itself (as today), unless Reussir also
  tells the host where the outermost drop glue starts and ends (a small
  patch, not written).

## Repros

- [`repros/bug02-long-list-drop.rr`](repros/bug02-long-list-drop.rr): a
  list, a snoc list and a left spine of 1,000,000 cells, freed on an 8 MB
  stack (prints 1000000 three times).
- [`repros/bug02-long-list-drop.lean`](repros/bug02-long-list-drop.lean):
  `List.replicate` and a snoc list of 40,000,000 cells through lean2rr.
- [`repros/bug02-nullable-chain-drop.rr`](repros/bug02-nullable-chain-drop.rr):
  1,000,000 links through `Nullable` on an 8 MB stack (prints 1).
- [`repros/bug02-unlink-provenance.rs`](repros/bug02-unlink-provenance.rs):
  a Miri test of the stack's `link` and `unlink` (its header gives the
  commands; `run.sh` does not run it).

The order itself is tested by lean2rr's runtime tests (above), not by a
repro here.

## Upstream note

Not offered upstream: upstream chose another design (above). A request
would be a host task protocol (a host routine for an `ffi_object` member,
exported routine descriptors) and a last-pushed-first member order, or
the start and end of the outermost drop glue as host hooks.
