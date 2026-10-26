# 2. Drop glue does not free in native Lean's order

**Kind:** missing feature. Not a bug: Reussir does not promise an order of
releases inside one free. Native Lean frees last field first; upstream
Reussir frees first field first. Until 2026-10-25 the local patches 02-a
to 02-e gave lean2rr native Lean's order; since Phase 2 lean2rr uses
upstream's drop design without them (with entry 23's worklist for
recursive records that are neither Direct nor TailLoop, on a stack that
lean2rr's runtime shares), and the two remaining differences are
accepted.

## Summary

**Kind:** missing feature, partly fixed upstream. **Status:** not
patched since 2026-10-25 (Phase 2, base `l2r-base9-shared`): patches
02-a to 02-e left the series. lean2rr uses upstream's drops for Direct
and TailLoop records and entry 23's worklist drops for the other
recursive records ([issue 23](23-worklist-drops.md)), and lean2rr's
runtime (leanrt) keeps its pending releases on entry 23's stack (patches
23-k to 23-m). Two differences from native Lean remain, which the owner
accepted (2026-10-19): records that user code drops are freed in field
order, and a value shared by two fields of one freed cell can be
released at another position ([lean2rr](#lean2rr-since-phase-2)).

**Upstream (2026-10-25):** Open at 00906e38, by design: upstream frees
deep values at a bounded stack depth (the part of the old problem that
it fixed, [below](#what-upstream-fixed)), but first field first, with the
state of each free local to that free, and with no API through which a
host can push work into a running free or learn where it ends. The
changes to upstream's drops since 7954a367 change neither: #763
(`fe9f2379`) lets the executor of retcon drops keep its slot table and
arena for each thread between root drops; #790 and #801 add rcgmp
integer members to the drop expansion and the inc/dec cancellation; #800
reuses a dominating load after the expansion.

This entry was entry 13 before 2026-10-19 ("drop glue recurses once per
cell of a long list"). It also covers the old entries 27 (a chain linked
through `Nullable`; patch 27-a, later 02-d) and 47 (a pointer provenance
bug in 13-c's own code, fixed inside 13-c, later 02-c). Their full texts
are in git history.

## Native Lean's order

Native Lean frees with one to-do stack per thread (`lean_del_core`): it
decrements a cell's fields in order, pushes each field whose count
reached zero, and pops the last pushed first. So a record's last field
is released first, and a list's heads are released from the tail. A
program sees the order when it frees resources at once: handles are
closed (and flushed) and promises are resolved in that order. Where
Lean's code knows the constructor (`lean_dec_ref_known`, for example a
structure that it has just built), the fields go in field order, each
completely; elsewhere (`lean_dec`) last first.

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
  makes an executor. (lean2rr's builds replace these retcon drops with
  entry 23's worklist, which frees with no state per level:
  [issue 23](23-worklist-drops.md); upstream's expansion of their
  direct arms is [issue 19](19-retcon-direct-arms.md).)
- Order: source order, each member's whole subtree before the next member;
  the cell is freed after its children. #682's test says it covers the
  hazard of old patch 13-d "without importing its pending stack's
  different, last-pushed-first member policy".

Checked on 2026-10-19 with upstream alone (7954a367 plus 10-a, 05-a and
07-a, no 02-x): the plain repros of old entry 13 (a list, a snoc list and a
left spine of 1,000,000 cells on an 8 MB stack) and of old entry 27
(1,000,000 links through `Nullable`) print the right values.

## lean2rr since Phase 2

leanrt frees arrays, references, thunk and task cells, boxes, handles and
promises. Its stack of pending releases and its "releasing" flag
(`runtime/leanrt/src/pending.rs`) are Reussir's drop stack and its
draining flag (entry 23, with patches 23-k to 23-m: runs, steps, the end
work). Reussir frees records with upstream's glue (Direct and TailLoop
records) and with entry 23's worklist (the other recursive records): at
a cell's visit its other members are released at once, in field order,
and its dead children of the cycle are pushed onto that stack and come
out last first ([issue 23](23-worklist-drops.md#order-of-releases)). The
implementation notes describe leanrt's side
(`docs/implementation/ownership.md`, "Runtime objects free through
leanrt's pending stack in Lean's order"; plan §10, "Order of releases in
one free").

- **Inside a drain** (a free that starts at a runtime object: an array,
  a reference's `set`, a box, a thunk or task cell; or a Worklist
  record's drain), every runtime object that Reussir's glue reaches is
  pushed, and the pops, last pushed first, give native Lean's order
  through any records (tests `RtDropOrderRec`, `RtNestedArrayFreeOrder`,
  `RtArrayRecordFreeOrder`, `RtRefSetOrder` and others).
- **Accepted difference 1: a record that user code drops by itself.** No
  drain runs around it (for a Worklist record, each dead Worklist child is
  a drain of its own that ends before the next member), so each runtime
  object that Reussir's glue reaches there is a free of its own, done
  before the glue goes on to the next field. So the order is field order
  at every record level from the root, and native again below the first
  runtime object or drain. A `List
  IO.FS.Handle` `L0 … L7` dropped by itself closes `L0 L1 … L7`
  (natively `L7 … L0`, or `L0 L7 … L1` where Lean knows the
  constructor). Tests with expectation files: `RtDepDropOrderBoxed`,
  `RtDropUserListHandles`, `RtPromiseDropRecordPending` (a dependent of
  a promise in a record's first field runs before a later field's handle
  is closed).
- **Accepted difference 2: a value shared by two fields of one freed
  cell.** Reussir decrements a field's subtree while it descends; native
  Lean decrements all fields of a cell first. In `R{a : Y{x : W, h}, b :
  W}`, with `W` held by `Y.x` and `R.b`, native closes `Y.h` before
  `W.h`; lean2rr closes `W.h` first (test `RtDropSharedSubtree`, with
  expectation files). The patched bases gave the same order here.
- **Fixed: Worklist records inside a free that starts at a runtime
  object.** On `l2r-base9` (entry 23 without 23-k to 23-m) Reussir's
  drain and leanrt's stack were separate, and `RtDropOrderRec` (trees
  `Tr.node l h r` of handles in an array freed at once) closed native
  `T7 T3 T6 T1 T5 T2 T4` as `T6 T7 T3 T1 T4 T5 T2`; with the shared
  stack it gives native's order again (lean2rr's phase2-dev, commit
  `d502cd7d`).

Before Phase 2, with 02-a to 02-e, only the first two cells of a free
that user code starts came out in field order (the list: `L0 L1 L7 …
L2`); everything below was native.

**What would remove difference 1:** a drop that user code starts running
inside a drain of the shared stack (the root of a Worklist record, and
TailLoop and Direct records, which entry 23 leaves to upstream's glue).
Not written: a Reussir change is the last resort (owner).

## The patches until Phase 2 (02-a to 02-e)

From 2026-09-30 to 2026-10-25 lean2rr's builds applied five patches that
replaced upstream's drop lowering with a stack shared with leanrt. Their
last files are in git history (commit `419a74d4`,
`reussir-bugs/patches/02-a-*.patch` to `02-e-*.patch`); they left the
series with Phase 2, when leanrt got its own stack.

- **02-a** (was 13-a): a release inside drop glue called a per-type
  function that freed the cell first and released the member that
  continues a chain last (a loop); it also turned off upstream's
  tail-recursive and retcon drops.
- **02-b** (was 13-b): a stack of pending releases per thread in
  Reussir's runtime (`reussir_rt::drop`), drained last pushed first,
  which hosts shared (`active`, `depth`, `defer_step`, `run_step`).
- **02-c** (was 13-c): the same stack, cheaper (runs of deferred cells
  linked through their headers), with the fix of old entry 47.
- **02-d** (was 27-a): `Nullable` members deferred like plain ones.
- **02-e** (was 13-d): a cell's last record member kept for last only
  when no later member could push work.

Reviews (on the old base): 13-a, 13-b, 13-c, 27-a and 13-d passed their
rounds; this file's version in commit `419a74d4` lists the review notes.
Patch 09-a (entry 9, now retired: see the
[history](README.md#history-phase-2-worklist-drops-instead-of-the-local-drop-patches-2026-10-25))
added a hook at the end of 02-b's drain.

## Repros

The repros show the part that upstream fixed (a bounded stack depth),
which lean2rr's builds now get from upstream itself (the lists are
TailLoop records) and, for other recursive records, from entry 23. They
stay as checks of that part. The order is tested by lean2rr's runtime tests (above), not
by a repro here.

- [`repros/bug02-long-list-drop.rr`](repros/bug02-long-list-drop.rr): a
  list, a snoc list and a left spine of 1,000,000 cells, freed on an 8 MB
  stack (prints 1000000 three times).
- [`repros/bug02-long-list-drop.lean`](repros/bug02-long-list-drop.lean):
  `List.replicate` and a snoc list of 40,000,000 cells through lean2rr.
- [`repros/bug02-nullable-chain-drop.rr`](repros/bug02-nullable-chain-drop.rr):
  1,000,000 links through `Nullable` on an 8 MB stack (prints 1).

The Miri test of 02-c's stack (`bug02-unlink-provenance.rs`) left with
02-c (git history).

## Upstream note

Not offered upstream: upstream chose another design (above). A request
would be the start and end of the outermost drop glue as host hooks, so
that a host runtime can keep its own order inside a free that user code
starts.
