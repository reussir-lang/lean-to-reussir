# 2. Drop glue does not free in native Lean's order

**Kind:** missing feature. Not a bug: Reussir does not promise an order of
releases inside one free. Native Lean frees last field first; upstream
Reussir freed first field first until 2026-11-01, and since then has a
switch whose default, `backward`, frees last first inside a free
([on upstream 36a55a0f](#on-upstream-36a55a0f)). Until 2026-10-25 the local patches 02-a
to 02-e gave lean2rr native Lean's order; since Phase 2 lean2rr uses
upstream's drop design without them (until 2026-11-17 with the local
worklist drops of entry 23, deleted since, for recursive records that
are neither Direct nor TailLoop, on a stack that lean2rr's runtime
shares; since then with upstream's scoped worklists), and the two remaining differences are
accepted.

## On upstream 36a55a0f

Since 2026-11-17 lean2rr's base is upstream `36a55a0f`, which has no
patch for the order of releases. What changed for this entry:

- **Upstream has a switch.** `rrc --drop-order forward|backward`
  (#913; `crates/reussir-core/src/drop_order.rs`). `forward` is source
  order. `backward` is the default: inside a free, a cell's dead members
  are pushed and come out last first. Upstream's own test
  (`conversion/worklist_recursive_order.c`: `node(1, node(2), node(3))`)
  prints `1 2 3` under forward and `3 2 1` under backward; native Lean
  gives `3 2 1`. The policy is saved in a module attribute, and a
  flag that conflicts with it is an error.
- **Backward is our order.** It is the order that `l2r-base12` gave
  (the worklist of the deleted entry 23), so `scripts/l2r.py` passes
  `--drop-order backward` explicitly: a later change of upstream's
  default cannot move lean2rr's release order. `forward` must not be
  used.
- **Native Lean's exact rule is still not a mode.** Nothing upstream
  plans it. So this entry stays a missing feature.
- **leanrt's side.** leanrt keeps its pending releases on upstream's
  drop scopes (`runtime/leanrt/src/pending.rs`): the same design as on
  `l2r-base12`, with upstream's functions in the place of 23-k to 23-m.

**What the port's first gate showed (2026-11-18).** Backward is not
`l2r-base12`'s code, only its policy. The first full run of the runtime
suite on the new base (lean2rr with the translator of dev, the 5
patches of the first series): 739 of 747 tests identical to native, 2
expected failures, and 6 failures, all of them release order, with the
right results otherwise. Two rules of upstream's design differ from
`l2r-base12`'s, and they explain all six:

1. **A whole value is one free, last field first.** A record that is
   released through its FFI release (lean2rr's `l2r_release_after`)
   goes through a bridge that joins or opens a scope and defers the
   root. So the whole value is one free, last pushed first: native
   `lean_dec`. `l2r-base12` expanded the root at that place, in field
   order. Result: three documented differences are gone
   (`RtDropUserListHandles`, `RtPromiseDropRecordPending`, and three of
   the four lines of `RtDepDropOrderBoxed` are identical to native; their
   expectation files are removed). But where native Lean knows the
   constructor it uses `lean_dec_ref_known`: field order, each field
   completely. There `l2r-base12`'s field order at the root was native's
   and the new order was not (`RtDropOrderMix` `shared`,
   `RtPromiseDepDrainShapes` `s4`, `RtDepDropOrderBoxed` `list`).
2. **A drop run that starts inside a free finishes before it returns.**
   On `l2r-base12` it joined the running free. lean2rr reaches it: the
   release function of a box's payload (`l2r_any_rel_N`) is generated
   code that leanrt calls inside its free, and its drop of a recursive
   member is a `__reussir_drop_run`. So a tree in a structure's first
   field closed its handles before the structure's later fields
   (`RtDropOrderRec` `mixes`, `RtDropOrderMix` `structs`). Plain repro
   of the runtime's rule:
   [`repros/bug02-nested-run-order.rr`](repros/bug02-nested-run-order.rr).
   This is not a bug: upstream tests this rule
   (`conversion/worklist_observable_order.c`, "nested public drop").

`--drop-order forward` is no answer to either: it does not change rule
2, it gives rule 1's known-constructor cases the right order only by
coincidence, and it breaks the orders of trees and lists (run).

**Both are answered in lean2rr's emitter, with no Reussir patch**
(2026-11-18):

- *Known constructor.* Where lean2rr releases a value itself and native
  Lean knows the value's constructor there, the release is a generated
  function for the type that releases the fields one after the other in
  Lean's field order (`l2r_release_known_<type>`). Else the plain
  release: one free, as `lean_dec`. This holds after a call that borrows
  the value natively, and at the start of a branch, also for one value
  that dies alone there (`docs/implementation/ownership.md`, "A value
  whose constructor Lean knows is released field by field").
- *Payload joins.* The payload release of a box goes through the
  record's FFI release, whose bridge joins the running free, when a
  drop run could start in it and a value of the type can hold a
  resource (`payloadJoins`;
  `docs/implementation/representations/box-and-uniform.md`).

With both rules, the six tests and the two new ones
(`RtDropKnownCtorOrder`, `RtDropNestedRunOrder`) are identical to
native, and so are the 258 runtime tests that were run again: every
test whose translation changed, and the release-order families. The
port's final gate (2026-11-18, lean2rr `8d032fdb` on the final series)
confirms it: 748 of 750 runtime tests identical to native, 2 expected
failures, and the six tests and the two new ones among the passes.

The other predictions that were made before the gate, by reading:

- `RtDropSharedSubtree` (a value shared by two fields of one freed
  cell) was predicted to move to native's order. It did not: it prints
  what it printed on `l2r-base12`, and its expectation files stay.
- The reset and reuse paths (`RtResetFieldOrder`, `RtDropArmReuse`,
  `RtDropArmPushProj`) are unchanged, as predicted.
- The tagged box `LAny`: no failure of the gate comes from its hook
  running in line where an untagged object is deferred.

**Differences from native that are left on this base** (plan §10 has
the full text):

- A matched value that Reussir consumes in its `match`, with nothing
  released before it: Reussir takes a record without a cycle apart in
  place, in the order of the record's fields. `mk {x, y} h` from
  another function, matched by arms that read no field, closes `x y h`,
  natively `h y x`. `l2r-base12` gave the same.
- A value that Lean's reset/reuse resets: the fields that the code does
  not read go in field order, natively last first (`RtResetFieldOrder`).
- A value shared by two fields of one freed cell (`RtDropSharedSubtree`).

The sections below ("lean2rr since Phase 2" and its accepted
differences) describe `l2r-base12` (history).

## Summary

**Kind:** missing feature, partly fixed upstream. **Status:** not
patched; on `36a55a0f` lean2rr's emitter gives native's order in the
shapes that the first gate showed, and three documented differences
stay ([above](#on-upstream-36a55a0f)). On the bases
from 2026-10-25 (Phase 2) to `l2r-base12` (history): patches
02-a to 02-e left the series. lean2rr used upstream's drops for Direct
and TailLoop records and local worklist drops for the other
recursive records (entry 23, deleted on 2026-11-18, when upstream had
taken its design: [history](README.md#history-entries-19-23-and-24-deleted-2026-11-18)), and lean2rr's
runtime (leanrt) kept its pending releases on entry 23's stack (patches
23-k to 23-m). Two differences from native Lean remained, which the owner
accepted (2026-10-19): records that user code drops are freed in field
order, and a value shared by two fields of one freed cell can be
released at another position ([lean2rr](#lean2rr-since-phase-2)).

**Upstream (history, 2026-10-25):** Open at 00906e38, by design: upstream frees
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

(History of the bases up to `95d9a1c8`. The retcon coroutines named here
were deleted upstream on 2026-11-01.)

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
  makes an executor. (lean2rr's builds replaced these retcon drops with
  the worklist of entry 23, which freed with no state per level;
  upstream's expansion of their direct arms was entry 19. Both entries
  are deleted: upstream removed the retcon drops.)
- Order: source order, each member's whole subtree before the next member;
  the cell is freed after its children. #682's test says it covers the
  hazard of old patch 13-d "without importing its pending stack's
  different, last-pushed-first member policy".

Checked on 2026-10-19 with upstream alone (7954a367 plus 10-a, 05-a and
07-a, no 02-x): the plain repros of old entry 13 (a list, a snoc list and a
left spine of 1,000,000 cells on an 8 MB stack) and of old entry 27
(1,000,000 links through `Nullable`) print the right values.

## lean2rr since Phase 2

(This section describes `l2r-base12`: history. For `36a55a0f` see
[on upstream 36a55a0f](#on-upstream-36a55a0f).)

leanrt frees arrays, references, thunk and task cells, boxes, handles and
promises. Its stack of pending releases and its "releasing" flag
(`runtime/leanrt/src/pending.rs`) are Reussir's drop stack and its
draining flag (entry 23, with patches 23-k to 23-m: runs, steps, the end
work). Reussir frees records with upstream's glue (Direct and TailLoop
records) and with entry 23's worklist (the other recursive records): at
a cell's visit its other members are released at once, in field order,
and its dead children of the cycle are pushed onto that stack and come
out last first (the deleted entry 23, section "Order of releases"; git history). The
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
  constructor). Tests with expectation files on `l2r-base12`:
  `RtDepDropOrderBoxed`, `RtDropUserListHandles`,
  `RtPromiseDropRecordPending` (a dependent of a promise in a record's
  first field ran before a later field's handle was closed). The last two
  are identical to native on `36a55a0f` ([above](#on-upstream-36a55a0f)),
  and so is `RtDepDropOrderBoxed` since lean2rr releases a value whose
  constructor native Lean knows field by field. What is left of this
  difference there: a record without a cycle that Reussir's own code
  drops in place (a matched value that dies in its `match` with nothing
  released before it; a value that dies alone at the start of a branch is
  released by lean2rr itself since review RV7).
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

- [`repros/bug02-nested-run-order.rr`](repros/bug02-nested-run-order.rr):
  the runtime's rule for a drop run that starts inside a running scope
  (prints `1 2` and `2 1` on `36a55a0f`, `2 1` twice on `l2r-base12`).
  Built by hand with the command in its header; `run.sh` does not run
  it (nothing to fix in Reussir).

The Miri test of 02-c's stack (`bug02-unlink-provenance.rs`) left with
02-c (git history).

## Upstream note

Not offered upstream: upstream chose another design (above). A request
would be the start and end of the outermost drop glue as host hooks, so
that a host runtime can keep its own order inside a free that user code
starts. At `36a55a0f` upstream has a part of that: a host can run work
after the outermost scope (`defer_until_scope_exit`) and join a running
scope (`join_or_run`, `join_or_run_step`). A sketch of native Lean's
rule as a third drop order (lean2rr's issue #1, 2026-10-20) got no
reply.
