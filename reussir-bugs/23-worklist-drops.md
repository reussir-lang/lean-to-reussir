# 23. Freeing a deep recursive value keeps one coroutine frame per level

**Kind:** cost (memory and run time of frees). Not a bug by Reussir's
rules: upstream promises that a drop runs at a bounded stack depth, and
it does. But the heap state of a drop grows with the depth of the value:
upstream frees the records of a `Worklist` type (a recursive type that
is neither Direct nor TailLoop) with retcon coroutines, and keeps one
suspended coroutine frame for each level of the value until the level
below it is freed. Whether memory that grows with depth counts as
erroneous is a judgement; the measured effect: lean2rr's
`RtClosureChainFree` (a chain of 10^6 closures) peaks at 652 MB where
native Lean peaks at 102 MB. Patches 23-a to 23-j free these records
with a per-thread stack of pending drops instead, the way Lean's
`lean_del` frees: no state per level for a one-sided chain. Patches
23-k to 23-m let lean2rr's runtime share that stack (end work after the
outermost drain, runs of cells, steps), so that one drain frees records
and runtime objects in one order and no Lean code runs inside a drain.
Patches 23-n to 23-p keep a pending record linked through its own header
when the release function changes, so that it costs no memory while it
waits, as in Lean's to-do list.

## Summary

**Kind:** cost (memory and run time), with a fix that bounds the
memory: the patches are optimizations, and 23-k to 23-m the features a
host runtime needs to share the stack. **Status:** patched (23-a to
23-p), applied in `./reussir`'s series since 2026-10-25 (branch
`l2r-base11`, commits `82b3985a` to `0bea9c7d`). `scripts/l2r.py`
requires the patches: it stops with an error when the Reussir checkout
lacks 23-f (the switch of rrc's pipeline to worklist drops), 23-k (the
end work), 23-m (steps, depth and drain), 23-n (`defer_wide`) or 23-o
(the glue's use of it; `REQUIRED_REUSSIR_PATCHES`), and leanrt's pending
stack does not compile without 23-k to 23-m. 23-p, an optimization of
instructions, is not checked.

**Upstream (2026-10-25):** Open at 00906e38, by design: upstream's drops
of Worklist types are retcon coroutines (#678, #679), with a bounded
stack depth and a heap frame per suspended level. Not reported. The
patches are made for Reussir's maintainer, who takes Reussir-side
changes for lean2rr from this directory ([policy](README.md#policy));
the larger follow-up, deleting the then unreachable retcon lowering,
is listed under [open items](#open-items).

The entry replaces the earlier work on the same cost, which was never
published here: a local patch that made retcon destructors share their
suspend points (`./reussir`'s branch `l2r-mergesusp`, commit
`a8f3fc70`, once numbered entry 22; LLVM's CoroSplit copies a
coroutine once per suspend point). With 23-f no pipeline makes retcon
destructors, so that patch has nothing left to improve; number 22 is
retired.

## Context

- **Record drop kinds** (upstream #675 to #682;
  `RecordType::classifyRecordDrop`, `lib/IR/RecordDrop.cpp`). A named
  record type with no cycle is *Direct*; one whose only recursive member
  is its last managed member is *TailLoop* (its drop is a `musttail`
  loop, `TailDrop.cpp`); any other recursive type is *Worklist*: a tree
  with two recursive fields, a list whose recursive field comes first, a
  closure enum whose arm captures the next closure before a value.
- **Upstream's Worklist drop** (#678 `58a6ce24`, #679 `20a6dd3d`). The
  destructor is a retcon coroutine (LLVM's `llvm.coro.id.retcon`). A drop
  of a recursive member suspends and yields the child to a per-thread
  executor (`crates/reussir-rt/src/dtor_executor.rs`), which runs the
  child's destructor and then resumes the parent. The order is source
  order: each member's whole subtree before the next member, the cell
  freed after its children. A parent resumes only after its first
  child's whole subtree is freed, so the parent's frame (the members it
  has not released yet) must live that long: one frame per level of the
  value, whatever the order of suspensions.
- **lean2rr.** Lean's inductive types with two recursive fields, or a
  recursive field before others, and lean2rr's closure types (one enum
  per closure type, an arm per closure kind, recursive through the arms
  that capture closures) are Worklist types. Until Phase 2 (2026-10-25)
  lean2rr's builds turned upstream's retcon drops off and freed through
  local patches 02-a to 02-e ([issue 2](02-native-drop-order.md));
  Phase 2's first base (`l2r-base7`) used upstream's retcon drops.

## Symptom and repro

Repro [`repros/bug23-deep-free.rr`](repros/bug23-deep-free.rr) with its
driver [`repros/bug23-deep-free.c`](repros/bug23-deep-free.c) (the
values of Reussir's test `frontend/worklist_drop_depth.rr`, which 23-g
adds): on a 256 KiB thread stack, one process per value builds a value
of 10^6 levels and frees it: one-sided trees of two recursive fields
(left-deep and right-deep), a chain of a 64-arm enum whose recursive
member comes first (the shape of a closure enum that captures the next
closure, then a value), and compositions of two recursive fields. The
driver prints how much peak RSS grew during the free.

**Command.** `run.sh RRC_CHECKOUT 23` (rrc `--emit obj -O aggressive`,
then `cc` with the checkout's `libreussir_rt`).

**Expected:** no growth with the depth (native Lean frees each of these
with a few kilobytes of to-do stack).

**Actual on upstream** (00906e38, 2026-10-25): the peak grows by 83972
KiB for each tree, 608264 KiB for the enum chain and 86020 KiB for the
compositions: about 85, 622 and 88 bytes per level (CoroSplit gives
each arm's spilled child its own frame slot, so the frame grows with the
number of arms). `run.sh` prints `REPRODUCES`. With 23-a to 23-j
(`l2r-base9`): 2052 KiB for each tree and nothing for the others
(allocator noise); with 23-k to 23-m too (`l2r-base9-shared`), and
with 23-a to 23-p (`l2r-base10`): nothing for any of the four. `run.sh`
prints `FIXED` on all three.

Through lean2rr (Phase 2's lean2rr, 10^6 levels, peak RSS):

| Program | native | `l2r-base7` (retcon) | with 23-a to 23-j |
|---|---|---|---|
| `RtDeepTreeFree` (left- and right-deep binary trees; freed by user code and by a reference's `set`) | 38.8 MB | 111 MB | 37.3 to 37.5 MB |
| `RtClosureChainFree`, a chain of closures that capture the next closure first | 102 MB | 652 MB | 68.1 MB |
| `RtClosureChainFree`, compositions of closures | 85.8 MB | 156 MB | 82.4 MB |

Before Phase 2, with the local drop patches (dev's lean2rr on
`l2r-stepd`), the same programs peaked at 37.3 MB, 68.1 MB and 45.5 MB
(02-c linked the cells of a run through their headers, so a deferred
composition cost no stack entry; 23-a uses one 16-byte entry per
deferred cell). With 23-l (runs: 8 bytes per cell joined to a run) and
leanrt on the shared stack, the runtime side measured, on the first
version of 23-k to 23-m (`l2r-base9-shared-v1`, `fbc2bba2`): trees 37.3
MB, the closure chain 68 MB, compositions 66 MB, under both integer
representations, and both tests pass their alloc-check bounds (lean2rr's
phase2-dev branch, commit `92512534`). A shape that
alternates two types cost more there: `RtAltTreeFree` (mutual types A
and B with two recursive fields each, 10^6 levels, each level deferring a
small child of the other type) peaked at 88.7 MB on `l2r-base9-shared`,
native Lean at 55.1 MB; about 25 MB of the difference was the pending
vector (runs of one cell, 24 bytes each). With 23-n to 23-p
(`l2r-base10`, 2026-10-26): 45.7 MB, its allocations and bytes as
native's, under both integer representations
([linked records](#linked-pending-records-23-n-23-o-23-p)).

## Cause

A retcon destructor finishes a member's subtree before it goes on to
the next member, and frees its cell after the last one. The executor's
stack stays one frame deep, but each suspended parent keeps its
coroutine frame, so the frames of all levels between the root and the
cell being freed are alive at once. No order of suspensions inside this
design removes that: the parent must still hold the members it has not
released. A worklist that releases a cell's members at its visit, frees
the cell, and keeps only its dead children on a stack needs no state per
level for any one-sided chain, and at most one stack entry per dead
child in general.

## Patch

Sixteen patch files, 23-a to 23-p, each at most 300 changed lines with
its tests. TailLoop and Direct records are unchanged; TPDE mode (which only
the JIT front ends select) keeps plain recursive drops, as before.

| Patch | Commit | Kind | What it does |
|---|---|---|---|
| [23-a](patches/23-a-drop-stack-runtime.patch) | `82b3985a` | optimization (runtime) | a per-thread stack of pending drops in Reussir's runtime: `drop_stack.rs`, `__reussir_drop_run` and `__reussir_drop_defer` |
| [23-b](patches/23-b-drop-stack-ops.patch) | `14df94cc` | optimization (IR) | ops `reussir.rc.defer` and `reussir.drop.run`, verified and lowered to the two runtime calls |
| [23-c](patches/23-c-tail-drop-box-free.patch) | `752ef7ce` | refactor | TailDrop's free of a box as a shared helper, `emitBoxFree` (no change in what TailDrop emits) |
| [23-d](patches/23-d-worklist-drops-option.patch) | `0e8c4cb0` | optimization | worklist drops behind a new option of the acquire/drop expansion, `worklist-drops` |
| [23-e](patches/23-e-worklist-nullable-locked.patch) | `0fef47d1` | optimization and bug fix | nullable members and locked cells deferred by the glue too; the locked-drop function under every option, which also fixes [issue 24](24-locked-drop-token-leak.md) |
| [23-f](patches/23-f-pipelines-worklist-drops.patch) | `1418ad22` | optimization | rrc's pipeline, the C API and the C++ bridge use worklist drops where they used retcon drops |
| [23-g](patches/23-g-worklist-drop-tests.patch) | `563c1b95` | tests | deep frees on a small stack, under ASan, and the release order |
| [23-h](patches/23-h-worklist-leaf-arms.patch) | `c7f8015f` | optimization | a leaf arm dropped from user code is released in place, without the drain |
| [23-i](patches/23-i-worklist-tail-release.patch) | `77ccdcc0` | optimization | the last dead child of a freed cell continues as a `musttail` call |
| [23-j](patches/23-j-worklist-tail-two-children.patch) | `fc9c1d20` | optimization | the tail call takes the last dead of the arm's last two such members |
| [23-k](patches/23-k-drop-stack-end-work.patch) | `34df7ac4` | feature (for a host; fixes a regression with leanrt) | end work: one function that the outermost drain calls once it has ended (`set_end_work`, `want_end_work`) |
| [23-l](patches/23-l-drop-stack-runs.patch) | `f67d389f` | optimization (runtime) | runs of drops with one release function: 8 bytes per pending cell in a run instead of a 16-byte entry |
| [23-m](patches/23-m-drop-stack-steps.patch) | `6111586c` | feature (for a host) | steps (`defer_step`, `run_step`), `depth()` and `drain()`, so that a host frees its own objects on the same stack |
| [23-n](patches/23-n-drop-stack-linked-runs.patch) | `8792ae76` | optimization (memory) | `defer_wide` (C: `__reussir_drop_defer_wide`): a box with a wide header waits linked through its header, in a linked run of the stack |
| [23-o](patches/23-o-defer-wide-headers.patch) | `a5fb6e94` | optimization (memory) | the glue defers boxes with a wide header (variants, compound records aligned to 8) through `defer_wide` |
| [23-p](patches/23-p-same-release-cells.patch) | `0bea9c7d` | optimization (instructions) | in a linked run, a box after one of the same release function joins the run's cells; only a change of function links; a cache of the release table |

### The runtime stack (23-a)

`crates/reussir-rt/src/drop_stack.rs`, one thread-local without a
destructor: a "draining" flag and the entries' buffer (16 bytes per
pending entry: the box and its release function).

- `run(object, walk)` (C: `__reussir_drop_run`) calls `walk(object)`
  with the thread marked as draining. The outermost run then pops the
  entries that the walk deferred, last deferred first, until none is
  left; a release it pops may defer more. A run started while the
  thread drains (a drop in a popped release, or in a foreign hook that
  the drain runs) only calls the walk and returns; the running drain
  releases what it deferred. So the native stack stays bounded however
  deep the value is.
- `defer(cell, release)` (C: `__reussir_drop_defer`) pushes one entry
  while the thread drains; outside a drain it runs the release at once,
  as a run of it. The stack never reads or writes the cell.
- The buffer shrinks back to 64 entries after a drain. A guard frees it
  at thread exit; a drain that runs after the guard (a drop in a later
  thread-local destructor) frees the buffer it needed at its end.
- Both symbols are registered for in-process JITs (`symbols.rs`).

### The ops (23-b)

`reussir.rc.defer @release(%box)` hands over a shared box whose last
reference the caller owns (its count was observed to be one); the drain
later calls `@release(%box)`, which releases the content and frees the
box. `reussir.drop.run @walk(%ref)` calls `@walk(%ref)` with the thread
draining, then (outermost only) runs what was deferred. The verifier
requires a callee that takes exactly the operand's type and returns
nothing, and a shared (counted) box for `rc.defer`. The basic-ops
lowering emits the two runtime calls (`DropStackLowering.cpp`).

### The glue (23-d, 23-e)

With `worklist-drops`, per Worklist record type and atomic kind
(`WorklistDrop.cpp`):

- `<dtor>.worklist(ref)`, the entry, which every drop of the record
  calls: `reussir.drop.run @<dtor>.worklist.walk(ref)`.
- `<dtor>.worklist.walk(ref)`, marked `reussir.worklist_drop`: the
  record's ordinary member walk, except that a member box of a Worklist
  record (plain, behind a `Nullable`, in an array or in a cell) is
  decremented and, once its count reaches zero, deferred with
  `reussir.rc.defer @<dtor>.worklist.release`.
- `<dtor>.worklist.release(box)`, what the drain calls: the record's
  members released as the walk releases them, then the box freed.
- A locked cell's payload is released inside its critical section by a
  separate locked-drop function (`__reussir_locked_drop`, and inside
  glue `__reussir_locked_drop.worklist`, which defers the payload's
  Worklist box).

A Worklist value reached through other glue calls its entry, which then
only walks (the thread already drains). This stays bounded as long as
the glue defers every box edge of the record's cycle that the type graph
shows.

### The pipelines (23-f)

`reussirCreateAcquireDropExpansionPass`'s last parameter is now
`worklistDrops` (was `retconDrops`); rrc's pipeline passes the same value
as before (on, except under TPDE), and the C++ bridge sets
`worklistDrops` where it set `retconDrops`. No driver asks for retcon
drops any more: the retcon lowering, its LLVM passes and the runtime
executor stay, reachable only through `reussir-opt`'s `retcon-drops`
option and their own tests.

### The optimizations (23-h, 23-i, 23-j)

- **Leaf arms (23-h).** A drop that starts in user code went through
  `__reussir_drop_run` (a runtime call, the flag set and cleared, an
  indirect call) even for a leaf: an arm with no member that can reach a
  box of a Worklist record without passing a named record's box. The
  entry now dispatches on the tag when the variant has a leaf arm and
  releases a leaf arm in place. lean2rr's deriv benchmarks drop mostly
  leaf expressions (`Val`, `Var`): without 23-h the round trip cost
  +7.9% instructions on L03 (deriv 10) and +4.4% on X02 (deriv 8)
  against `l2r-base7`.
- **Tail calls (23-i, 23-j).** In the worklist order a freed cell's last
  dead child is released next, so a chain is a loop. The release
  function expands the record itself; the arm's last two member boxes
  that the walk would defer are decremented in their places (field
  order), and after the box's free the last dead one is called as a
  `musttail` call, the other deferred. This needs no member after them
  that may push work onto the drain (`mayPush`: a member that can reach
  a Worklist record, a closure or an FFI object, whose hooks may push);
  otherwise the child is deferred in its place as in the walk. On
  WebAssembly (no `tail-call` feature recorded in the module) the
  release calls the walk instead.
- **The type predicates** (`holdsWorklistBox` for 23-h, `mayPush` for
  23-i) are one reachability walk per query with a cache (a miss caches
  every type it visited, a hit the queried type): linear in the types
  reached. A review found the first version exponential on generated
  inputs (K variants in TailLoop cycles: at K = 24 more than a minute);
  now the pass takes 3 to 6 ms at K = 16, 24 and 32. Printing those
  types (`--emit mlir`, `reussir-opt`'s output) stays exponential, as
  on upstream (entry [4](04-emit-mlir-size.md)'s cause).

### The shared stack (23-k, 23-l, 23-m)

Made by the runtime side for leanrt, whose own stack of pending releases
(`runtime/leanrt/src/pending.rs`) is now built on this one.

- **End work (23-k).** A host registers one end function
  (`set_end_work`) and a release asks for it (`want_end_work`); the
  outermost drain calls it once it has ended, with the thread no longer
  draining and nothing pending. Outside a drain the request calls it at
  once. It is for work that must not run inside a drain because it may
  block or switch contexts (leanrt: promise resolutions put off, a
  stream's hand-off), since the drain state is the thread's: a context
  suspended inside a drain would make every other context's drop join
  the suspended drain. A drain that nobody asked costs one test at its
  end. An end function whose own drops ask for the end work again gets
  it at the end of their drains, inside the call: one nesting level per
  generation, as native Lean's frees nest inside the dependents they run
  (deliberate).
- **Runs (23-l).** Drops deferred one after the other with one release
  function form one run: the run (release, last cell, count) is one
  entry, kept in the thread's state while it is the top one, and each of
  its cells but the last is one pointer in a second vector. A cell
  joined to a run takes 8 bytes (4 on wasm32) instead of a 16-byte
  entry (8); a run of one cell below the top takes a 24-byte entry (12
  on wasm32), so drops that alternate release functions (the dead
  children of two record types in turn) took half as much again while
  they waited, until 23-n linked the glue's records. The order is the
  same, last deferred first. Runs form only
  between equal function pointers: a function reified twice may get two
  addresses, which costs entries, never order.
- **Steps, depth and drain (23-m).** A step (`defer_step`, `run_step`)
  is incremental work that stays on the stack until it answers that it
  is done, run again after what it deferred meanwhile (leanrt's array
  free, in native Lean's two passes). A step is
  `unsafe extern "C" fn(usize) -> bool`, as a release is `extern "C"`:
  one that panics aborts instead of unwinding out of the drain with the
  thread still marked as draining. `depth()` is the number of entries;
  `drain()` runs what is pending and returns at once inside a drain.
  Outside a drain the stack stays empty (checked in debug builds).

**The regression they fix** (on `l2r-base9`, which had 23-a to 23-j
only, with Phase 2's runtime). Reussir's drain and leanrt's stack were
separate, and leanrt ran Lean code inside Reussir's drain: a promise
dropped there was resolved at once and its `sync` dependents ran inside
the drain, and leanrt's own end work ran there too. Lean code that freed
a Worklist record inside the drain, or a task it waited for (which runs
on the waiter's stack), only joined the drain, whose dead children then
waited until the outer drain resumed. So a promise dropped that way was
not resolved (lean2rr's test `RtPromiseDepFreeInDrain`: `false`,
natively `true`), and code that waited for it hung
(`RtPromiseDepWaitInDrain`); dev on `l2r-base8` gives native's results.
With 23-k to 23-m, leanrt's pending stack is this stack, its end work is
the stack's end function, and no Lean code runs inside any drain; both
tests pass (lean2rr's phase2-dev branch, commits `fbd9f1c2` and
`d502cd7d`, 2026-10-25).

### Linked pending records (23-n, 23-o, 23-p)

With the shared stack, a pending record of the glue cost 8 bytes in a
run of cells, and a 24-byte entry when its release function differed
from the previous one's: a chain whose levels each leave a record of
another type pending (`RtAltTreeFree`) took 24 bytes per level while it
waited, 88.7 MB at 10^6 levels against native Lean's 55.1 MB. Lean's
to-do list is linked through the freed objects; the earlier local stack
(02-b) linked its records through their headers too (45.7 MB there).

- **Linked runs (23-n).** `defer_wide` (C: `__reussir_drop_defer_wide`)
  takes a box whose first 8 bytes are header: its 32-bit count, then a
  32-bit word whose upper 16 bits are 0 (a variant's tag, below 2^16) or
  padding. Such boxes form a linked run, one entry of the stack like a
  run of cells, so host cells, runs and steps interleave last deferred
  first as before, and `depth()` counts it once. A box links to the box
  deferred before it through its count and those 16 bits (48 bits): a
  40-bit signed offset in 8-byte units and, in the high 8 bits, 1 plus
  the index of the previous box's release function in a per-thread table
  of 255 functions, emptied with the stack (02-b's encoding). A pop
  reads the link and writes count 1 and the upper bits 0 back before the
  box's release runs; the release reads neither the count nor the bits
  above the tag. The box is the caller's alone until its release (its
  count was observed to be 1, or reached 0 for an atomic box). A box
  that cannot link starts a new run: one with a nonzero top byte (under
  top-byte tagging an immediate's dummy box, which the glue never
  defers), one farther than 2^42 bytes or not a multiple of 8 bytes
  away, or a new function with the table full. The previous box's
  provenance is exposed and the pop rebuilds the pointer from its
  address (Miri's default mode accepts that; `-Zmiri-strict-provenance`
  rejects it, as expected). The table is a zero-initialized thread-local
  of its own (a new thread's TLS image does not grow), and a run's linked
  flag below the top is the top bit of its count (an entry stays 12
  bytes on 32-bit targets). The stack still never writes a host's cell.
- **The glue (23-o).** The lowering of `reussir.rc.defer` calls
  `__reussir_drop_defer_wide` for a fused variant box with at most 2^16
  arms (the count, then the i32 tag) and for a compound record box whose
  payload starts at offset 8 or later (the box is `{i32, payload}`, not
  packed, so the payload starts at its alignment); other boxes keep
  `__reussir_drop_defer`. Every Worklist variant qualifies, and every
  Worklist compound record on 64-bit targets (its box members are 8-byte
  pointers); on i686 and wasm32 a compound record without 8-byte members
  does not.
- **One function's records as cells (23-p).** Linking every pending box
  cost instructions where the glue defers one child per freed cell (a
  balanced tree +6.5 instructions per freed cell, a rose tree +5.8). So
  a box deferred after a box of the same release function joins the
  linked run's cells (8 bytes while it waits; for a value of one type
  usually as many as its height), with the upper 16 bits of its header's
  second word set to 0, and only a change of function links (those bits
  are then never 0, so a pop tells a link from a cell). The table lookup
  on a change goes through a 16-slot cache of (function, index) pairs.

**Measured** (2026-10-26; base9-shared = `6111586c`, 23-n = linking every
box, 23-p = the series' head):

| Instructions per freed cell (plain Reussir microbenchmark) | base9-shared | 23-n | 23-p |
|---|---|---|---|
| left-deep, right-deep binary trees | 41.83, 42.33 | 41.83, 42.33 | 41.83, 42.33 |
| balanced binary tree (depth 20) | 57.08 | 63.58 | 59.08 |
| 64-arm enum chain; compositions left, right | 41.77; 45.33, 47.33 | the same | the same |
| rose tree (depth 12) | 52.77 | 58.54 | 54.55 |
| alternating pending nodes (two mutual types) | 66.07 | 74.60 | 74.60 |

lean2rr (the leanrt backend, instructions): L06 (binary trees) 6011.06M
on base9-shared, 6011.06M with 23-p; X02 (deriv 8) 128.6M and 129.7M;
E07 (rose tree) 362.4M and 365.6M; the same outputs. Peak RSS at 10^6
levels (alloc-check, both integer representations for the first two):
`RtAltTreeFree` 45.7 MB (native 55.1; base9-shared 88.7);
`RtDeepTreeFree` 37.3 to 37.5 MB (native 38.7); `RtClosureChainFree`
68.2 to 68.4 MB in its closure modes (native 102.2), compositions 66.2
MB (native 85.8; linking every box, 23-n alone, 45.9 MB: one function's
pending records are cells again), `list` 109.2 MB (native 163.7).
`RtDepPolyRec`'s rrc: 127.5 s and 3.62 GB on base9-shared, 130.8 s and
3.71 GB with 23-n and 23-o (one run each, on a busy machine).

## Order of releases

For a value of a Worklist type that is freed:

- **With 23-a to 23-m:** at a cell's visit, every member that is not a
  box of the record's cycle is released at once, in field order, each to
  its end (a string, a handle, a TailLoop list); the boxes of the cycle
  whose count reaches zero are kept; the cell is freed; the kept
  children are released later, the last one first (the last one as a
  tail call when nothing after it can push). A leaf arm dropped by user
  code is released in place, in field order (23-h).
- **Native Lean** (`lean_del_core`): every field of a freed cell whose
  count reaches zero is pushed onto the thread's to-do stack, whatever
  its kind, and the stack is popped last pushed first. So the children
  of the cycle come out in the same order (the last first), but native
  Lean also defers the other fields: for `Node(l, h, r)` with a handle
  `h`, native frees `r`'s subtree, then closes `h`, then frees `l`'s
  subtree; the patches close `h` first, then free `r`'s subtree, then
  `l`'s.
- **Nested drops.** A drop that starts inside the drain (in a foreign
  hook, say) returns before its dead children are released; they are
  released after the hook returns. Native Lean's nested `lean_del`
  completes first.
- **Upstream** (retcon): source order, each member's whole subtree
  before the next member, the cell freed after its children.

- **When user code drops a Worklist record** the drop of the root is
  expanded at the site, not through the entry: the root's members go in
  field order, and each dead Worklist child is a drain of its own that
  ends before the next member.

lean2rr's runtime (leanrt) keeps its pending releases for runtime
objects (arrays, references, boxes, handles, promises) on this stack
since 23-k to 23-m, with one "draining" flag for both. A runtime object
that Reussir's glue reaches inside a drain is pushed onto the same
stack, so one drain pops records and runtime objects in one order, last
pushed first: the reverse of the glue's visit, which is native Lean's
order ([issue 2](02-native-drop-order.md#lean2rr-since-phase-2)). On
`l2r-base9` (23-a to 23-j only) the two stacks were separate, and a
tree's handles inside a leanrt free closed per subtree: lean2rr's
`RtDropOrderRec` gave `T6 T7 T3 T1 T4 T5 T2` (natively `T7 T3 T6 T1 T5
T2 T4`). With the shared stack it gives native's order again (the
runtime side's check, phase2-dev `d502cd7d`).

## Tests

In the patches (Reussir's lit tests, unit tests and Rust tests):

- `drop_stack/tests.rs` (23-a): last deferred first with nested
  deferrals; a run inside a release joins the drain; a chain of 10^6
  cells on a 64 KiB thread stack; 10^4 pending entries and the shrink
  afterwards; a defer outside a drain; a drop in a thread-local
  destructor after the guard's; the exported symbols. Also under Miri
  (smaller sizes).
- `conversion/drop_stack_ops.mlir`, `drop_stack_invalid.mlir` (23-b):
  the ops' round trip, lowering and verifier (rigid and flex boxes
  rejected).
- `conversion/worklist_drop.mlir`, `worklist_drop_members.mlir` (23-d,
  23-e, 23-h, 23-i, 23-j): the entry, walk and release, nullable, cell,
  mutex and plain members of the cycle, leaf arms, anonymous records,
  the tail calls, the cases that keep a child deferred, and the wasm32
  release.
- `conversion/locked_cell_drop.mlir`, `mutex_cell_drop.mlir`,
  `rwlock_cell_drop.mlir`, `flatlock_cell_drop.mlir` (23-e): the locked
  drop function and its token free.
- `codegen/retcon_drop_targets.rr`, `executable_pic_default_retcon.rr`,
  `frontend/coff_comdat.rr`, `frontend/retcon_drop.rr` (23-f, 23-i): what
  rrc emits for a recursive enum on seven targets.
- `frontend/worklist_drop_depth.rr` (23-g): the repro's four values in
  one process, at `-O aggressive` and `-O none`; it fails when the peak
  grows by 16 MiB or more during a free (on `l2r-base7`, the left-deep
  tree grew it by 84 MiB). `sanitizer/e2e/worklist_drop_depth.rr`: the
  same frees at 10^5 levels under ASan.
- `runtime/drop_member_order.mlir` (23-g): the release order of chains,
  a complete binary tree, shared subtrees and inline children, with
  worklist drops. The test no longer covers the retcon order.
- `drop_stack/tests.rs` (23-k to 23-m): the end work after the
  outermost drain and outside a drain; the entries and cells of three
  runs and their order; a step that yields to its deferrals, a step done
  with work above it, a step deferred inside a drain, an empty drain.
- `drop_stack/tests.rs` (23-n, 23-p): alternating releases in one linked
  entry with no cells, headers restored before each release, boxes that
  cannot link starting runs, the table emptied after the drain; a random
  program of drops, steps and nested runs whose events are identical
  whether its boxes go through `defer_wide` or `defer` (boxes with
  garbage in the upper half of their second word, as padding has; the
  wide run must use cells too).
- `conversion/drop_stack_ops.mlir` (23-o): a compound record aligned to
  8 and a variant through the wide entry, one aligned to 4 through the
  plain one. `frontend/worklist_drop_depth.rr` gains a chain of two
  mutually recursive types whose levels each leave a small node of the
  other type pending, 10^6 levels: the peak grew by 45060 KiB with 23-a
  to 23-m; it must grow by less than 16 MiB. The ASan run frees it at
  10^5 levels.

Results on `l2r-base9` (`fc9c1d20`, 2026-10-25, a build with the tests
and the ASan runtime): Reussir's lit tests 776 passed, 125 unsupported,
2 failed (`frontend/kernel_launch_config_errors.rr` and
`kernel_launch_disabled.rr`: the test environment has no `not` tool;
they fail the same way without the patches); `reussir-ut` 82 of 82. On
the series' first base (`l2r-base7` with 19-a, the same code of 23-a to
23-j): reussir-rt's tests 66 of 66, `drop_stack` 6 of 6 under Miri, the
review's ASan programs (sharing shapes, mutual recursion through arrays,
cells, nullables and `Arc`, value records, closures, locked cells; nested
runs) clean, and rrepl's JIT tests 29 of 29 (rrepl frees 3 x 10^5
levels at `-O aggressive`). 23-k to 23-m change only reussir-rt
(`drop_stack.rs` and its tests). On `l2r-base9-shared` (`6111586c`) the
repros of entries 19 and 23 print FIXED (23: no growth for any of the
four values; on `l2r-base9`, before the runs, 2052 KiB for each tree);
on the first version of 23-k to 23-m (`fbc2bba2`) the runtime side
reported leanrt's unit tests 101 of 101 (leanrt build) and 104 of 104
(rcgmp build), and the trace digests of its 400 random order scenarios
equal to those of leanrt's own stack before (phase2-dev `d502cd7d`).
On `l2r-base10` (`0bea9c7d`, 2026-10-26): reussir-rt's tests 73 of 73,
`drop_stack` 13 of 13 under Miri (stacked and tree borrows), the
drop-related lit tests 26 of 26 (one unsupported) with the ASan run of
`worklist_drop_depth`, `reussir-ut` 82 of 82; with 23-n and 23-o, the
whole lit suite 776 passed, 125 unsupported and the 2 failures for want
of the `not` tool; lean2rr's 31 release-order and deep-free tests and
leanrt's unit tests 101 of 101 and 104 of 104.

## Measurements

Instructions per freed cell (plain Reussir microbenchmark, 10^6 levels,
cachegrind; `l2r-base7` = upstream's retcon drops with 19-a, `l2r-stepd`
= the old local drop patches):

| Shape | `l2r-base7` | `l2r-stepd` | with 23-a to 23-j |
|---|---|---|---|
| left-deep binary tree | 73.3 | 63.3 | 41.8 |
| right-deep binary tree | 72.6 | 42.8 | 42.3 |
| balanced binary tree (depth 20) | 57.4 | 61.1 | 53.1 |
| 64-arm enum chain, recursive member first | 98.6 | 41.8 | 41.8 |
| compositions nested on the left | 109.2 | 92.3 | 45.3 |
| compositions nested on the right | 106.7 | 48.3 | 47.3 |
| rose tree (depth 12) | 66.8 | 64.8 | 49.2 |

lean2rr's programs (instructions, cachegrind, the leanrt backend; the
same outputs): X02 (deriv 8) 130.9M on `l2r-base7`, 128.0M on
`l2r-stepd`, 125.0M with the patches; L03 (deriv 10) 7427M, 7425M,
7103M; E07 (rose tree) 362.6M, 383.1M, 362.6M; L01 (red-black tree)
1685M, 1658M, 1676M; L06 (binary trees) 6045M, 6011M, 6011M.

rrc's compile time and memory (lean2rr's rrc flags, `--emit obj`):
`RtDepPolyRec` 4.41 GB and 126 s on `l2r-base7`, 3.40 GB and 99 s on
`l2r-stepd`, 3.43 GB and 111 s with the patches (no CoroSplit);
`RtSyncSelect` 1.92 GB and 63 s, 1.89 GB and 59 s, 1.95 GB and 59 s.
The measurements above are of 23-a to 23-j (23-k to 23-m change the
runtime stack only: a cell joined to a run takes 8 bytes, a run of one
below the top 24). On
`l2r-base9` (without 19-a, which worklist drops do not reach):
`RtDepPolyRec` 3.47 GB and 109 s, `RtSyncSelect` 1.94 GB and 57 s.

## Reviews

Two adversarial reviews (code, targeted repros, ASan, mutations of the
release order), then an independent re-review of the reworked series;
notes in `lifodrop-review/` (local). Round one found two order bugs and
fixed them in the patches: the tail call taken although a later member
pushed work (the subtrees came out reordered; now `mayPush`, test case
`OrderTri`), and an anonymous recursive arm taken for a leaf (the entry
recursed once per level: a crash at 10^5 levels on a 256 KiB stack; now
the classification walks into anonymous boxes). It also found the
locked-cell token leak of TPDE mode ([issue 24](24-locked-drop-token-leak.md),
fixed in 23-e by using the locked-drop function under every option), a
`rc.defer` of a flex box that verified (now rejected), a defer outside a
drain that waited for a later, unrelated drain (now it runs at once), a
drop after the thread-exit guard that leaked the buffer (now freed), and
the documentation and test gaps that the patches now cover. The re-review found the type
predicates exponential on generated inputs (fixed: one reachability
walk per query) and nothing else. Two mutations of the release order
(swapping the tail call and the deferral; moving an inline member) make
`runtime/drop_member_order.mlir` fail.

23-k to 23-m were made by the runtime side and reviewed adversarially
(2026-10-25); the review's fixes are in the patches (a step is
`extern "C"`, so a panicking step aborts; the nesting of end work and the
entry costs of runs documented). 23-n and 23-o were reviewed
adversarially (2026-10-26, notes in `lifodrop-review/rt/link/`): no bug.
Every box that 23-o routes to `defer_wide` has the header it claims on
every target (i686 narrow, wasm32 right, big-endian safe); the headers
are back before each release; the order holds with host cells, steps,
runs, nested runs and end work in a model check with real boxes (3000
seeds x 3 natively, 40 x 3 under Miri with both borrow models); the
40-bit offset links at +-2^42 and starts a run beyond. Its cleanups
(the table zero-initialized, the linked flag in the count's top bit, two
comments) are in 23-n. The runtime side found the order digests of its
400 scenarios unchanged. 23-p's re-review follows; the review's model
check, with a joined box allowed (count untouched, upper bits 0), passes
against it (3000 x 3 natively, 40 x 3 under Miri).

## Open items

- **A chain through a `[value]` variant** (`S { o: [value] Opt(S), v }`):
  the release calls the variant's entry, a nested `__reussir_drop_run`
  of its walk, a deferral and a pop per level, and no tail call. The
  memory stays bounded; the cost is a few calls per level.
- **A member after the last child that can reach an FFI object or a
  closure** keeps the child deferred (`mayPush` is conservative: such a
  member's hook may push), so such a chain costs a deferral and a pop
  per level. Under lean2rr's leanrt backend (until D8, 2026-10-26) a
  `Nat` field after the recursive fields was such a member (a tagged FFI
  handle).
- **TPDE mode keeps plain recursive drops.** rrepl's default level, when
  Reussir is built with TPDE, is TPDE: a tree of 10^6 levels overflows
  its stack there (upstream and the series alike; `-O none`, `default`,
  `aggressive` and `size` are fine). lean2rr does not use the JIT.
- **Recursion through a closure's captures** is not in the type graph:
  a Worklist enum whose cycle passes through a Reussir closure's
  captures overflows a 256 KiB stack at 10^5 levels (upstream's retcon
  drops alike). lean2rr's closures are records (enums of closure arms),
  which the type graph sees.
- **TailDrop's `musttail` on WebAssembly.** Upstream's tail drop of a
  TailLoop type is a `musttail` call, which llc rejects for
  `wasm32-wasip1` unless the module has the `tail-call` feature (seen
  on `l2r-base7` with a list's tail drop). 23-i avoids `musttail` on
  wasm; TailDrop is unchanged. A bug of upstream that lean2rr does
  not reach (no wasm target).
- **One function's pending records are cells.** Since 23-p a record
  deferred after one of the same release function takes 8 bytes in a
  run of cells (fewer instructions than a link); for a value of one type
  usually as many as its height, but a chain of one type that leaves a
  record pending per level takes 8 bytes per level (the compositions of
  `RtClosureChainFree`: 66.2 MB, 45.9 MB with every record linked;
  native 85.8 MB).
- **Delete the retcon lowering.** No driver reaches it after 23-f: the
  retcon expansion in `AcquireDropExpansion.cpp`, the LLVM passes
  (`reussir-retcon-drop`), `dtor_executor.rs` and their tests. More than
  300 changed lines per component; not written.

The stack shared with leanrt, an open item of the first version, is
23-k to 23-m ([above](#the-shared-stack-23-k-23-l-23-m)), and the links
of the glue's own pending records through their headers 23-n to 23-p
([above](#linked-pending-records-23-n-23-o-23-p)).

## Upstream note

Not reported upstream. A report would say: retcon destructors keep one
coroutine frame per level of the value being freed (85 to 622 bytes per
level in the measurements above; a lean2rr program at 652 MB against
native Lean's 102 MB); a worklist that releases a cell's members at its
visit, frees the cell and keeps only its dead children (23-a to 23-j)
needs no state per level for any one-sided chain and frees with fewer
instructions per cell.
