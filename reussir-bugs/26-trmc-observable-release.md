# 26. TRMC moves a self call before a release that runs a foreign cleanup

**Kind:** bug (wrong order of effects). Reussir's tail-recursion-modulo-cons
pass (TRMC) moves a self call past the releases that stand between the
call and the constructor that takes its result. When such a release runs
foreign code (the cleanup hook of an FFI object, or the drop of a
closure), that code runs before the recursion, where the source runs it
after. Patch 26-a keeps the self call in place there.

## Summary

**Kind:** bug. **Status:** patched (26-a), in the series on upstream
`36a55a0f` (Reussir branch `l2r-base13-r7`, tree `6dc99546`; the patch is the file `patches/26-a-trmc-observable-release.patch`).
lean2rr's programs are not known to reach the bug: one constructed Lean
program gave native's output, and the patch changes no TRMC helper of
the 19 lean2rr programs that the review compiled. `scripts/l2r.py`
requires the patch all the same (it checks for the text
`runsObservableCleanup` in `TRMCRecursionAnalysis.cpp`): without it a
build succeeds, and a program that does reach the bug gets a wrong
release order with no message.

**Upstream (2026-11-18):** Open at `36a55a0f`. Old: the same wrong
output on `l2r-base12` (upstream `95d9a1c8`). Not reported: the
maintainer takes fixes from this directory. The patch applies to a clean
`36a55a0f` alone, and together with 27-a and 28-a.

## Context

- **TRMC.** A function such as `fn build(n) { ...; let rest = build(n - 1);
  Cons { x, rest } }` is not tail recursive: the constructor comes after
  the self call. TRMC makes a helper (`build.trmc`) that builds the
  constructor first, with a hole, and then calls itself to fill the hole.
  So the recursion is a loop. To do this, the pass must move the self
  call after the operations that stand between it and the constructor.
- **What may move.** Upstream #984 (`ba79790e`) states the
  rule: an operation may go before the self call only if that is not
  observable. A store, a cell read or another call keeps the self call in
  place, and that function then gets no loop (the "apply fallback").
  `canPrecedeSelfCall` decides
  (`lib/Transformation/TRMCRecursionAnalysis/TRMCRecursionAnalysis.cpp:297`
  at `36a55a0f`).
- **Releases.** At the pass, the release of a value is still one
  operation, `reussir.rc.dec` or `reussir.ref.drop`, or an `scf.if`
  marked `reussir.expanded_decrement`. The call of a foreign cleanup
  hook appears only later, in the lowering.

## Symptom and repro

Repro [`repros/bug26-trmc-observable-release.rr`](repros/bug26-trmc-observable-release.rr)
with its C driver. A foreign handle type is a clone of one Rust `Arc`,
so the `Arc`'s strong count says how many handles are open.
`open_count()` is called in the base case of the recursion.

```
fn build(n: u64) -> List {                       // the TRMC shape
    if n == 0 { List::Cons { open_count(), List::Nil } } else {
        let b = Holder { id: n, h: open() };
        let rest = build(n - 1);
        List::Cons { b.id, rest }                // b is used after the call
    }
}
fn depth(n: u64) -> u64 {                        // control: no constructor
    if n == 0 { open_count() } else {
        let b = Holder { id: n, h: open() };
        let rest = depth(n - 1);
        b.id * 0 + rest
    }
}
```

**Expected:** both functions see 3 open handles at the leaf (`n` = 3):
each level's `b` lives until after its self call.

**Actual on pristine `36a55a0f`,** at `-O none`, `-O default` and
`-O aggressive` (the pass runs at every level, and no switch turns it
off):

```
build: open handles at the leaf = 0
control: open handles at the leaf = 3
```

`l2r-base12` at `-O default`: the same. With 26-a: 3 and 3 at all three
levels. A second shape, a closure that captured the handle and is called
after the recursion, gave 3 at `-O none` and 0 at `-O aggressive` on
pristine upstream, and 3 at both with the patch.

## Cause

`canPrecedeSelfCall` accepts every `rc.dec`, every `ref.drop` and every
`scf.if` with `reussir.expanded_decrement` as bookkeeping, and does not
look inside. The release of a record with a foreign member is such an
expanded decrement; its branch for the last reference holds
`reussir.rc.dec(%h : rc<ffi_object>) cleanup(@hook)`. #984 made stores,
cell reads and calls keep the self call in place, and left this one out,
because it is not yet a call at that point.

Why it is a bug and not a legal move of a release: no text of Reussir
lets a pass move a release across a call. The pass's own rule is "only
what is not observable", and upstream treats the order of foreign
cleanups as observable in its drop code
(`RecordType::hasObservableCleanup`, the tests
`worklist_observable_order` and `drop_order_default`). One doubt stays:
the maintainer can say that the time of a release is not specified.
Then the patch is still what #984 intends.

## lean2rr

- lean2rr's own releases (`l2r_release_after`) are FFI calls. Since
  #984, a call between the self call and its constructor keeps the self
  call in place, so they are never moved on this base.
- A release that Reussir places itself can reach the bug only when a
  value that may hold a resource has its last use, which is not a call,
  between a self call and the constructor that takes the call's result.
  One constructed Lean program of that shape (a map over holders of file
  handles that reads a field after the self call) prints `123` natively
  and through lean2rr: Lean's own code reads the field before the call.
  No lean2rr program that reaches the bug was found; it is not excluded.
- Related, and fixed by upstream's #984 itself, not by this patch: on
  `l2r-base12` TRMC moved a self call past every operation, also past
  another call. A Lean function that applies a traced closure after its
  self call printed its traces in the wrong order through lean2rr
  (`g0 g1 g2` for native `g2 g1 g0`). On `36a55a0f` the order is
  native's (lean2rr's test `RtTrmcCallOrder`).

## Patch

[`patches/26-a-trmc-observable-release.patch`](patches/26-a-trmc-observable-release.patch),
`[trmc] keep a self call in place across a release with an observable
cleanup` (6 files, +283/-13; without `tests/`, +83/-13).

- `hasObservableCleanup(type)` looks through rc, ref, nullable, cell and
  array types. For a record it asks upstream's
  `RecordType::hasObservableCleanup()` first and, when that says yes,
  the record's members. A foreign object, a closure, a locked cell, a
  device array, a null type and an incomplete record are observable. An
  rcgmp integer and a token are not.
- `runsObservableCleanup(op)` walks an operation and its regions. Every
  nested operation that is neither read-only (`leavesCountsAlone`,
  upstream's shared predicate) nor count bookkeeping (`isCountBookkeeping`,
  the pass's own list of count, token and allocation operations) is
  tested by the types of its operands. So the list names the operations
  that do not release, and a new operation is tested by default:
  `rc.dec`, `ref.drop`, a call of drop glue, and the drop callbacks
  (`drop.run`, `drop.defer`, `drop.join`, `drop.defer_indexed`,
  `rc.defer`).
- `canPrecedeSelfCall` refuses an operation for which that holds. The
  self call then stays, and its leaf takes the apply fallback.

**Tests.** `conversion/trmc_reordering.mlir`: a foreign object released
after the self call, and a record that holds one, released through
`reussir.drop.run`; FileCheck fails on pristine upstream (it emits the
`.trmc` helper) and passes with the patch.
`conversion/trmc_reordering_rcgmp.mlir`: a record of an integer still
gets its helper (a guard against a rule that is too wide).
`frontend/trmc_cleanup_order.rr` with a C driver: the repro above and
the closure shape; on pristine upstream it stops at an assertion at
`-O none` and `-O aggressive`, with the patch it exits 0.

## Review

Two rounds by an independent reviewer (local notes `port13/reviews/RV4`).

- Round 1 found the first version incomplete: a value with a worklist
  drop is released by `reussir.drop.run`, which is no call operation, so
  two of the reviewer's 14 handle shapes still gave 0. It also found the
  rule too wide: a record that holds only an integer counted as
  observable and lost its helper. Both are fixed in the patch.
- Round 2: approved, no new finding. The reviewer read every operation
  that the rule leaves out and found none that can run a cleanup. All 14
  handle shapes give 3 at the three levels.
- Limits that stay: a closure that captured nothing foreign also keeps
  the call in place; a release hidden behind an operand of a plain type
  would not be seen (no such operation exists today).
- Not run: the full lit suite, clang-tidy, the sanitizer tests.
  The patch's changed lines are clean under clang-format 23.1.0 (LLVM
  style) since 2026-11-19; the formatter moved line breaks in 13
  lines and changed no token.

## Measured claim

What the patch costs: TRMC helpers that it removes. Measured as counts,
not as time (no wall time was measured).

| Set | Helpers, pristine / patched | Helper calls | Lowered MLIR |
|---|---|---|---|
| upstream's benchmark suite (31 programs) with core and std, `-O aggressive --reuse-across-call` | 18 / 18 | 114 / 114 | byte-identical, 33 of 33 units |
| 19 lean2rr programs, the port's base without and with 26-a and 27-a | 7 / 7 | 40 / 40 | byte-identical, 19 of 19 |
| the same 19 programs on the final series | 7 / 7, the same names | 40 | - |
| the reviewer's 12 TRMC functions that release plain values or values with integers | 12 / 11 | - | the one lost holds a closure, by design |

So: no helper is lost on the measured programs. A function changes only
when an operation between a self call and its constructor can release a
value whose type reaches a foreign object, a closure, a locked cell or a
device array. That function goes from a wrong order to plain recursion.

## Upstream note

Not reported. A report would give the repro: three levels of
`build`, the count of open handles at the leaf, 0 for 3. The fix is the
completion of #984's rule for releases, with upstream's own predicate
for an observable cleanup.
