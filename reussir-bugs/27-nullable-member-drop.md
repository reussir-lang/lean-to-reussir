# 27. Releasing a chain linked through `Nullable` recurses once per link

## Summary

**Kind:** missing feature (the bounded-depth frees of
[bug 13](13-long-list-drop.md) did not cover `Nullable` links). **Status:**
patched (0027), applied in `./reussir` (`l2r-local` cc8e5aa5); does not
affect lean2rr (it does not use `Nullable`).

**Verdict: a gap in bug 13's patches, not caused by them.** With patches
0013-0015, drop glue releases a member box of a shared record through the
thread's pending stack, so a long chain is freed in a loop. A member of type
`Nullable<shared record>` was released by a plain decrement, which recurses
into the next link's glue: a chain linked through `Nullable` takes a stack
frame (or more) per link and overflows at a million links. Reussir without
the local patches recurses for every chain ([bug 13](13-long-list-drop.md)),
so the baseline crashes too. Found by the review of agent B's patches
(rv7/p22, round 2, finding RV7P-05).

## Symptom and repro

Repro [`repros/bug27-nullable-member-drop.rr`](repros/bug27-nullable-member-drop.rr):

```
struct [shared] S(u64)
struct [value] A { b: Nullable<B>, s: S, n: u64 }
struct B { a: A, k: u64 }
fn build(n : u64, acc : Nullable<B>) -> Nullable<B> {
    if n == 0 { acc } else {
        build(n - 1, Nullable::NonNull{B { a: A { b: acc, s: S{n}, n: n * 2 }, k: n }})
    }
}
fn first_k(l : Nullable<B>) -> u64 {
    match l { Nullable::NonNull(x) => x.k, Nullable::Null => 0 }
}
#[main]
fn main() { say(first_k(build(links(), Nullable::Null))); }   // links() = 1000000
```

A chain of a million `B` cells, each linking to the next through the
`Nullable` inside its `[value]` member `A`, is read at its head and then
released.

**Command.** `rrc bug27-nullable-member-drop.rr -O default`, run with an
8 MB stack.

**Expected.** Prints `1`.

**Actual on ef922049 with 0013-0015** (91da4f80): the program aborts,
"thread 'main' has overflowed its stack" (SIGABRT; gdb shows
`drop_in_place::<A>` recursing), at `-O default`, `-O aggressive` and with
lean2rr's flags. The same chain linked through a plain shared enum
(`enum C { End, Link(A, u64) }`) frees 3,000,000 links. A chain of
`Nullable` links held in a `Cell` crashes the same way. `run.sh` prints
`bug 27   REPRODUCES  1M links through Nullable, 8 MB stack: overflowed
its stack (SIGABRT)`.

## Cause

`AcquireDropExpansion` (`lib/Conversion/AcquireDropExpansion/AcquireDropExpansion.cpp`)
expands each `ref.drop` in drop glue. For a plain shared record member,
`rewriteDropRc` releases the box through `emitDeferredRelease` when it is
inside drop glue (`kDropGlueAttr`) and the box is deferrable: when the
count is 1 the box goes onto the thread's pending stack (patch 0014), and
the outermost glue drains the stack in a loop. `rewriteDropNullable`, the
pattern for a `Nullable` member, dispatches on null and, in the non-null
arm, always emitted a plain `rc.dec`. Its expansion calls the box's drop
glue directly, which releases the next link the same way: one level of
native recursion per link.

## lean2rr

Not affected: lean2rr does not use `Nullable` (its optional values are
enums), and the LLVM IR of 30 lean2rr programs is the same with and without
the patch. No workaround needed.

## Patch

Patch file
[`patches/0027-l2r-local-bug-27-defer-a-nullable-member-s-release-i.patch`](patches/0027-l2r-local-bug-27-defer-a-nullable-member-s-release-i.patch)
(`l2r-local` commit `9ea68905`, the version amended after review finding
RV8R-01; applied in `./reussir`, `l2r-local` cc8e5aa5). Two changes in
`AcquireDropExpansion.cpp`:

1. `rewriteDropNullable`, non-null arm: inside drop glue, release the
   unwrapped box like `rewriteDropRc` does, under the same condition:

   ```c++
   +      if (auto func = op->getParentOfType<mlir::func::FuncOp>();
   +          func && func->hasAttr(kDropGlueAttr) && isDeferrable(rcType)) {
   +        emitDeferredRelease(rewriter, op.getLoc(),
   +                            op->getParentOfType<mlir::ModuleOp>(),
   +                            nonNullBlock->getArgument(0));
   +        ReussirScfYieldOp::create(rewriter, op.getLoc(), nullptr);
   +        rewriter.eraseOp(op);
   +        return mlir::success();
   +      }
   ```

2. `emitCellRelease` (`drop_and_free`, which frees a cell whose count was
   1): it defers every member box but the last non-leaf one, frees the
   cell, then releases that last box directly (a tail call when its count is
   1, so a chain is a loop). It now also lets a `Nullable` member whose box
   is a non-leaf record fill that last slot: loaded before the free, then
   null-checked (`nullable.dispatch`) and released by `emitLastRelease`
   after it. Without this, a record `{ s: S, b: Nullable<B> }` released `S`
   before `B`, the opposite of `{ s: S, b: B }` and of the order before the
   first change (RV8R-01), and each `Nullable` link cost a push and a pop
   instead of a tail call.

Outside drop glue nothing changes. As for plain links, the tail call makes
a chain a loop only when LLVM eliminates it: at `-O none` a million links
overflow through a plain shared enum as well as through `Nullable`, with or
without the patch.

**Why it is correct.** The deferral is the one the plain member already
uses, under the identical condition, so a `Nullable` box is released
exactly as a plain one when it is not null: once, through the pending
stack, drained by the outermost glue. A null member has nothing to release.
In `emitCellRelease` the last member's value is read before the cell is
freed and released after, as for a plain last member; the null check only
adds the `Nullable` case.

**Verification.**

- New test `tests/integration/frontend/drop_long_nullable_chain`: two
  million links, a shared record linking to itself through a `Nullable`
  member, the link inside a `[value]` member, and the `[value]` record held
  in a cell and released by `cell::set` (`-O default` and `-O aggressive`;
  all three crash without the patch), and the glue of `{ Os, Nullable<Ob> }`
  checked to defer `Os` and release `Ob` after the free, like that of
  `{ Os, Ob }`. The generated code of Reussir's other frontend tests changes
  only for `cell_e2e` (a `Cell<Nullable<..>>` in a shared record).
- `run.sh`: `bug 27   FIXED       1M links through Nullable, 8 MB stack:
  prints 1   [-O default]`.

**Review.** The gap was found by review rv7/p22, round 2 (RV7P-05,
pre-existing, low: lean2rr does not use `Nullable`). Review rv8/reussir
checked the first version of 0027: the deferral condition is identical to
`rewriteDropRc`'s; `Nullable` of a `[value]` record, a closure, an FFI
object, a `field` member or an atomic rc is handled as before; chains
through `Nullable<shared enum>` with nullary arms (1.5M links) are right.
It found one low-severity defect, RV8R-01: the release order reversal
described in item 2 (memory safety and stack depth unaffected). The
amended 0027 makes the reviewer's suggested fix (a `Nullable` member can
be the last member, released after the free).

**Effect on lean2rr.** None (no `Nullable` in lean2rr's output).

## Upstream note

With bounded-depth frees, drop glue should release a `Nullable<shared
record>` member like a plain one: `rewriteDropNullable`
(`AcquireDropExpansion.cpp`) releases its box with a plain `rc.dec`, so a
chain linked through `Nullable` recurses once per link (a million links
overflow an 8 MB stack). Without bounded-depth frees every chain recurses
(bug 13).
