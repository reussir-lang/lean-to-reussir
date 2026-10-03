# 26. An assume after the reuse launder lets LLVM fold a rebuilt cell

## Summary

**Kind:** bug (miscompile). **Status:** patched (0021), applied in
`./reussir` (`l2r-local` cc8e5aa5).

**Verdict: bug.** When a unique cell is reused for a new record, Reussir
launders the cell's pointer (`llvm.launder.invariant.group`) so that LLVM
does not take the new record's fields for the old one's, and then tells
LLVM, with `llvm.assume(launder(p) == p)`, that the laundered pointer equals
the old one. LLVM uses that equality to put the new record's stores back on
the old pointer, which undoes the launder: the cell's tag and fields look
constant. In a loop that rebuilds one cell in place, the result is wrong at
`-O aggressive`. lean2rr's output hits it: a Lean program of this shape
prints `2` instead of `25009648` through lean2rr.

## Symptom and repro

Repro [`repros/bug26-launder-assume.rr`](repros/bug26-launder-assume.rr):

```
enum S { A(u8, u16), B(bool), C(u64) }
fn step(x : S, s : u64) -> S {
    match x {
        S::A(a, b) => { S::B{s % 2 == 1} },
        S::B(f) => { S::A{(s % 251) as u8, (s % 65521) as u16} },
        S::C(w) => { S::C{w + s} }
    }
}
fn iter(x : S, n : u64, s : u64) -> S {
    if n == 0 { x } else { iter(step(x, s), n - 1, (s * 33 + 10) % 1000003) }
}
fn sum(x : S) -> u64 { ... }      // A(a, b) => a * 100000 + b; B(f) => 1 or 2
#[main]
fn main() { say(sum(iter(S::A{1, 2}, 6, 153))); }
```

`iter` rebuilds one `S` cell six times in place (`A` → `B` → `A` ...);
the result is `A{250, 9648}`.

**Command.** `rrc bug26-launder-assume.rr -O aggressive`.

**Expected.** Prints `25009648`.

**Actual on ef922049** (here 91da4f80): prints `2` (`B(false)`) at `-O
aggressive`, with or without lean2rr's flags; `25009648` at `-O none` and
`-O default`. With
an opaque seed instead of the constant 153, LLVM does not reach the wrong
fold on this program. `run.sh` prints `bug 26   REPRODUCES  prints 2,
expected 25009648`.

Through lean2rr (`morepatches-a/launder-bug/lean-bool-loop.lean`, the same
program in Lean, and `lean-uint8-loop.lean` with a `UInt8` field instead of
the `Bool`): native Lean prints `25009648`; lean2rr with Reussir 91da4f80
(or with 0018-0020) prints `2`; with 0021, `25009648`. Small variations
(`morepatches-a/launder-bug/`, five programs) fail under `-O aggressive`
in the packed and the declaration-order layouts and under lean2rr's flags;
one is right on 91da4f80 by luck and wrong once 0018-0020 change its layout.

Found by differential fuzzing of the patches for bugs 1, 2 and 8 (random
record and enum shapes against a reference evaluator; agent A,
`morepatches-a/`). The LLVM IR rrc hands to LLVM is right under `clang -O0`
and `-O1` and wrong after the O2/O3 pipeline; deleting the icmp/assume
pairs from it made it, and five fuzzer programs that failed the same way,
right.

## Cause

`!invariant.group` metadata on a load or store tells LLVM that every access
with that metadata through "the same pointer" sees the same value. Reussir
puts it on the stores of a new record's tag and fields (`rc.create`) and on
the loads of a compound's fields. When a cell is reused, its token is
laundered first (`token.launder`, lowered to `llvm.launder.invariant.group`,
`ReussirTokenLaunderOpConversionPattern` in
`lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp`; `token.realloc`
launders its result the same way, `ReussirTokenReallocConversionPattern`):
the launder returns a pointer that aliases the cell but counts as a
different pointer for `invariant.group`, so the old and the new record are
two objects to LLVM.

Both lowerings then emitted, deliberately (a long comment explained it as
recovering alias and value propagation after the launder):

```c++
auto ptrEq = mlir::LLVM::ICmpOp::create(rewriter, op.getLoc(),
                                        mlir::LLVM::ICmpPredicate::eq,
                                        newSSA, adaptor.getToken());
mlir::LLVM::AssumeOp::create(rewriter, op.getLoc(), ptrEq);
```

GVN and EarlyCSE replace a value by another they know to be equal, and the
assume says the laundered pointer equals the old one. On one repro, GVN
alone moved four `!invariant.group` stores back onto the old pointer. The
new record's stores and the old record's loads and stores then share one
pointer and one invariant group, which says that the cell's tag and fields
never change. In the loop that rebuilds the cell, LICM hoisted the tag
stores out of the loop (`opt -opt-bisect-limit` lands on LICM in all three
cases bisected), and the result was a wrong value, or the computation
folded to a constant.

## lean2rr

lean2rr's output is affected: in-place reuse is how it runs Lean's
reset/reuse (`--reuse-across-call`), its IR has these launders (9, 62 and
112 in three programs), and the Lean repro above prints a wrong result. A
loop that rebuilds a small enum cell in place (`Bool`, `UInt8`, `UInt16`
fields) is enough. No lean2rr workaround.

## Patch

Patch file
[`patches/0021-l2r-local-bug-26-no-llvm.assume-launder-p-p-after-an.patch`](patches/0021-l2r-local-bug-26-no-llvm.assume-launder-p-p-after-an.patch)
(`l2r-local` commit `9a171995`; applied in `./reussir`, `l2r-local`
cc8e5aa5). No assume after the launder, in both lowerings:

```c++
   mlir::Value laundered =
       mlir::LLVM::LaunderInvariantGroupOp::create(rewriter, loc, reallocated);
-  mlir::Value ptrEq = mlir::LLVM::ICmpOp::create(
-      rewriter, loc, mlir::LLVM::ICmpPredicate::eq, laundered, reallocated);
-  mlir::LLVM::AssumeOp::create(rewriter, loc, ptrEq);
   rewriter.replaceOp(op, laundered);
```

and in the `token.launder` lowering the same, the old comment replaced by
one that says why no assume may follow the launder.

**Why it is correct.** The launder alone is what `invariant.group` asks for
when an object is replaced in the same memory (LLVM's LangRef). The assume
only added the equality, and that equality is what let LLVM merge the two
objects. Dropping it loses no needed fact: LLVM's basic alias analysis sees
through the launder (`getArgumentAliasingToReturnedPointer`), so the
laundered pointer still must-aliases the cell and ordinary store-to-load
forwarding stays. What is lost is GVN rewriting the laundered pointer to the
old one, which only enabled removing stores of unchanged fields
(RcCreateFusion's copy avoidance, `skipFields`, already does that) and the
unsound folds.

**Verification.**

- New test `tests/integration/frontend/reuse_launder_loop` (the repro's
  program with a C driver). `token_ops.mlir` and
  `rc_create_fused_lowering.mlir` checked for the assume; they now check
  that none follows the launder.
- `run.sh`: `bug 26   FIXED       prints 25009648   [-O aggressive]`.

**Review.** Review rv8/reussir (patches 0018-0021, 0027, 0040): no
correctness defect.

- Every launder, `invariant.group` and assume in `lib/` was checked: two
  launders remain (`token.launder`, `token.realloc`); the remaining assumes
  (tag < number of arms, count >= 1, count == 1 for `rc.assume_unique`)
  relate no two pointers; no `returned` attributes.
- Removing the assume loses nothing needed (the alias-analysis argument
  above). On lean2rr's IR the number of assumes drops by exactly the number
  of launders (9, 62, 112); static load and store counts are essentially
  unchanged.
- A struct cell, a two-arm enum and the repro's enum rebuilt in place in
  loops: right at every level and with lean2rr's flags (without 0021 the
  repro's case prints 2). The Lean repros through lean2rr print 25009648.
- The pending-stack frees (0013-0015) never reuse tokens in drop glue, so
  they have no launders.

**Effect on lean2rr.** Fixes wrong results in programs that rebuild a cell
in place in a loop. Generated code otherwise loses one assume per launder.

## Upstream note

`BasicOpsLowering.cpp`: the `token.launder` and `token.realloc` lowerings
emit `llvm.assume(icmp eq (launder p), p)` after
`llvm.launder.invariant.group`. GVN uses the equality to replace the
laundered pointer by `p`, merging the old and the new record's
`!invariant.group` accesses, and LICM then hoists the tag stores of a cell
rebuilt in place out of the loop: wrong results at -O2/-O3 (the repro above
prints 2 instead of 25009648). Fix: no assume after the launder.
