# 27. `core::object::is_unique` can answer true for a nullary immediate under TBI

**Kind:** bug (a wrong result). On aarch64 with the top-byte encoding of
nullary variants (TBI), a nullary constructor is a tagged pointer to a
static dummy box that all values of that constructor share. Its
retains count on the dummy's 32-bit count. After 2^32 - 1 retains the
count reads 1, and the uniqueness test answers true for a value that is
no box at all. Patch 27-a makes the test answer false for an immediate.

## Summary

**Kind:** bug, low severity. **Status:** patched (27-a), in the series
on upstream `36a55a0f` (Reussir branch `l2r-base13-r7`, tree `6dc99546`; the patch
is the file `patches/27-a-is-unique-tbi-immediate.patch`). It does not affect lean2rr: lean2rr's prelude and generated
code do not call `core::object::is_unique`. `scripts/l2r.py` does not
check for the patch.

**Upstream (2026-11-18):** Open at `36a55a0f`. New with #983,
which added the intrinsic; `l2r-base12` has no such
function. aarch64 with TBI only: on x86-64, and with
`--nullary-variant-encoding arch-independent`, the answer is always
false. Not reported: the maintainer takes fixes from this directory.
The patch applies to a clean `36a55a0f` alone.

## Context

- **Nullary immediates.** A nullary constructor (`Nil`, `None`) of a
  shared enum is not allocated. Under TBI its handle is the address of a
  static dummy box, one for each tag number, with the tag + 1 in the top
  byte. The hardware ignores the top byte, so code that retains such a
  handle updates the dummy's count.
- **`core::object::is_unique`** (#983) says whether a value has one
  reference. Its purpose: true means that nobody else can observe a
  write through the value. It lowers to `reussir.rc.is_unique`, a read
  of the count.
- The decrement expansion has its own test for an immediate
  (`rc.is_immediate`) before it frees. The uniqueness test has none.

## Symptom and repro

Repro [`repros/bug27-is-unique-immediate.rr`](repros/bug27-is-unique-immediate.rr)
with its C driver: `enum E { A, B(u64) }`, retains with
`core::object::unsafe_inc` in a tail-recursive loop (a few seconds).
`-O default`, pristine `36a55a0f`, aarch64:

```
is_unique(E::A) = 0
is_unique(E::B{1}) = 1
is_unique(E::A) after 1 retain = 0
is_unique(E::A) after 2^32-2 retains in total = 0
is_unique(E::A) after 2^32-1 retains in total = 1     <- wrong
is_unique(E::A) after 2^32 retains in total = 0
```

With 27-a the marked line reads 0.

## Cause

The comment at the lowering says it
(`lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp:128` at
`36a55a0f`): under TBI `rc.is_unique` can "answer true for a wrapped
dummy; no pass emits it for a type with immediates". That is no longer
true: since #983 a program can ask, and the borrow specialization emits
the test for an argument at its last use
(`lib/Transformation/BorrowSpecialization/BorrowSpecialization.cpp:210`).

Severity is low. The wrong answer needs 2^32 - 1 more references to one
nullary value than releases: an `unsafe_inc` loop, or more than 32 GiB
of live references. No construct of the language writes in place
through an enum value, so the result is one wrong boolean. The
compiler's own test in a borrow entry is harmless: it only selects the
owned or the borrowed copy of a callee, and both are correct for an
immediate.

## lean2rr

Not reached. lean2rr does not emit the intrinsic. leanrt's own sharing
test for a record (`is_shared_record`) reads the handle's top byte
first and answers "not shared" for an immediate.

## Patch

[`patches/27-a-is-unique-tbi-immediate.patch`](patches/27-a-is-unique-tbi-immediate.patch),
`[codegen] answer false to a uniqueness test of an immediate under TBI`
(3 files, +44/-2; without `tests/`, +29/-2).

In the special-pointer-tag pass
(`lib/Transformation/SpecialPointerTag/SpecialPointerTag.cpp`), under
TBI, after the rewrite of nullary constructors: each `rc.is_unique`
that is in the module at that point, and whose type can carry a tag,
becomes `is_unique & !rc.is_immediate`. These are the three operations
that the decrement expansion uses. The pass runs before the borrow
specialization, so only the tests that the program wrote get the guard.
The comment in `BasicOpsLowering.cpp` is corrected.

**Tests.** `conversion/special_pointer_tag.mlir` has a new function
`@is_unique`: the guard under TBI, none under the immortal encoding.
FileCheck fails on pristine upstream and passes with the patch.

## Review

Approved in both rounds by an independent reviewer (local notes
`port13/reviews/RV4`); the code did not change between them, only the
subject's scope (`[codegen]`, the scope of upstream's TBI commits). The
reviewer ran the repro on pristine upstream (1 after 2^32 - 1 retains)
and on the patch (0).

Limits that stay:

- The guard covers the tests that exist when the pass runs. A pass that
  adds `rc.is_unique` on such a type later must be sound for a true
  answer on an immediate (today only the borrow entry, which is).
- A guarded test is `and(is_unique, ...)`, so a pattern that looks for a
  bare `rc.is_unique` condition (dispatch fusion, inc/dec cancellation)
  does not match it. This holds only for such a type under TBI.
- The 2^32 loop is not a lit test (seconds of run time).

## Measured claim

What the patch costs: nothing for a program that does not call the
intrinsic on an enum with a nullary constructor. Measured, pristine
`36a55a0f` against the patched compiler (26-a and 27-a together),
`-O aggressive --reuse-across-call`: the lowered MLIR of upstream's
benchmark suite (31 programs), core and std is byte-identical, 33 of 33
units; the same for 19 lean2rr programs. A guarded call costs one test
of the top byte. No wall time was measured.

A first version put the test in the LLVM lowering of every
`rc.is_unique`. It changed code that no program asked for (the borrow
entries): 3 of the 33 units differed (optimized IR lines: heap-functional
606 to 658, mltt 24681 to 24687, std 87720 to 88118). That version was
dropped for this reason.

## Upstream note

Not reported. A report would give the six output lines above. Upstream
tried full constructor tagging inside #980 and took it out again; the
maintainer wrote there that he may remove TBI. If TBI goes, the bug
goes with it.
