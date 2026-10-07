# 14. `fuseArm` loses a count when a bound member is consumed before the scrutinee's release

## Summary

**Kind:** bug. **Status:** patched (by 09-a, the patch of
[bug 9](09-duplicate-bound-member.md)), applied in `./reussir` (`l2r-local` cc8e5aa5).

**Upstream:** pull request #653 (open), with 09-a, the patch of entry 9.

`RcDispatchFusion`'s `fuseArm` fuses a match arm's member retains into the
release of the scrutinee (a "destructuring" release that transfers the
cell's reference to each member). It keeps scanning past a use that
consumes a bound member, such as storing it in a new cell that is released
again before the scrutinee. The retain's reference is then already gone
when the release transfers it: the member is freed while still in use (use
after free). Found by review round 2 (finding R2-2, also generator seed
5077) in unpatched code, while checking the first version of 09-a.

## Symptom and repro

Repro [`repros/bug14-member-consumed-before-release.rr`](repros/bug14-member-consumed-before-release.rr):

```
fn f(x : T) -> T {
    match x {
        T::N(a, l, r) => { let y : T = { let z : T = T::N { a, l, T::L{} }; x }; T::L{} },
        T::L => x
    }
}
```

`go` builds a tree `t`, calls `f(t)` and then reads `t` (so `x` is shared),
1000 times, and prints how many checksums are wrong.

**Command.** `rrc bug14-member-consumed-before-release.rr` with lean2rr's
flags.

**Expected.** `0`.

**Actual on ef922049.** A crash at every `-O` level: SIGSEGV, or SIGABRT
from a stack overflow (a freed cell forms a cycle). ASan reports a heap use
after free. `run.sh` printed
`issue 14   REPRODUCES  use after free: SIGABRT (overflowed its stack), expected 0`.

## Cause

`RcDispatchFusion`'s `fuseArm`
(`lib/Transformation/RcDispatchFusion/RcDispatchFusion.cpp`; its scan is
shown under [bug 9](09-duplicate-bound-member.md#cause)) fuses a match
arm's member retains into the release of the scrutinee and keeps scanning
past a use that consumes a bound member: it accepts any op that has no
regions and does not touch the scrutinee. Here `l` is stored in `z`, which
is released again before `x`. With `x` shared, `z`'s release drops `l`'s
count below its holders; the fused decrement's shared path then reloads
`l` from `x`'s cell and retains it.

`f`'s arm before fusion, dumped from `rrc -t mlir -O none` plus the passes
before `RcDispatchFusion` (types shortened):

```
%5 = reussir.ref.load (project %arg1 [1])      // l
reussir.rc.inc(%5)
%7 = reussir.record.compound(%3, %5, %6)       // z = T::N{a, l, L}: consumes l
%10 = reussir.rc.create value(...)
reussir.rc.dec(%10)                             // release z
reussir.rc.dec(%arg0)                           // release x
```

The unpatched pass erases the retain and stamps `boundMembers = [1]`. Here
`x` is shared (`t` is read after the call), and `l`'s count is 1, held by
`x`'s cell. `z` takes `l` without a reference of its own. Releasing `z`
releases `l`: count 0, freed, while `x` still points to it. Then the
release of `x` takes the shared path, which re-loads `l` from `x`'s cell
and retains the freed cell. The fused retain stood for a reference that
`z` had already given away.

## lean2rr

lean2rr can reach the shape through Reussir's inliner (a callee that drops
a constructed argument; see [bug 9](09-duplicate-bound-member.md#lean2rr));
not seen in the corpus or test suites.

## Patch

Fixed by 09-a, the patch of [bug 9](09-duplicate-bound-member.md#patch)
(its second hunk, in the revision after review round 2): no fusion when an
op before the release uses a bound member other than by a borrow or a
retain (`consumesFusedMember`, which 09-a adds; before 2026-10-07 the
parked 07-a added it). 07-a had the same flaw in its own scan, found in
review (R2-1), and was fixed the same way
([issue 7](07-phantom-reuse-donor.md#patch)).

The round-2 stack, which has the first 09-a (duplicate rule only), still
crashes; with the revised 07-a/09-a: FIXED (`0`). `run.sh` on the patched
build: `issue 14   FIXED       prints 0 (no wrong result in 1000 runs)   [lean2rr's flags]`.
