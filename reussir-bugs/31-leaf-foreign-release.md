# 31. A record without counted members that foreign code releases enters a destruction scope

**Kind:** cost (run time). Not a bug: the program is correct. When Rust
code (a texture, or a runtime library) releases the last reference to a
Reussir record, the release goes through the runtime's destruction
scope, also when the record holds only scalars and so has nothing to
release inside. Patch 31-a lets such a release free the box directly.
It is an optimization.

## Summary

**Kind:** cost. **Status:** patched (31-a), patch 10 of the series on
upstream `36a55a0f` (Reussir branch `l2r-base13-r4`, commit
`bebee388`; 168 added lines, 7 of them code, the rest tests).
`scripts/l2r.py` does not check for the patch: without it the programs
are the same and one kind of release is slower.

**Upstream (2026-11-18):** Open at `36a55a0f`: new with upstream's drop
series of 2026-11-01 (#924 added the count test of the bridge). On
`l2r-base12` the same release was a direct free. Not reported: the
maintainer takes changes from this directory. The patch applies to a
clean `36a55a0f` alone.

## Context

- **A foreign release.** A Reussir record can be held by Rust code
  (lean2rr's typed arrays hold records as `Bridge<T>`). For each such
  record type rrc makes a release function, `<T>_ffi_release`, which the
  Rust side calls when it drops a reference.
- **The bridge.** Upstream's worklist drops wrap every such function
  (`prepareWorklistDropBridges`,
  `lib/Conversion/AcquireDropExpansion/WorklistDrop.cpp`): the body
  moves to `<name>.worklist.<order>`; for a reference that is not the
  last, the function calls the body; for the last one it calls
  `__reussir_drop_join_or_run(object, body)`. That runtime function
  (`crates/reussir-rt/src/drop_stack.rs:355`) tests a thread-local
  flag and, outside a running free, sets up a scope, calls the body
  through a pointer, drains the work list and takes the list of
  scope-exit callbacks.
- The scope is there for the work that the body can put on the work
  list: the record's dead children. A record of scalars has none.

## Symptom

One case of the shared benchmark set, X10 n_body: 22.9 ms on
`l2r-base12`, 34.3 ms on the port's first final series (1.562; timing
run 20). The `.rr` is identical on both sides.

n_body keeps its bodies as a record of floats (64 bytes) in an array,
and every `Array.set` drops the old element. The floating-point code is
the same machine code on both bases (the 270 instructions around the
square root differ in two register names and one cold call). The
difference is in the drop of the old element:

```
l2r-base12                                 the series before 31-a
   ldr  w8, [x0]                              ldr  w8, [x0]
   subs w8, w8, #1                            subs w8, w8, #1
   b.ne  store                                b.ne  store
   mov  w1, #8                                adrp x1, ...     ; the release's worker
   mov  w2, #64                               add  x1, x1, ...
   b    __reussir_deallocate                  b    __reussir_drop_join_or_run
```

## Cause

`prepareWorklistDropBridges` wraps every function with the
`reussir.foreign_drop` attribute. The same function already leaves out
closure drops whose payloads are trivially copyable; foreign drops had
no such rule. So the last release of a record of scalars from Rust code
pays one runtime entry: a thread-local test, a scope and an indirect
call, for a body that only frees a box.

## lean2rr

lean2rr reaches it where a record of scalars is an element of a typed
array or lives in another runtime container. Of the 53 benchmark cases
one shows it in time (X10). In two programs that were compared
statically, one release function each changes (X10: the record `Body`;
the regex engine: one record); 17 runtime tests that were compared have
no such record.

## Patch

[`patches/31-a-leaf-foreign-release.patch`](patches/31-a-leaf-foreign-release.patch),
`[drop] release a foreign box of trivially copyable members in place`.

In `prepareWorklistDropBridges`, a `reussir.foreign_drop` function whose
argument is a shared box that is not regional, and whose payload is
trivially copyable, keeps its body and only loses the attribute. The
predicate is upstream's own (`isTriviallyCopyable`): the worklist glue
frees such a box at once in every other place, and the closure rule
three lines above uses the same test.

**Why the behaviour is the same.** The bridge is not what makes a
foreign drop correct; it only lets the body put work into a scope that
runs. Inside a running free the bridge called the body directly.
Outside one it opened a scope around a body that queues nothing,
drained an empty list and found no scope-exit callback (callbacks are
queued only inside a scope). The free happens at the same point in both
forms. A payload with a managed member (another box, a foreign object,
also a tagged one, a big integer, a token) and a regional box keep the
bridge.

**Tests.** `conversion/worklist_drop_bridges_leaf.mlir`: a record of
scalars, a record of value records, a variant of them and an atomic box
keep their bodies under both drop orders; a record with a link to
another box, one with a foreign object and a rigid box get the bridge.
It fails on pristine upstream. `frontend/ffi_leaf_release_e2e.rr`: a
Rust `Vec` of such records and of an enum with nullary arms; the
program runs under both drop orders.

## Review

Accepted by an independent reviewer (local notes `port13/reviews/RV1`,
the section on 31-a). The reviewer could not break it: for every kind
of payload that the frontend can send across the boundary (twelve kinds:
records of scalars, of value records, with a `bool`, a `str`, a
pointer; enums with nullary and payload arms; records that hold a box,
an enum, a cell), pushed into a Rust `Vec`, cloned and dropped by Rust
code, the output, the allocations, the frees and the set of live boxes
are equal on pristine upstream and with the patch, at two optimization
levels and under both drop orders.

Findings, all low:

- With 31-a, `reussir-opt` run by hand crashes on one input that
  pristine accepts: a `foreign_drop` function with an `rc.dec` that has
  no token, given to the decrement expansion before the token pass. The
  cause is an upstream bug, [entry 33](33-tokenless-rc-dec-expansion.md);
  before 31-a the bridge hid it. rrc is not affected (it runs the token
  pass first).
- The rule tests the argument's type, where the property belongs to the
  body. The frontend's only producer of such a function emits exactly
  "decrement, return", and upstream's closure rule is by type in the
  same way.
- A doubt of the author was checked and is **not** a bug: the bridge's
  fast path reads the count before it tests for an immediate. Under
  TBI an immediate is a real address of a static dummy box, so the read
  is valid by design.

Not checked: x86 by a run; SIMD members by a run.

## Measured claim

**Wall time** (timing run 21, 2026-11-18: the series with 31-a and 32-a
against the series before them; direct pairs, median of 9 and min, the
two sides in turn; 53 cases; the `.rr` byte-identical on both sides):

| Case | before | with 31-a and 32-a | ratio (median) | (min) |
|---|---:|---:|---:|---:|
| X10 n_body | 34.4 ms | 22.9 ms | 0.642 | 0.665 |

X10 is 31-a's case: 31-a's prototype alone, in a timing step of its
own, gave 34.2 ms to 22.8 ms (ratio 0.667 median, 0.665 min) with 19
other cases between 0.984 and 1.008. X10
against `l2r-base12`: 1.56 in run 20, about 1.00 now (derived: this
run's ratio times run 20's). Against native: 1.22 to 0.78.

**31-a alone** (timing run 22, 2026-11-18: the series of 12 patches
with 31-a against the same without it; direct pairs, median of 9 and
min; the 9 cases whose object the patch changes and 2 controls):

| Case | without | with 31-a | ratio |
|---|---:|---:|---:|
| X10 n_body | 34.3 ms | 23.1 ms | 0.642 (by the kernel's time; 0.671 median and 0.664 min by wall time) |
| the 10 others | | | 0.970 to 1.002 |

So 31-a alone gives the gain on n_body, and nothing else moves
measurably. One case is at the edge of the band: Cedar's first
case, 0.970 (median and min agree; a small real gain is likely).
The final form gives the two changed functions of n_body the same
eight instructions as the prototype (checked by the author and by the
reviewer).

**Static:** in X10 one of 7 foreign release functions keeps its body,
and 4 functions differ (that release and the three runtime functions
that inline it); `.text` of X10 falls by about 8 kB. Upstream's
benchmark suite, core and std (33 units, lowered MLIR): 1 differs
(`std`: the release of `Option<u32>` keeps its body), 32 are
byte-identical.

**Through lean2rr:** 8 release-order and memory tests of the runtime
suite pass on the series with 31-a; the gate on the series with all 15
patches passes (748 of 750, 2 expected failures).

**Not measured:** the number of records that n_body drops; a wider rule (a payload whose
members release without a scope, such as strings or big integers).

**Repro.** [`repros/bug31-leaf-foreign-release.mlir`](repros/bug31-leaf-foreign-release.mlir) shows the static difference through `reussir-opt`: the foreign release of a leaf record has a `drop.join` (REPRODUCES) or frees the box directly (FIXED). In the gate on the series of 16 patches (2026-11-18): REPRODUCES on pristine `36a55a0f`, FIXED on the series.

## Upstream note

Not reported. A report would give the two instruction listings above
and the pair of X10. The fix is seven lines next to upstream's closure
rule, with upstream's own predicate.
