# 21. An integer member's retain is not cancelled against its record's drop

**Kind:** missed optimization. Not a bug: rrc's output is correct. When
code takes a `[value]` record apart, inc/dec cancellation removes the
retain of each rc member against the member's release in the record's
drop, but keeps both for an rcgmp integer member (`Nat`, `Int`). Patch
21-a cancels them under the same rules.

## Summary

**Kind:** missed optimization. **Status:** patched (21-a), patch 8 of
the series on upstream `36a55a0f` (Reussir branch `l2r-base13-final`,
commit `3db9b817`; 6 files, +418/-2, without `tests/` +16/-2). The
patch was reworked for this base
([below](#21-a-on-36a55a0f-reworked)): its rule is smaller than the one
of `l2r-base12` (commit `5a15f745`; made as `8e9a6293`, `l2r-stepd`
plus 21-a). Measured on this base: fewer instructions, statically and
executed; wall time is pending the timing run.
No workaround in lean2rr.**Upstream (2026-11-18):** Not upstream at `36a55a0f` (source read):
`EquivalenceAnalysis::decideLoadedEquivalent` still needs a load on both
sides, and the counted-word scan stops at `ref.spilled`. The
maintainer's port of lean2rr left 21-a out of the series. Upstream
changed the same pass after `95d9a1c8` (#919, #983), and it has a
borrow analysis now; the pattern is still there with both (measured,
below).

**Upstream, earlier base (history, 2026-10-25):** Not upstream at
00906e38. Prepared as a pull request candidate; not opened.

## 21-a on 36a55a0f (reworked)

The patch of the final series is not the patch of `l2r-base12` moved.
It was moved, reviewed and made smaller in two steps (2026-11-17 and
2026-11-18; local notes `port13/reviews/RV5`).

**Why the old form could not be moved as it was.** The old patch
widened the predicate `leavesCountsAlone` (which operations the scan of
the cancellation may cross). On `95d9a1c8` that function was local to
`IncDecCancellation.cpp`. Upstream moved it to `lib/IR/ReussirOps.cpp`
and uses it in three more passes: the borrow analysis, the borrow
specialization and the TRMC recursion analysis. A wider predicate there
is no memory-safety hole (each caller was read), but it changes what
those passes do: with it, the borrow specialization makes a borrowed
copy of a traversal that ends in a conversion to `Nat`, a function that
it leaves owned today (one repro; nobody measured or reviewed that
change, and 21-a's claim does not need it).

**The rule now.** Two changes, 16 lines of code:

- `EquivalenceAnalysis::decideLoadedEquivalent` (values of the types
  other than ref, rc and nullable) also accepts the same field of the
  same by-value record, read by `record.extract` on one side and through
  the record's spill on the other. rc pointers have this rule already.
- The counted-word scan (`cancelCountedWordRetains`, and only it) also
  passes `reussir.ref.spilled`, which only fills a new stack slot and
  changes no count. `leavesCountsAlone` itself is upstream's, unchanged.

Both parts are needed: with the scan change alone, the optimized IR of
the three programs below is the baseline's. Gone from the old patch:
the rule "an operation that allocates new storage and writes only into
it" (`onlyWritesFreshStorage`), and the stop at
`rcgmp.bridge.mpz.is_unique` (`isRCGMPCountObserver`). The review
counted the cancelled pairs with an instrumented build: every extra
pair crosses only the spill, so the one-line rule cancels the same
pairs as the effect-based rule did (the optimized LLVM IR of the three
programs is byte-identical between the two forms).

**Measured on `36a55a0f`** (aarch64, `-O aggressive`, borrow analysis
on, the flags of `scripts/l2r.py`; the same `.rr` compiled without and
with the patch). L12 is the classic Sieve, L17 Strings, Z01c lean-zip's
compress.

Static, optimized LLVM IR and object ("release slow paths" are calls of
`rcgmp_mpz_free`, one for each release site that stays):

| Program | IR instructions | release slow paths | `.text` bytes | pairs cancelled by the pass |
|---|---|---|---|---|
| L12 | 25,660 to 24,808 (-3.3%) | 123 to 93 | 112,149 to 107,313 (-4.3%) | 49 to 95 |
| L17 | 87,485 to 85,888 (-1.8%) | 616 to 561 | 379,450 to 368,962 (-2.8%) | 124 to 265 |
| Z01c | 407,488 to 368,828 (-9.5%) | 7063 to 5232 | 1,880,872 to 1,651,480 (-12.2%) | 2071 to 4359 |

In Z01c 97 functions change and 5 of them grow (LLVM inlines in another
way). The patch's own test program: 3008 to 2657 lines of assembly, 49
to 35 release slow paths.

Executed instructions (cachegrind, builds without SVE and RCPC, reduced
sizes, identical output):

| Program | without | with | change | the figure on `l2r-base12` (full size) |
|---|---|---|---|---|
| L12, 5·10^6 | 1,863,640,806 | 1,761,003,311 | -5.5% | -9.6% |
| L17, 10^5 | 2,431,295,586 | 2,269,968,300 | -6.6% | -7.8% |
| Z01c | not run | | | -6.0% |

So the gain is smaller than on `l2r-base12` for L12 and still there.
**Wall time: pending the timing run.** Until then, "21-a makes these
programs faster" is a hypothesis that instruction counts support.

On other code: the patch changes nothing in upstream's benchmark suite,
core and std (33 units, lowered MLIR; no by-value record of integers is
taken apart there). In 14 lean2rr programs of the runtime suite, every
difference between the series without and with 21-a is a net removal
(for example `RtCArrKinds` 495,466 to 469,737 instructions, -5.2%); the
other patches of the series change no instruction of those programs.

**Checks** (2026-11-18, aarch64): the conversion and bigint lit subset
with the patch's MLIR test and `frontend/bigint_value_record_members.rr`:
281 pass, 2 unsupported, 1 fails for a missing tool of the build
machine (not the patch). The ASan twin cannot run there. The review
ran its own probes on two builds with 8 option sets and found no
erroneous behaviour.

The rest of this entry describes the patch as it was reviewed on the
earlier bases; where it names the wider scan rule or the `is_unique`
stop, the text above is the current one.

## Context

- **Inc/dec cancellation** (`lib/Transformation/IncDecCancellation/`,
  pass `reussir-inc-dec-cancellation`) removes a retain and a later
  release of the same value when nothing between them can free the
  value or read its count. It runs twice in rrc's pipeline: before the
  first acquire/drop expansion and after it
  (`crates/reussir-backend/src/pipeline.rs`).
- **Counted words.** An rcgmp integer is one word, an immediate or a
  pointer to a counted heap object; `rcgmp.retain` and `rcgmp.release`
  count it. Upstream #801 (`7cb5f58c`) added their cancellation,
  `cancelCountedWordRetains`, next to the one for `rc.inc`.
- **Equivalence analysis** (`lib/Analysis/EquivalenceAnalysis.cpp`)
  answers the pass's alias queries: two values are MustAlias when it
  proves that they hold the same runtime value.

## What Reussir does

A `[value]` record (or a tuple) taken apart: each member is extracted
and retained, then the record is dropped.

```rust
struct [value] T4(Nat, Nat, Nat, Nat)

fn loop2(n : u64, i : u64, a : Nat, b : Nat, c : Nat, d : Nat) -> Nat {
    if i < n {
        let t : T4 = { if i % 3 == 0 { T4{a + 1, b + a, i as Nat, d} } else { T4{a, b, c, d} } };
        let a2 : Nat = t.0;
        let b2 : Nat = t.1;
        let c2 : Nat = t.2;
        let d2 : Nat = t.3;
        loop2(n, i + 1, a2, b2, c2, d2)
    } else { a + b + c + d }
}
```

The first acquire/drop expansion turns the drop of `t` into one release
per member, read back through the record's spill:

```mlir
%a = reussir.record.extract(%t) [0]          rcgmp.retain %a
...                                          (the other three members)
%s = reussir.ref.spilled(%t)
%p = reussir.ref.project(%s) [0]
%f = reussir.ref.load(%p)                    rcgmp.release %f
...                                          (the other three members)
```

With rc members (`struct B(u64)` in place of `Nat`), the second
cancellation run removes all four pairs: the equivalence analysis knows
that `record.extract %t[i]` and the load at `[i]` through
`ref.spilled %t` are the same value (`valueRecordField`, upstream #568,
`85392b88`). With integer members all eight operations stay, for two
reasons:

- `cancelCountedWordRetains` scans from a retain only across retains and
  operations that are pure or only read memory (`leavesCountsAlone`).
  `ref.spilled` allocates its stack slot and writes the value into it,
  so the scan stopped there, before every member release.
- `EquivalenceAnalysis::decideLoadedEquivalent`, the rule for values
  that are not refs, rc pointers or nullables (upstream #800,
  `810849d6`), made two values equal only when both are loads. The
  extract/spill rule applied to rc pointers only, so the retained
  extract and the released load were never MustAlias.

The drop patches of [issue 2](02-native-drop-order.md) do not change
this shape: on the series' base the first expansion releases a by-value
record's integer members in the same way.

## Cost

Every pair costs a retain and a release, each with its immediate test,
in each step of a loop that builds such a record or tuple. lean2rr's
generated code has the shape often: a join point that returns several
values returns them in a tuple (J2), and its caller takes the tuple
apart.

Measured on `l2r-stepd` without and with 21-a:

- The program above and its tuple twin (`let (a2, b2, c2, d2) : (Nat,
  Nat, Nat, Nat) = ...`): after the second cancellation, 6 retains and
  6 releases without the patch, 2 and 2 with it (the four member pairs
  are gone; what is left is the arithmetic's own). At `-O aggressive`,
  384 lines of assembly without the patch and 295 with it, 36
  test-and-branch instructions and 22, 19 calls and 10.
- lean2rr dev `2c4083d9` under `--int-backend rcgmp`, the same `.rr`
  compiled by both, instruction counts (cachegrind, valgrind-ready
  builds without SVE); the program outputs are the same:

| Program | Without 21-a | With 21-a | Change |
|---|---|---|---|
| L12 (`Sieve`, 5·10^7) | 11,739,421,888 | 10,616,815,344 | -9.6% |
| L17 (`Strings`, 10^6) | 17,543,805,819 | 16,169,936,692 | -7.8% |
| Z01c (lean-zip, compress) | 22,910,292,491 | 21,524,991,521 | -6.0% |

On lean2rr's planned base for Phase 2 (upstream's drop design), the same
patch gave -9.2%, -8.9% and -6.3%. Under lean2rr's leanrt backend (then the default) L12
and L17 compile to the same instructions with and without the patch
(disassembly compared, on that base).

## Patch

Patch file
[`patches/21-a-value-record-member-retains.patch`](patches/21-a-value-record-member-retains.patch)
(commit `3db9b817` on `l2r-base13-final`; `5a15f745` on `l2r-base12`, `8e9a6293` on `l2r-base8`). Its
rule: a counted word's retain cancels against the member release of a
record's expanded drop under the rules that hold for an rc member.

- **Equivalence** (`lib/Analysis/EquivalenceAnalysis.cpp`,
  `decideLoadedEquivalent`): the same field of the same by-value record,
  read by extract on one side and through the record's spill on the
  other, is the same value for every type, as it already was for rc
  pointers.
- **The scan** (`lib/Transformation/IncDecCancellation/IncDecCancellation.cpp`,
  `leavesCountsAlone`) also crosses an operation whose only effects other
  than reads are an Allocate and a Write on its own result. That is
  `ref.spilled`, and also `reussir.token.alloc`, `reussir.region.create`,
  `rcgmp.extsi`, `rcgmp.extui`, `rcgmp.fptosi`, `rcgmp.bridge.mpz.promote`
  and `memref.alloc` or `alloca`.
- **A stop.** The scan stops at `rcgmp.bridge.mpz.is_unique`, which it
  crossed before as a read, as the rc scan stops at `rc.is_unique`. No
  pipeline reaches it now (the operation appears only in a glue
  function, inside an `scf.if`); the stop is defensive. A helper
  `isRCGMPCountObserver` (`lib/IR/RCGMPMembers.cpp`, declared in
  `include/Reussir/IR/ReussirOps.h`) names the operation and is false
  in a build without rcgmp.

**Why it is sound.**

- The extract and the load read the same bytes: a spill slot is never
  written after the spill. `reussir.ref.store` needs a reference with
  `field` capability, and a projection of a spill keeps the spill's
  unspecified capability (the verifier of `ref.project`). The rule for rc
  pointers rests on the same fact.
- An operation that only allocates its result and writes into it
  changes no count and no value that existed before it.
- Between the retain and the release nothing frees the word or reads
  its count: the scan still stops at the first release of any word, at
  calls, at operations with regions, and at every operation that writes
  or frees other memory. That includes an rcgmp operation that consumes
  an operand (it has read, write and free effects on the operand),
  `reussir.token.free`, `reussir.ref.drop` and a `reussir.ref.memcpy`
  into a spill. The release must be MustAlias the retained word.
- So the record's reference moves to the extracted value: in between,
  the word's count is one lower but at least 1, since the record holds
  the word until the removed release.

As for rc members, a member extracted out of field order keeps its pair:
the scan meets another member's release first. The equivalence change
reaches only the counted-word cancellation's queries. The other users of
the analysis ask about refs, rc pointers and nullables, or compare loads
with loads.

## Tests

- `conversion/inc_dec_cancellation_counted_word_value_record.mlir`
  (FileCheck after the first acquire/drop expansion and the
  cancellation):
  - nothing is left of a four-member record, a tuple, or a record with a
    trivial member between the integers;
  - with one member extracted, only the other member's release stays;
  - a member used twice keeps one retain;
  - an `rcgmp.extui` between the retain and the drop is crossed;
  - the pair stays when an `rcgmp.addi` of other words or a
    `reussir.token.free` sits between them, when
    `rcgmp.bridge.mpz.is_unique` reads the member's count, when the
    member escapes into a call, when the record escapes into a call,
    when the member is consumed while the record is read again, when
    the dropped record is another one, or when the release is another
    field's.
  The test fails without the patch.
- `frontend/bigint_value_record_members.rr`, with its C driver
  `bigint_value_record_members.c`: the loop with a record and with a
  tuple, a member used twice, a record still used after the extract,
  and a record with `Nat`, `u64` and `Int` members, with heap and
  immediate integers. Each test takes a seed from the C driver (1 and
  2, both branches), so the integers are computed and the records chosen
  at run time and nothing folds to a constant. It runs at the default
  level and at `-O aggressive`.
- `sanitizer/bigint-value-record-members-asan.rr`: the same program
  under ASan (a cancelled retain that was still needed shows as a use
  after free, a lost release as a leak).

On `l2r-stepd` with 21-a, Reussir's lit suite has the results it has
without it, apart from the new tests (763 pass; the 11 that fail also
fail without 21-a), and `reussir-ut` passes 82 of 82. On `l2r-base9`
its tests pass with the rest of the suite (776 pass, 2 fail for want of
the `not` tool).

## Review

An independent review (local notes, `rccancel-review/`) found the rule
sound. Every pair that the patch cancels in lean2rr's L12, L17 and Z01c
and in the new tests (2494 pairs) has the intended shape, and Reussir's
output for lean2rr's leanrt backend (then the default) did not change. Its three findings
are in the patch: runtime inputs for the end-to-end tests (their
records first folded to constants, so ASan saw no counts), the
operations that the scan now crosses named in the commit message with a
negative test, and the stop at `rcgmp.bridge.mpz.is_unique`.

## Upstream note

The change is general, not lean2rr's: any by-value record or tuple with
rcgmp integer members, taken apart and dropped, keeps a retain and a
release per member without it. It extends #801's counted-word
cancellation with #568's extract/spill rule, which rc members already
have, and one effect-based rule for the scan. The patch is
self-contained; its commit message has the motivation, the change and
its tests.
