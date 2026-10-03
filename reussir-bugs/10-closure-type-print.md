# 10. Closure devirtualization prints result types exponentially

## Summary

**Kind:** bug (build time). **Status:** patched (0024), applied in
`./reussir` (`l2r-local` 5c0514e3); lean2rr also works around it (it
passes `--no-closure-wpd`).

With `-O aggressive`, rrc's closure devirtualization computes a type id for
each closure result type by printing the type to a string, uncached, and
the printer expands every named record inline. lean2rr's function and
`Box` types nest deeply in polymorphic recursion, so build time and memory
grow exponentially.

## Symptom and repro

Repro [`repros/bug10-closure-type-print.py`](repros/bug10-closure-type-print.py)
`K OUT.rr` writes a program with `D0 = struct(u64)` and
`D(i) = struct(D(i-1), D(i-1))`, and twenty closures of type `u64 -> D(K)`
chosen at run time, so their calls stay indirect. `D(K)` printed with
every named record expanded has 2^K copies of `D0`. The program prints
`780`.

**Command.** `rrc OUT.rr -O aggressive`, and the same with
`--no-closure-wpd`.

**Expected.** Build time about the same with and without closure
devirtualization, and growing linearly with K.

**Actual on ef922049** (rrc build time and peak memory, this machine):

| K | `-O aggressive` | with `--no-closure-wpd` |
|---|---|---|
| 16 | 1.2 s | 0.5 s |
| 18 | 3.8-8.4 s | 0.5-1.3 s |
| 20 | 24 s, 250 MB | 0.7-0.8 s |
| 22 | 89 s, 730 MB | 0.7 s |

`run.sh` on the final stack: `bug 10   FIXED       K = 20: 2.5 s with
closure devirtualization, 2.1 s with --no-closure-wpd   [-O aggressive]`
(loaded machine); K = 22 builds in 0.4 s either way.

The same exponential text appears in `rrc --emit mlir`, which prints every
type with the same rule ([bug 32](32-emit-mlir-size.md)); 0024 does not
change that printer.

Sizes that hit the limits (lean2rr outputs before the workaround, rrc to an
object file, 16 GB limit): a polymorphic recursion through a `StateT` tower
(`Cn3PolyS1`, 1291 functions) took 313 s and 8.1 GB (39 s and 0.8 GB with
`--no-closure-wpd`); two others (`Cn3PolyWhere`, `Cn3PolyMut`) ran out of
memory after 184 s and 225 s.

## Cause

With `-O aggressive`, rrc devirtualizes closures. It computes a type id for
each closure result type by printing the type to a string and hashing it
(`closureWpdTypeId`, `include/Reussir/Conversion/ClosureWpd.h`), uncached,
at every indirect call, clone or drop site (`emitClosureWpdTest`) and every
vtable (`stampClosureWpdTypeIds`, both in
`lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp`).
`RecordType::print` (`lib/IR/ReussirTypes.cpp`) expands named records
inline and stops only at a record already on its print stack, so a record
reached k ways is printed k times. lean2rr's function and `Box` types nest
deeply in polymorphic recursion, so the text grows exponentially.

## lean2rr

Reussir closures occur in lean2rr's output in the `raw(A -> B)` arm of
every generated function enum `L2RFn_…` (plan §5.3: a Reussir closure,
for values built by glue code); their result types, often `L2RBox` or
another function enum, are what the devirtualization prints in full.

The driver (`scripts/l2r.py`) passes `--no-closure-wpd`. The classic
benchmarks measured the same with and without it, within noise (lean2rr
dispatches its function values itself), so it costs nothing measurable.
Fewer and smaller types would shrink the printed text, but the text is
exponential in nesting either way, and the towers that hit this also hit
[bug 20](20-statet-tower.md); with both worked around the towers of the
adversarial rounds build in 15 s to 2.5 minutes. lean2rr keeps passing the
flag with 0024 applied (README policy: workarounds stay, so that lean2rr
also works with an unpatched Reussir); it costs nothing measurable.

## Patch

Patch file
[`patches/0024-l2r-local-bug-10-compute-closure-WPD-type-ids-from-a.patch`](patches/0024-l2r-local-bug-10-compute-closure-WPD-type-ids-from-a.patch)
(`l2r-local` commit `362d6a21`, applied in `./reussir`; `l2r-local` head
`5c0514e3`).

**The change.** A new printer entry point,
`printTypeWithRecordBodiesOnce` (`include/Reussir/IR/ReussirTypes.h`,
`lib/IR/ReussirTypes.cpp`): the usual printer, except that while it runs,
`RecordType::print` writes a named record's body only at its first
occurrence and later occurrences as `<kind "name">`, the form it already
uses for a self-reference. A thread-local set holds the named records
already written; it exists only during that call, and is saved and
restored around it:

```c++
   cyclicPrintGuard = printer.tryStartCyclicPrint(*this);
-  if (failed(cyclicPrintGuard)) {
+  if (failed(cyclicPrintGuard) ||
+      (getName() && recordBodiesPrinted &&
+       !recordBodiesPrinted->insert(*this).second)) {
     printer << '>';
     return;
   }
```

`closureWpdTypeId` (`include/Reussir/Conversion/ClosureWpd.h`) digests that
text instead of `output.print(os)`; the comments there and
`docs/design/closure-wpd.md` say so. Each named record now costs its body
once per id instead of once per path.

**Why it is correct.** The id must be equal for equal types and distinct
for distinct ones. Named records are unique by (name, kind) in a context,
and the short form includes both, so the text still determines the type;
equal types print the same text because the traversal order depends only
on the type. Types in which no named record repeats print exactly as
before, so their ids are unchanged; where one repeats, the id changes but
the grouping of vtables and call sites into families does not. The
devirtualization is speculative (a guarded direct call with an indirect
fallback), so even a wrong id could not call the wrong closure. Only named
records are shortened: an unnamed composite type that repeats along many
paths (a closure type `T(i+1) = (T(i)) -> T(i)`) is still written in full
each time, as before, and rrc is exponential on such types without
devirtualization too; the comments state this limit.

**Verification.**

- Test `tests/integration/frontend/closure_wpd_nested_records` (with a C
  driver): a 22-level tower; the two `D22` closures share an id, the `D21`
  closure has another. It took 23 s and 690 MB before the patch.
- The object files of the repro at K = 12 are identical with and without
  the patch; the LLVM IR of Reussir's frontend tests is identical after
  renaming the ids in order of appearance.
- `run.sh` on the final stack: `bug 10   FIXED` (above).
- On the final stack (all 34 patches): Reussir's lit suite, 645 tests, 564
  passed, 81 unsupported, none failed.

**Review.** Round 7, `p22` (`~/Documents/l2r-scratch/rv7/p22/FINDINGS.txt`
and `round2/FINDINGS.txt`): the id is still injective and deterministic
(checks above, records in different modules get path-qualified names, a
12-closure, 11-family program with same-shaped records under different
names: identical IR and id grouping; lean2rr's RtFnConvChain, RtThunk and
RtHashMap with devirtualization on: identical IR). Two findings, both
fixed: RV7P-02, the comments and the commit message claimed a text linear
in the number of distinct types, which unnamed closure types contradict
(now stated as above); RV7P-04, `docs/design/closure-wpd.md` still gave
the id as the digest of `print(c)` (now `text(c)`, the new printer).

**Effect on lean2rr.** None while it passes `--no-closure-wpd`. Without the
flag, its closure result types (`L2RBox`, function enums `L2RFn_…`, named
records) no longer make build time exponential.

## Upstream note

`closureWpdTypeId` (ClosureWpd.h) hashes `type.print()`, and
`RecordType::print` writes a named record's body at each occurrence, so a
record reached along k paths costs k bodies: `D(i) = struct(D(i-1),
D(i-1))` at K = 22 took 89 s with closure devirtualization against 0.7 s
without. Fix: a printing mode that writes each named record's body once
(later occurrences as `<kind "name">`) for computing the id.
