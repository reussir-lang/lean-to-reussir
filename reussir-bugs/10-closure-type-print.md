# 10. Closure devirtualization prints result types exponentially

## Summary

**Kind:** bug (build time). **Status:** worked around (build time only;
lean2rr passes `--no-closure-wpd`). No patch yet.

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
adversarial rounds build in 15 s to 2.5 minutes.
