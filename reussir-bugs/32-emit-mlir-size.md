# 32. `rrc --emit mlir` output grows exponentially with record nesting

## Summary

**Kind:** cost (debug output). **Status:** open (debug output only). No
patch.

**Verdict: cost of the textual format, not a defect.** The MLIR printer
writes a named record's body at every place the record occurs, so a
record reachable along k paths in a type is written k times, at every use
of the type. When records share sub-records the dump grows exponentially
with their nesting, and rrc holds the whole text in memory. This is the
mechanism of [bug 10](10-closure-type-print.md), in the general printer.
Patch 0024, written for bug 10, changed only the closure devirtualization's
type ids. A fix would change the dialect's textual format, and the output
is only a debug dump, so it stays unpatched.

## Symptom and repro

Repro [`repros/bug32-emit-mlir-size.py`](repros/bug32-emit-mlir-size.py)
`K OUT.rr` writes `D0 = struct(u64)` and `D(i) = struct(D(i-1), D(i-1))`,
builds a `D(K)` and prints `1`.

**Command.** `rrc OUT.rr --emit mlir -o OUT.mlir`.

**Expected.** A dump about linear in K (the program is).

**Actual on ef922049.** About 2x per level: K = 8: 0.55 MB, K = 10:
2.2 MB, K = 12: 8.7 MB. `run.sh` prints `bug 32   REPRODUCES  --emit mlir:
K = 10: 2133 KB, K = 12: 8532 KB (3.99x for two more levels)` (also with
0060 to 0063). Bug 10's generator, which nests the same records inside
closure types, gives 16 MB at K = 10 and 1.0 GB at K = 16 (14 s, 1.06 GB of
rrc memory).

In lean2rr's output (found when the dumps of two adversarial-round
programs, `Tower` and `Io6Http`, passed 31 GB and 55 GB of memory): a small
program, MapMIO (291 KB of `.rr`), dumps 11 MB of MLIR in 0.3 s, with lines
up to 68,000 characters.

## Cause

`RecordType::print` (`lib/IR/ReussirTypes.cpp`) writes the record's kind,
name and, unless the record is already being printed (a self-reference),
its whole body; the body's members are printed the same way. The MLIR
printer replaces a type by an alias (`!name = ...` once at the top) only if
the dialect's `OpAsmDialectInterface` provides one, and the Reussir dialect
has none. So every operand, result and signature writes its types in full,
and a named record that a type reaches along k paths is written k times.
The parser needs this form: it accepts the short form `<kind "name">` only
for a record whose body it is reading (a self-reference); elsewhere it is
"invalid self-reference within record".

`--emit mlir` builds the text with `module.as_operation().to_string()`
(`crates/reussir-compiler/src/driver/backend.rs`) before writing it, so rrc
needs about as much memory as the dump's size.

## lean2rr

No effect on builds: `scripts/l2r.py` never asks for `--emit mlir`.
lean2rr's types nest deeply (function representations and `Box` types in
polymorphic recursion, monad transformer towers), so its dumps are large,
and the largest programs cannot be dumped. To look at one, dump a smaller
program, or a later stage (`--emit mlir-llvm`), where a boxed record is an
opaque `!llvm.ptr` and the nesting stops at each box.

## Why it stays unpatched

A fix changes the textual format: either the dialect gives named records
type aliases (every dump gains an alias section and uses the aliases), or
the printer writes each body once per type and the parser accepts the
short form for a record defined earlier (patch 0024's
`printTypeWithRecordBodiesOnce` is the printing half, used only for type
ids). Either is a design change of the dialect's textual form, not a
small fix: aliases must also cover recursive records (printed while their
own body is being printed), the second needs a new parser rule, and the
printed types that Reussir's tests match change (14 test files check
printed record types). For a debug output that lean2rr does not use, that
is not worth a local divergence; costs stay documented, not patched.

## Upstream note

`RecordType::print` writes a named record's body at each occurrence and
the dialect defines no type aliases, so `--emit mlir` is exponential in the
nesting of records that share sub-records (`D(i) = struct(D(i-1),
D(i-1))`: about 2x per level; lean2rr programs with tens of GB).
Possible fix: aliases for named records through `OpAsmDialectInterface`.
