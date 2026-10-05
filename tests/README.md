# lean2rr tests

The classic corpus is the reference for correctness and performance: every
program is compiled natively by stock Lean 4.34, its outputs are recorded,
and an alternative implementation (lean2rr's output) must reproduce them
exactly. `oracle.py` does the building, recording, checking and timing.

## Layout

- `classic/` — a Lake package (Lean v4.34.0, core `Init`/`Std` only), one
  executable per case. The executable name is the case name; the root module
  is the CamelCase file of the same name at the package root.
- `classic/cases.json` — for each case: `name`, `exe`, `module`, `origin`
  and `sizes` (`small` < 0.1 s, `medium` < 1 s, `bench` 1–10 s natively).
- `classic/expected/<name>.<size>.{stdout,stderr,exitcode}` — the native
  outputs, recorded by `oracle.py record`.
- `oracle.py` — the harness (Python 3, standard library only).

Every program has `main (args : List String)`; the first argument is the
size (parsed with `String.toNat?`; default: the upstream constant for the
ported cases, the bench size for the others). Output is a few deterministic
lines of results and checksums that depend on all the work, printed so that
a divergence points at the part that went wrong. No case reads files, stdin,
the environment or the clock, uses randomness or `initialize`, writes to
stderr, panics, or exits nonzero.

## Cases

| case | origin | stresses | small / medium / bench |
|---|---|---|---|
| rbtree | Perceus (Koka) | red-black tree insertion, in-place updates of a uniquely owned tree, a closure passed to `fold`; `prelude` module | 100000 / 1000000 / 8000000 |
| rbtree-ck | Perceus (Koka) | the same with every 5th tree kept alive (shared trees, copying) | 100000 / 1000000 / 4200000 |
| deriv | Perceus (Koka) | symbolic differentiation: `Int`, `String`, big trees, `partial` functions, IO in a fold | 8 / 10 / 11 |
| nqueens | Perceus (Koka, ported) | lists of lists, `Int32` arithmetic and comparisons | 10 / 13 / 14 |
| cfold | Perceus (Lean `const_fold`) | expression rewriting, deep non-tail recursion | 15 / 20 / 23 |
| binarytrees | Lean 4 | allocation-heavy trees, `UInt32`, `Task.spawn`/`Task.get` | 14 / 18 / 21 |
| qsort | Lean 4 | in-place `Array UInt32` quicksort, `@[specialize]`, `UInt32` indices, `IO.Ref`, `throw` | 80 / 250 / 400 |
| unionfind | Lean 4 | hand-written `StateT`/`ExceptT` monads, arrays of structures | 70000 / 1000000 / 3000000 |
| rbmap | Lean 4 | rbtree with a fold polymorphic in the accumulator | 100000 / 1000000 / 8000000 |
| liasolver | Lean 4 | `Std.HashMap Nat Int`, big `Int`s, `Id.run do`, string parsing, range iterators | 16 / 30 / 50 |
| bignum | new | `Nat`/`Int` far past 2^64: Fibonacci and factorial two ways, the three `Int` divisions, bit operations, the 2^63/2^64 boundaries, decimal conversion | 1000 / 3000 / 6000 |
| sieve | new | `Array Bool`/`Array Nat` updates, `for` over (stepped) ranges with `break`/`continue`, `while`, proof-carrying indices | 1000000 / 10000000 / 50000000 |
| mergesort | new | one generic merge sort over `List α` with `[Ord α]` at `Nat`, `Int`, `String`, `UInt64` and two user structures (derived and hand-written `Ord`); stability | 10000 / 100000 / 300000 |
| higher-order | new | map/filter/folds, closures in lists/arrays/structures/`Option`, partial application, closures returned after work, unknown closures of several arities, over-application, Church numerals, CPS | 100000 / 3000000 / 20000000 |
| monadic-interp | new | an interpreter in `ReaderT (ExceptT (StateT IO))`: do-notation, early `return`, `break`/`continue` (also inside `catch`), `throw`/`try`/`finally`, `IO` errors; a checker in `ExceptT (StateM)` over `Id` | 1000 / 10000 / 30000 |
| typeclass-generic | new | generic `sum` at `Nat`/`Int`/`UInt64`/`Float`/user type, a user class hierarchy with `mconcat`/`mpow`, instances built from instances, default methods, packed values carrying their own dictionary, `outParam`, a user `Functor` | 100000 / 1000000 / 10000000 |
| strings | new | building (`push`, `++`, interpolation), `splitOn`, `toNat?`/`toInt?`, UTF-8 (`length` vs `utf8ByteSize`, positions, bytes), `Char` operations, slices, `String.hash`, `toString` of `Nat`/`Int`/`Float` including inf/NaN/-0 | 20000 / 200000 / 1000000 |
| hashmap | new | `Std.HashMap`/`HashSet` with `Nat`, `String` and derived-`Hashable` structure keys: insert/overwrite, hit/miss lookups, erase, `alter`/`modify`/`insertIfNew`, `fold`/`for`, iteration order | 10000 / 1000000 / 4000000 |

## Provenance

Each file's header cites its source and lists every change made to it.

- Perceus paper benchmarks: the Lean versions in the Koka repository,
  `test/bench/lean/` at commit `cf5607640061031052c2ad6da86ce0f9ac8cd287`
  (branch `dev`; the files were added in commit `f1e0b74b`). That directory
  has rbtree, rbtree-ck and deriv (and rbtree4, not used). rbtree and
  rbtree-ck needed only the removal of obsolete syntax. The Koka `deriv.lean`
  no longer elaborates; the Lean repository's current-syntax copy of the same
  program is used. There is no Lean nqueens, so `Nqueens.lean` is a
  line-by-line port of Koka's `test/bench/koka/nqueens.kk`. There is no Lean
  cfold either; Koka's `cfold.kk` says it is adapted from the Lean
  repository's `const_fold`, so `Cfold.lean` is that Lean program.
- Lean 4 repository benchmarks: `tests/compile_bench/` at tag `v4.33.0`
  (commit `d8b18978322de05a8f3dba51ef03cf5461676c17`; the files used are
  unchanged at `v4.34.0`). `const_fold` is the
  cfold case. `rbmap` is included because it differs from Koka's rbtree
  (polymorphic `fold`, argument order). Changes: an optional size argument;
  qsort, which printed nothing, prints a checksum of every sorted array;
  liasolver embeds its input file, drops an unused `Lean.AssocList` import,
  and runs a sweep over subsystems of its problem (see its header). The
  bench sweep ends with the upstream problem and prints upstream's expected
  output.
- The other eight cases were written for this corpus. Their expected outputs
  were checked independently: bignum's output is identical to a Python
  reimplementation at every size, the sieve's for small and medium, prime
  counts match the known values of π(x), and the mergesort and hashmap
  results match values computed separately.

## Harness

```
python3 tests/oracle.py build                   # lake build in tests/classic
python3 tests/oracle.py record                  # run natively, write expected/
python3 tests/oracle.py check --cmd 'out/{exe} {size}' [--cases A B] [--sizes small medium]
python3 tests/oracle.py bench --cmd 'out/{exe} {size}' [--cases A B] [--size bench] [--repeat 5]
```

The native builds (`oracle.py build`, `tests/runtime/run.sh`,
`tests/env/run.sh`, `tests/runtime/nat-alloc-check.sh`,
`tests/runtime/conv-count-check.sh`, `tests/reussir-benchmark/run.sh`, `reussir-bugs/repros/run.sh`) and
`scripts/l2r.py`'s GMP use the Lean toolchain lean2rr is pinned to
(`lean2rr/lean-toolchain`, the elan toolchain
`~/.elan/toolchains/leanprover--lean4---v4.34.0`), not elan's default:
`scripts/toolchain.sh` puts its `bin/` first on `PATH`. Set
`L2R_LEAN_TOOLCHAIN` to a toolchain directory to use another.

To check lean2rr with some of its optimizations turned off, build with
`scripts/l2r.py --disable-opt NAME` (repeatable), or set
`L2R_DISABLE_OPTS=a,b` (and `L2R_ENABLE_OPTS`) in the environment, which
`scripts/l2r.py` reads and therefore `tests/runtime/run.sh` and
`tests/reussir-benchmark/run.sh` too. `lean2rr --list-opts` lists the
optimizations.

The `--cmd` template is run by the shell with the placeholders `{name}`,
`{exe}`, `{module}`, `{size}` (the size argument) and `{native}` (the path
of the native executable). `check --cmd '{native} {size}'` checks that the
native outputs are reproducible.

- `check` compares stdout, stderr and the exit code byte for byte, prints a
  pass/fail table and the first differing line of each mismatch, and exits
  with status 1 if anything differs.
- `bench` runs native and alternative interleaved, pinned with `taskset` to
  the least-loaded of the fastest cores (chosen again for each case from
  `/proc/stat`), and reports the minimum wall time and maximum RSS
  (`/usr/bin/time -f "%e %M"`) of each and their ratios. It also flags runs
  whose stdout differs from the recorded output. Without `--cmd` it times
  only the native executables.

## Notes for alternative implementations

- Native Lean runs `main` on a thread with a 1 GB stack
  (`LEAN_DEFAULT_THREAD_STACK_SIZE`, `src/runtime/thread.cpp`). cfold's
  `appendAdd` recursion is about 2^(n-1) frames deep: about 4M for the
  bench size 23. n = 24 overflows even natively, which is why cfold's bench
  run is below 1 s.
- binarytrees uses `Task.spawn`. Under `bench` everything is pinned to one
  core, so the tasks share it.
- deriv at the bench size needs about 4.6 GB, rbtree-ck about 1.4 GB, cfold
  about 1.3 GB.
- The sizes were chosen by timing the native executables pinned to an idle
  Cortex-X925 core (3.9 GHz, NVIDIA DGX Spark), taking the minimum of 3 runs.
  Native bench-size results (`oracle.py bench --repeat 3`; measured with
  Lean 4.33, not yet re-measured with 4.34, whose runtime uses mimalloc 3):

| case | bench size | time (s) | max RSS (MiB) |
|---|---:|---:|---:|
| rbtree | 8000000 | 1.84 | 373.4 |
| rbtree-ck | 4200000 | 1.36 | 1383.4 |
| deriv | 11 | 4.16 | 4653.7 |
| nqueens | 14 | 3.63 | 719.9 |
| cfold | 23 | 0.73 | 1267.6 |
| binarytrees | 21 | 2.99 | 247.1 |
| qsort | 400 | 1.19 | 7.8 |
| unionfind | 3000000 | 1.15 | 139.6 |
| rbmap | 8000000 | 1.87 | 373.9 |
| liasolver | 50 | 2.12 | 10.8 |
| bignum | 6000 | 2.46 | 8.0 |
| sieve | 50000000 | 1.46 | 485.8 |
| mergesort | 300000 | 1.38 | 97.8 |
| higher-order | 20000000 | 2.34 | 8.1 |
| monadic-interp | 30000 | 1.80 | 8.0 |
| typeclass-generic | 10000000 | 2.15 | 12.1 |
| strings | 1000000 | 1.80 | 149.9 |
| hashmap | 4000000 | 1.53 | 233.9 |

## The Reussir benchmark programs

`tests/reussir-benchmark/run.sh BENCHMARK_CHECKOUT [NAME...]` checks the
Lean programs of the Reussir benchmark suite (a checkout of
github.com/reussir-lang/benchmark, `lean/*.lean`, used under their own file
names such as `rbtree-zipper.lean`): it builds each one natively as the
suite's `compile.py` does (`lean FILE -c`, `leanc -flto -O3`) and through
lean2rr (`lean -o`, then `scripts/l2r.py FILE.lean`), runs both and compares
stdout, stderr and the exit code. The programs check their own results. It
is a correctness check only; the suite itself does the timing.

## Loader checks

`tests/env/run.sh` checks which program modules lean2rr accepts (plan §10,
"Module names"). For each case it translates a small program (`lean2rr
--emit mono`, a few seconds) and expects either acceptance or rejection:
- rejected: program modules named `Lean.*` or `L2RShim`, a directory
  `L2RShim` of program modules, Lean's library with one module's `.olean`
  or `.olean.private` replaced by a different file, and a shim directory
  without the shim (`L2R_SHIM_DIR` missing or empty, or unset with the
  lean2rr binary moved out of its build directory);
- accepted: Lean's library reached through a symbolic link or through hard
  links, a working directory whose `lean-toolchain` names another Lean, and
  the shim from the build directory or from `L2R_SHIM_DIR`.

It also runs `lean2rr --stats` on polymorphic recursion at a doubling type,
which must finish (`stats-polyrec`).

## Runtime tests and the findings they cover

`tests/runtime/run.sh` builds each `tests/runtime/Rt*.lean` natively and
through lean2rr and compares stdout, stderr and the exit code (its header
lists the per-test `.args`, `.stdin`, `.pipe`, `.opts`, `.xfail`, `.ffi.c`,
`.refused` and `.l2r-log` files: `.ffi.c` is C code for the native build
only, `.refused` an expected refusal by lean2rr, `.l2r-log` lines
expected in lean2rr's build output). Each
test's header says what it covers. Many come from the adversarial reviews:
a finding (a bug a reviewer reproduced, fixed since) or a check that held
up in review.

`tests/runtime/leanrt-unit.sh` runs the runtime crate's unit tests.
`tests/runtime/allow-missing-check.sh` builds `tests/runtime/AllowMissing.lean`
(refused externs of the program used directly, partially applied, as a
closure, through an instance and through the `ptrAddrUnsafe` shortcut) with
`L2R_ALLOW_MISSING_EXTERNS=1` and checks that lean2rr warns, that rrc fails
on an unknown `l2r_refused_…` function, and that the generated code calls
no runtime function of those symbols (review REB-15, of REB-11).
`tests/runtime/ffi-inline-check.sh` builds runtime tests that call the libm,
string, hash, float and fixed-width rules to LLVM IR (`scripts/l2r.py --emit
llvm-ir`) and fails on a call through the packed-argument FFI boundary (a
texture LLVM did not inline; review RULR-01) or a `black_box` barrier inside
a Reussir function (an inlined `black_box`ed libm function; RULR-07): either
would keep a Lean loop's tail call.
`tests/runtime/rows-check.sh` builds lean-runtime's row oracle
(`scripts/oracle/Oracle.lean` of the lean-runtime checkout, which evaluates
the functions of its `tests/cases/<area>/<area>.rows.toml`) with lean2rr and
checks every row's expected outcome, recorded from native Lean 4.34.0
(with lean-runtime's `scripts/gen_rows.py`): the prelude's own inline code
and its glue around lean-runtime meet lean-runtime's rows (hashes, strings,
floats, fixed-width integers, libm, `Nat` and `Int`, arrays, panics, the
text of numbers). A row whose `deviations` name an `LB-nn` of lean-runtime's
docs/lean-bugs.md expects the Lean definition's result, which lean2rr must
give (native's outcome, in the row's `native`, is not compared); a row
naming a difference of lean2rr's own (none so far) is listed, not
failed.

Tests for findings (the reviews' FINDINGS.txt files are in the scratch
directories `adv3`..`adv6`, `rv6`..`rv9`). The rows marked "none" are
coverage tests, not findings: round 9's area crane re-expressed shapes from
the regression tests of Crane (Bloomberg's Rocq-to-C++ extractor, another
typed, reference-counted code generator) in Lean; they held up, and each
test's header lists the Crane tests it covers. Round 9's area cslib
extracted the computational code of CSLib (github.com/leanprover/cslib,
990e65a) into programs that import only Init (proofs dropped; CSLib itself
imports Mathlib, which is not a target, plan §10); they gave the same
output as native, and each test's header lists the CSLib and Mathlib files
it draws on, with their copyright notices (Apache 2.0):

| finding | test |
|---|---|
| RP3-1, RP3-2 | RtPtrEqFix |
| RP3-3 | RtFnConvChain |
| RP3-4, RP3-5 | RtCastCases |
| RP3-6 | RtArraySelf |
| P3-2..P3-5 | RtTaskPrio, RtTaskSyncBind, RtTaskSyncDep, RtTaskSyncRun |
| CN3-02, CN3-03 | RtInitSpec, RtStartWhere |
| PF4-03, PF4-10, RP4-08 | RtLazyReturned |
| PF4-07 | RtArrayMapRepr |
| PF4-10 | RtSinkProj |
| RP4-03..RP4-07 | RtCastRepr |
| ST4-01 | RtStartLongLine, RtStartMacro |
| IO6-01, IO6-02, IO6-03 | RtRandomBytes |
| IO6-04, IO6-05 | RtCwdLong |
| IO6-06 | RtHardwareConcurrency |
| IO6-03, IO6-08, IO6-10, IO6-11, IO6-12 | RtUvSysLimits |
| IO6-09 | RtOsStringsLossy |
| IO6-13 | RtTimerPeriod0 |
| IO6-14 | RtJpRebound |
| S6-01 (Reussir bug 21), RV6L-01 | RtStrLitBracket |
| PRG6-01 | RtNestedMap |
| PRG6-02 | RtWildcardSink |
| TY6-01 | RtNestGrowType |
| TY6-02 | RtBoxNoCast, RtCastSorry |
| U1 (adv6 numbers), RV6L-03 | RtFloatCastBits |
| RV6J-03 | RtJpWide |
| RV6L-02 | RtMapFirstIteration |
| RV6L-04 (and the hygienic forms of RV6T-01/02) | RtCastHygienic |
| RV6T-01 | RtCastExtern (now refused: the binding's type test, plan §5.8) |
| RV6T-02 | RtCastUnsafeRec |
| RV6T-04 | RtTaskConvSync |
| RV6T-05 | RtCastImplementedBy |
| RV6T-06 | tests/env `lean-named-module` |
| RV7F-01 | RtDepFields, RtLcAnyProj |
| RV7D-01 | RtMapProjFields, RtLcAnyProj, RtFuzzArr (operation 11), RtSplitMaps (SMapA shape 6) |
| RV7F-02, RV7F-04 | RtDictConst |
| RV7F-03, RV7R-03 | tests/env `stats-polyrec` |
| RV7L-01 | RtPersistWalk, RtTaskConstDeep |
| RV7L-03 | RtJpSlots |
| RV7O-01 | RtStartMeta (a `module` main; the multi-module cases have no test) |
| RV7O-02 | tests/env `lake-named-module` |
| RV7O-03 | RtInitRedirectNoThread |
| RV7C-01 | RtPromiseFreeSync, RtPromiseFreeGlue |
| RV7C-02 | RtSyncLostWake |
| RV7C-03 | RtPromiseResultDropped |
| RV7C-04 | RtStackOverflowContexts |
| RV7C-05 | RtSignalFd |
| RV7C-06 | RtNetEffectPoll |
| RV7C-07 | RtTimerSyncSleep |
| RV8L-01, RV8L-02, RV8L-06, RV8L-07 | tests/env |
| RV8T-01, RV8T-02 | RtRefSetOrder, RtRefSetFiles, RtSyncLostWakeLoop |
| RV8T-03 | RtTimerStopDropped |
| RV8T-04 | RtSockCancel |
| RV9C-01, C01R-01, C01R-03 | RtZeroFinite, RtZeroLazyCycle, RtZeroTaskCycle, RtZeroWalkRef, RtZeroWalkRefNoCache |
| RV9C-02, C02R-01, C02R-02, C03R-01 | RtUniformUpdates, RtUniformUpdatesJp, RtUniformUpdatesMixed, RtUniformUpdatesNested, RtUniformUpdatesShared (and `conv-count-check.sh`) |
| RV9L-01, RV9L-01a | RtCtorNameClash |
| R9S2R-04 (review of RV9S-02: no test took `boxCastConv`'s rollback) | RtConvProbeRollback (and `conv-count-check.sh`) |
| XT-6 (cross-test), XT6-01..XT6-04 | RtCseAcrossTypes, RtCseFnValues, RtCseResidual, RtCseFnField, RtCseFnTrivial, RtCseFnResult (expectation files: the trace prints once natively, twice through lean2rr) |
| RVA-01 (review of perf-rvec) | RtReadIntoArray |
| LR1-01 (lean-runtime's oracle rows) | RtStringExtractBig |
| lean-runtime's case io/startup_fd_limit (`IO.stdGenRef`, the library's initializer, ran only when the program used it) | RtStartupInitUrandom, RtStartupInitRand |
| RSG-01 (review of fix-stdgen: the library's initializers ran before the program's, not at their module's place) | RtStartupInitOrder (companion module `StartupInitOrderDep`, `RtStartupInitOrder.deps`) |
| RSG-02, RSG-03 (a program that uses the `Lean` package: `lean_initialize()` runs `Init`'s initializers first; natively an error there aborts) | RtStartupInitLeanPkg (expectation files for RSG-03, plan §10) |
| RV8E-01, RV8E-02, RV8E-05, RV8E-06 (rv8/ext, branch lean-externs) | RtExternNames, RtExternLeanPkg |
| RV8E-03 | the `.l2r-log` files of the `RtExtern*` tests |
| RV8E-04 | RtExternRefused |
| RV8E-09 (now refused: no binding to Lean's runtime) | RtExternOpaqueRedecl |
| RV8E-10 (now refused: no binding to Lean's runtime) | RtExternOpaqueRepr |
| RV8E-11 | RtExternFold |
| none: checks of rv8/ext round 1 (ExtImpl, ExtRec, ExtMisc, ExtZip) | RtExternForms, RtExternRec, RtExternBytes |
| REB-01 (review of extern-bodies) | RtExternFold (`exportShl`) |
| REB-02 | RtExternStub |
| REB-03 | RtExternRefused (`decodeLossy`) |
| REB-07 | RtExternRefused (`myRepr`, `np`) |
| REB-10, REB-12, REB-18 | RtExternPrivate, RtExternRefused (`decodeLossy`) |
| REB-11, REB-15 | `tests/runtime/allow-missing-check.sh` |
| REB-13, REB-14 | RtExternStub (`dec`, `myDrop2`), RtExternRefused (`myDropO`) |
| none: coverage from the Crane corpus (rv9/crane CrGram) | RtGrammarActions |
| none: coverage from the Crane corpus (rv9/crane CrPrintf) | RtComputedFnTypes |
| none: coverage from the Crane corpus (rv9/crane CrUniq; the Lean form of Reussir bug 28's shape) | RtSharedOnOnePath |
| none: coverage from the Crane corpus (rv9/crane CrDrain, CrInd) | RtDropMediated |
| none: coverage from the Crane corpus (rv9/crane CrConv) | RtConvMediated |
| none: coverage from the Crane corpus (rv9/crane CrReuse) | RtReuseAlias |
| none: coverage from the Crane corpus (rv9/crane CrPoly) | RtUniformFnTypes |
| none: coverage from the Crane corpus (rv9/crane CrLoop) | RtMutualTailArgs |
| none: coverage from the Crane corpus (rv9/crane CrTask) | RtTaskCaptureUpdate |
| none: coverage from CSLib (rv9/cslib CslxInsertion: `TimeM`, monadic insertion sort) | RtCslInsertion |
| none: coverage from CSLib (rv9/cslib CslxMergeSort: monadic merge sort, comparison counts) | RtCslMergeSort |
| none: coverage from CSLib (rv9/cslib CslxTuring: single- and multi-tape Turing machines) | RtCslTuring |
| none: coverage from CSLib (rv9/cslib CslxURM: unlimited register machine) | RtCslURM |
| none: coverage from CSLib (rv9/cslib CslxVending: CCS terms, Milner's vending machine) | RtCslVending |

Findings without a test here: costs (time, memory, build time or code
size), Reussir-only bugs (lit tests in their patches), documentation
findings, documented differences (translation plan §10), and findings whose
fix is still on another branch, which adds its own test.

Tests made from the programs of checks that held up in review rounds 6 and 7
(the first curation, c35d7b8; combined programs keep one namespace each):

| test | reviewer check |
|---|---|
| RtSweepNat | adv6/numbers NArith, NBits |
| RtSweepInt | adv6/numbers IArith |
| RtSweepFixed | adv6/numbers UOps, SOps |
| RtSweepFloat | adv6/numbers FOps, FSweep |
| RtFloatLibm | adv6/numbers FBits |
| RtNumText | adv6/numbers CStr, CChar |
| RtFuzzScalar | adv6/numbers fz/G1 (gen.py) |
| RtFuzzReuse | adv6/types Ty6Rnd1 (genreuse.py) |
| RtExistPayloads | adv6/types Ty6Exist |
| RtSweepStrPos | rv7/rtdata DStrPos |
| RtSweepUtf8 | rv7/rtdata DUtf8; adv6/stdlib T30Utf8 |
| RtSweepStrInternal | rv7/rtdata DInternal, DSlice |
| RtFuzzStr | rv7/rtdata DFuzzStr, DStrSearch |
| RtFuzzBig | rv7/rtdata DBig, DAlias |
| RtFuzzFloatBits | rv7/rtdata DFloat |
| RtArrEdges | rv7/rtdata DArrEdge, DGrow, DConstMut |
| RtFuzzArr | rv7/rtdata DFuzzArr |
| RtShareMutators | rv7/lowering check 2 (LwShare2) |
| RtExternEdges | rv7/lowering check 16 (LwExtEdge1) |
| RtJpShapes | rv7/lowering check 7 (LwJp1) |
| RtOutlineStates | rv7/lowering check 9 (LwOutMut) |
| RtFnValues | rv7/lowering checks 12, 13 (LwFn1, LwFn2) |
| RtGenControl | rv7/lowering check 26 (Rcf6, gen/rcf.py) |
| RtStateMachines | rv7/opts O7SM, O7SM2; rv6/jp check 18 (JpSm3) |
| RtSplitMaps | rv7/opts O7Map; rv6/lower check 5 (SMapA) |
| RtConvUniform | rv7/repr R7Conv |
| RtReprFuzzCtx | rv7/repr fz/Gz5 (gen2.py) |
| RtReprFuzzTypes | rv7/repr fz/gen.py, seed 7, 6 types |
