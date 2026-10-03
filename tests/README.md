# lean2rr tests

The classic corpus is the reference for correctness and performance: every
program is compiled natively by stock Lean 4.33, its outputs are recorded,
and an alternative implementation (lean2rr's output) must reproduce them
exactly. `oracle.py` does the building, recording, checking and timing.

## Layout

- `classic/` — a Lake package (Lean v4.33.0, core `Init`/`Std` only), one
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
  (commit `d8b18978322de05a8f3dba51ef03cf5461676c17`). `const_fold` is the
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
  Native bench-size results (`oracle.py bench --repeat 3`):

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
