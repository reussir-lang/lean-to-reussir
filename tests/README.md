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
`tests/runtime/conv-count-check.sh`, `tests/runtime/alloc-check.sh`,
`tests/runtime/paynothing-check.sh`, `tests/runtime/determinism-check.sh`,
`tests/reussir-benchmark/run.sh`, `reussir-bugs/repros/run.sh`) and
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
  Lean 4.33, when the sizes were chosen). Native Lean 4.34.0, whose runtime
  uses mimalloc 3, was timed at the bench size on 2026-10-04 (best of 5):
  its times are in
  [`../docs/implementation-status.md`](../docs/implementation-status.md#performance),
  "Performance". The table keeps the 4.33 sizing run:

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

## Applications

`tests/apps/` holds real Lean programs of more than one module. Each is a
Lake package with its own runner script. The runner copies the package
into its build directory and builds it natively (`lake build`) and through
lean2rr (`scripts/l2r.py` on the root module, with the package's `.olean`
files on `--lean-path`). Then it runs both with the same arguments and
compares stdout, stderr, the exit code and each file that the program
writes, byte for byte. It does no timing.

- `tests/apps/raytracer/`: lean4-raytracer
  (github.com/kmill/lean4-raytracer, commit 205143b; Apache 2.0, its
  `LICENSE.md`), the ray tracer of the book *Ray Tracing in One Weekend*
  in two modules (`Main`, `Render.Vec3`). It writes a PPM image. `NOTICE`
  lists our changes: the port to Lean 4.34 (`Array.replicate`), the image
  settings on the command line (`render FILE WIDTH SAMPLES THREADS
  [DEPTH]`) and THREADS = 0, which renders on the main thread.
  `tests/apps/raytracer/run.sh [CONFIG...]` runs `small0` (60×40 pixels,
  2 samples per pixel, depth 10, main thread) and `small1` (the same in
  one task) by default, and `bench0` (200×133 pixels, 4 samples per pixel,
  depth 30, main thread; about 10 s natively) when you name it. Only
  THREADS = 0 and THREADS = 1 give one image: all tasks take random
  numbers from `IO.stdGenRef`, so natively the image of two or more tasks
  changes from run to run. The program uses `Float` arithmetic through a
  polymorphic structure (`Vec3 α` at `Float`), inductive types with
  `Float` fields, a reference to the random generator that the inner loop
  reads and writes, arrays of structures, and a file written line by line.

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
lists the per-test `.args`, `.stdin`, `.pipe`, `.opts`, `.enable-opts`,
`.xfail`, `.ffi.c`, `.refused`, `.l2r-log` and `.l2r-debug` files: `.opts`
turns optimizations off for the test, `.enable-opts` turns on one that is
off by default (`unread-fields`), `.ffi.c` is C code for the native build
only, `.refused` an expected refusal by lean2rr, `.l2r-log` lines
expected in lean2rr's build output, `.l2r-debug` the same with lean2rr
run under `L2R_DEBUG=1`, which prints its whole-program facts: whether the
program can cast, the compact array kinds). Each
test's header says what it covers. Many come from the adversarial reviews:
a finding (a bug a reviewer reproduced, fixed since) or a check that held
up in review.

The tests `RtUnreadFields*` check the optimization `unread-fields` (off by
default; each turns it on with `.enable-opts`, except `RtUnreadFieldsHookOff`):
callbacks that `initialize` blocks register and no kept code reads are
left out (`RtUnreadFieldsHook`: its callbacks call a C++ function of the
`Lean` package, and without the pass lean2rr refuses the same program,
`RtUnreadFieldsHookOff`); callbacks read by projection, by a match or
through a nested field (`RtUnreadFieldsCalled`), through `unsafeCast`
(`RtUnreadFieldsCast`) or only by the runtime (a stderr stream's
`putStr`, `RtUnreadFieldsStream`; an extern used as a function value,
`RtUnreadFieldsExternFn`) stay, and so does a closure that holds a file
handle (`RtUnreadFieldsHandle`); the initializers' output and their
error keep native's order (`RtUnreadFieldsStartup`). Data goes too: `Expr`s
that Lean's C++ builds, in a field no code reads (`RtUnreadFieldsData`;
refused without the pass, `RtUnreadFieldsDataOff`), while data read by
projection, by a match, through a nested field or only by derived
`BEq`/`Hashable`/`Ord`/`Repr` instances stays (`RtUnreadFieldsDataRead`). A test's `.opts`
also takes its names out of `L2R_ENABLE_OPTS` (`RtUnreadFieldsHookOff`
stays refused in a run that turns the pass on for all).

`tests/runtime/leanrt-unit.sh` runs the runtime crate's unit tests, with
debug assertions on (so leanrt's invariant checks run, such as no big
`Int` in the small range).
`tests/runtime/any-probe.sh` probes the one-word box `LAny` (every `Box`)
with a hand-written Reussir program (`tests/runtime/any-probe/`)
appended to a translated host program and linked with an allocation
tracker: 19 scenarios (records, enums with nullary variants, function
values and closures capturing boxes, strings, big numbers, cells, value
records holding boxes, arrays of boxes, references, chains of 10^6 boxes
on a 1 MiB stack, boxes in records, `box(0)` at every kind of type, the
generic textures at scalars, the order of observable releases checked
against native Lean's, `tests/runtime/any-probe/Order.lean`), each run
twice, under both of Reussir's
nullary-variant encodings; the second run must give its result and free
every block it allocates exactly once. A third run unboxes at the wrong
number and must end with Lean's internal panic. It needs a Reussir with
patch 38-a (`L2R_REUSSIR`).
`tests/runtime/allow-missing-check.sh` builds `tests/runtime/AllowMissing.lean`
(refused externs of the program used directly, partially applied, as a
closure, through an instance and through the `ptrAddrUnsafe` shortcut) with
`L2R_ALLOW_MISSING_EXTERNS=1` and checks that lean2rr warns, that rrc fails
on an unknown `l2r_refused_…` function, and that the generated code calls
no runtime function of those symbols (review REB-15, of REB-11).
`tests/runtime/prelude-liveness-check.sh` translates `RtIO` with and
without the optimization `prelude-liveness` (lean2rr only) and checks that
the generated parts of the two texts are equal, that the text without it
starts with the whole prelude, and that the text with it keeps at most half
of the prelude's `#[ffi(import)]` functions (RtIO: 86 of 493; each is a
rustc run of rrc when its texture cache misses).
`tests/runtime/ffi-inline-check.sh` builds runtime tests that call the libm,
string, hash, float and fixed-width rules to LLVM IR (`scripts/l2r.py --emit
llvm-ir`) and fails on a call through the packed-argument FFI boundary (a
texture LLVM did not inline; review RULR-01) or a `black_box` barrier inside
a Reussir function (an inlined `black_box`ed libm function; RULR-07): either
would keep a Lean loop's tail call. For `RtReadsDeep` it also fails when an
array read stays a call (reads deep in branches, cold call sites), except
the three reads that cost more than LLVM's cold-site threshold
(`l2r_view_take<LAny>`, `l2r_view_take_as<Nat>` and `<Int>`), whose calls
it allows and counts (Reussir issue 36, not patched: its patch 36-a is
parked), and for `RtArraySets` when an array set or read stays a call
(sets in loops and a read of a box, at ordinary call sites; the set of an
`Array` of a structure stayed a call before switch step 10).
`tests/runtime/wait-inline-check.sh` builds `RtWaitInline` (a program that
creates tasks, with a loop of reference operations and a loop forcing
thunks) to an executable and fails when, in the functions that hold the
loops, a fast path of lean-runtime's wait cores (the reference points, a
thunk's store `l2r_lcell_set` and its `done_keyed`) is reached by a call, a
tail or conditional branch, or a `blr` to an address the function builds
or loads from the GOT, or when the executable has a TLS descriptor or
module relocation (a thread-local access the linker did not relax): it
reads the linked machine code (lean2rr's condition L7 for switch step 6;
review RS6-03). It then checks itself on four mutations, each of which
must fail: a `bl`, a `cbnz` and a `blr` to a fast path added to the
disassembly, and a TLS descriptor relocation added to readelf's output
(RS6-06; an indirect tail branch `br` is tracked as `blr` is).
`tests/runtime/const-read-check.sh` builds `RtConstReads` (constants of
every kind of once-cell read in loops: a table computed at startup, a
literal table, closed terms, a toolchain constant, a small scalar,
64-bit and 8-bit zeros, in a task too) to LLVM IR and fails when, on the
hot path of a loop, a constant's read calls its accessor, a once-cell
texture or a function of leanrt's `once` module, or loads leanrt's slot
record instead of the tables at fixed addresses (a read of a constant is
one load: docs/implementation/startup/constants.md). It reads symbols by
their identifiers, whatever the mangling's prefix, fails when it finds
no accessor or cannot read the IR's symbols, and checks itself on four
mutations of the IR named from the IR's own symbols (a call of an
accessor, of `l2r_once_claim`, of `once::claim`, a load of the record,
added to a hot loop block), each of which must fail (review PCR-01).
`tests/runtime/sm-slots-check.sh` builds `RtSmDecode` (a table-driven
decoder loop, a state machine of three variants), `RtStateMachines` and
`RtJpSlots` to LLVM IR and fails when the entry point of a state machine
whose variants are all nullary is an enum, not an integer (in the `.rr`),
when its match is not one literal arm per variant (0, 1, ... in order)
and an unreachable wildcard, when its entry point is not an integer in
the IR, when LLVM did not thread RtSmDecode's loop (no DFAJumpThreading
block `.jtN` in its IR function), when a call entering a variant puts
anything but a placeholder, or a slot that the calling arm does not bind,
in a slot that the variant does not bind (a live value kept alive across
the jump, RF-1), or when an arm passes a placeholder in a slot that it
does not bind instead of the slot itself
(docs/implementation/control-flow/state-machines.md). It fails when
RtSmDecode has no such state machine or no slot passed on, and checks
itself on six mutations of RtSmDecode's `.rr` and IR (the entry point made
a `[value]` enum, a passed-on slot given a placeholder, a placeholder
replaced by the arm's live variable of that slot, the wildcard arm taken
away, the IR's entry point made a struct, the IR's threaded blocks
renamed), each of which must fail.
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

### Representation changes: allocations, determinism, pay nothing

Values whose type is not known at compile time use the uniform layout
(`Box` fields; before the one-word `LAny`, the enum `L2RBox`), and a value
that went from one layout to the other was converted (plan §2.6, §10 "Structural conversions";
`docs/implementation/conversions/`). The blowup audit (`BA-00`..`BA-19`)
and the design reviews of a layout redesign (`DRC-…` correctness,
`DRP-…` performance) found where that costs more than native Lean, and
asked for these checks before the redesign. They cover costs as well as
results, so each runs at two sizes.

- `tests/runtime/alloccount/`: an allocation counter, `alloccount.c`, linked
  into both builds with `-Wl,--wrap` on mimalloc's allocation entry points
  (both runtimes link mimalloc statically: native Lean's libleanrt, and
  Reussir's runtime crate under lean2rr). At exit it prints `alloccount:
  allocs A reallocs R bytes B` to stderr. `alloccount.sh` compiles it with
  `leanc` and gives the link flags of both builds (`leanc … $AC_LEANC`;
  `L2R_RRC_FLAGS=$AC_RRC` for `scripts/l2r.py`, which hands each
  `--link-arg` to rrc's link). It needs an ELF linker with `--wrap` (GNU
  ld, gold, lld); a run that prints no count fails the check.
- `tests/runtime/alloc-check.sh [NAME...]` builds each runtime test that has
  a `NAME.alloc` file natively and through lean2rr with the counter, runs
  both at the two sizes of each line of `NAME.alloc` (`SMALL ARGS | LARGE
  ARGS | FACTOR OFFSET [| rss FACTOR OFFSET_KB]`), and checks that the
  outputs equal native's, and that lean2rr's allocations, and the bytes it
  allocates, grow from the small run to the large one at most FACTOR times
  as much as native's, plus OFFSET (64 × OFFSET bytes): `L_large − L_small
  ≤ FACTOR × (N_large − N_small) + OFFSET`. The startup of each build
  cancels out; linear where native is linear passes, quadratic or
  exponential where native is linear fails at sizes a few times apart. The
  bytes catch the copies of a whole array (one allocation of n elements),
  which the count alone misses (C03R-01, BA-13). `rss` also bounds the peak
  memory of the large run. The sizes keep every run under a second on
  today's lean2rr, quadratic or not.
- A `NAME.xfail` whose first line starts with `alloc-check:` marks only the
  allocation check as known to fail: `run.sh` then still expects the
  test's output to equal native's. `alloc-check.sh` reports `XFAIL` for
  any `NAME.xfail`, and `XPASS` when such a test passes. Each of these
  files says what dev does (its numbers at the two sizes) and that one
  layout for each datatype (rule 1 of the design site's page "Dependent
  types") removes it.
- `tests/runtime/determinism-check.sh [PROGRAM...]` translates a few
  programs (`lean2rr --emit rr`, no Reussir build) twice and requires
  byte-identical `.rr` files; then it adds an unrelated definition (a
  structure of two numbers and a recursive function over it, with a new
  entry point `l2rDetRoot` that runs `main` and then the function,
  translated with `--root l2rDetRoot`) and requires every function
  translated from the program's own code, except `main`, to be unchanged
  in the canonical form below. A program known to fail is listed in the
  script's `KNOWN` table with the reason (XFAIL).
- `tests/runtime/rr-fingerprint.py` gives each item of the generated part
  of a `.rr` file (functions, types, `extern` lines) a hash of a canonical
  form that does not change when only lean2rr's numbering changes: one
  counter numbers types (`T_List_15`), helpers (`l2r_zero_836`, `jp_77`),
  the payload numbers of `Box` and local names, and Stage 1
  numbers each declaration's instances in the order it finds them, so an
  added definition shifts names in code it does not touch. Numbered names
  become labels made from their own canonical definitions; string literal
  indices become the literals. `show` prints the pay-nothing counts and
  the hashes, `compare` and `check` list the changed and dropped items, and
  `text` prints an item's canonical form.
- `tests/runtime/paynothing-check.sh [--update] [NAME...]`: programs
  without values of unknown type (the classic programs rbtree, cfold,
  qsort, deriv and unionfind at their `small` size, and RtJpSlots and
  RtLazyFields) against their baselines in `tests/runtime/paynothing/`: the
  pay-nothing counts of the generated code (conversion helpers and their
  uses, values put into a `Box`, the program's pointer payload types of
  `Box`) must not
  grow, nor the allocations and bytes of a run (1% plus 100 allocations or
  10000 bytes of slack); the native counts are recorded beside them. The
  changed items are listed (with `PAYNOTHING_STRICT=1` they fail the
  check). `--update` rewrites the baselines after an intended change; the
  allocation counts belong to this machine's toolchain and runtime pin.

The runtime tests of this suite are named `RtRepr*` (the older
`RtReprFuzzCtx`, `RtReprFuzzTypes` and `RtReprShare` are other tests):

| source | test | what | `alloc-check` |
|---|---|---|---|
| BA-01, BA-02, BA-07 | RtDepShareDag, RtDepShareShapes, RtDepShareHeld | a shared tree, rose tree, list of suffixes and five more shapes through existentials | see "Dependent types" below |
| BA-03 | RtReprProdDag | a shared tree through `Prod`, packed once | exponential (rule 1) |
| BA-04 | RtReprThunkDag | a shared tree in a forced thunk, packed once | exponential (rule 1) |
| BA-05 | RtReprCseDag | a shared tree converted typed to typed after `cse` | exponential (rule 1) |
| BA-06 | RtReprArrShared | one row shared n times in an `Array (Array α)` | quadratic (rule 1) |
| BA-08 | RtReprExistShared | one list in n live packages | quadratic, also peak memory (rule 1) |
| BA-09 | RtReprExistRepack | a growing list packed at every step | quadratic (rule 1) |
| BA-10 | RtReprRefUniform | an `IO.Ref (List α)` modified by uniform code | quadratic (rule 1) |
| BA-11 | RtReprColListLib | a list column, cons then a typed `head!` | quadratic (rule 1) |
| BA-12 = C03R-01 | RtUniformUpdatesShared | a typed helper on the uniform column | quadratic in bytes (rule 1) |
| BA-13 | RtReprColPassOn | a helper passing its parameter on at `Array Nat` | quadratic in bytes (rule 1) |
| BA-14 | RtReprFnArgConv | a typed function value applied by uniform code | quadratic (rule 1) |
| BA-15 | RtReprOpenPoly | a generic function field called with typed lists | quadratic (rule 1) |
| BA-16 | RtReprThunkRepack | a forced thunk packed at every step | quadratic (rule 1) |
| BA-17 | RtDepBoxMatchReads, RtDepBoxMatchFallback; RtReprBoxCopy | reads of a dependent payload; RtReprBoxCopy: the reducible family and a payload boxed again | quadratic (rule 1) |
| BA-18 | RtDepProofBuilder, RtDepUniformBuilder | a builder at a proposition; at a type too large for its own copy | see "Dependent types" below |
| BA-19 | RtReprThunkChain, RtReprThunkForced | a thunk's round trips typed → uniform → typed, pending (both modes' output) and forced | pending: linear; forced: quadratic (rule 1) |
| DRP-04 | RtReprRecRepack | BA-09 with the list also in a typed record field | quadratic (rule 1) |
| DRC-07 | RtReprSwapLoop | a tail loop swapping a typed and a crossing list: 10^8 iterations, constant stack | — |
| DRC-01 | RtReprInitRef, RtReprExitPoly | `initialize` values; an exit code from the uniform instance (7) | — |
| DRC-02 | RtReprDepHeads | one dependent position reached by two heads | — |
| DRC-04, DRC-05 | RtReprModShape | `Array.modify`'s placeholder, `Array.map`'s cast | — |
| DRC-08 | RtReprConstAcc | constants shared by a helper's callers | — |
| audit semantics probes | RtReprRefAlias, RtReprThunkOnce, RtReprTaskOnce, RtReprClosure, RtReprCowPlaceholder, RtReprIndexed | aliasing, evaluation once, closure timing, copy-on-write, indexed families across crossings | RtReprIndexed passes (no conversion) |
| audit, repeated crossings | RtReprFnRoundTrip | a function value through two packages and back at every step: no wrapper chain | passes |
| audit, checked and not a problem | RtReprNestPair, RtReprMonadGrow, RtReprCseLoop, RtReprColUpdateTyped | polymorphic recursion at `α × α` and through `StateT`; a `cse`-merged value read in a loop; a typed helper whose call sites are all uniform | pass (guards: linear today) |

BA-00 (in test builds only, the conversion counter broke the loop of the
conversion machine: a deep conversion overflowed the stack) has the shape of
RtConvDeep (an 8 MB stack) and of RtDepDeep's left spine. The branches
fix-conv-sharing, fix-box-match and fix-proof-builder are superseded by the
layout redesign (one layout per datatype, rule 1 of the design site's page
"Dependent types"); their tests are RtDep* tests below, without the address
checks (sharing is checked by memory).

### Dependent types: the `RtDep*` corpus

Values whose type is not known at compile time, or depends on a value
(existential packages, dependent pairs and fields, polymorphic recursion,
type parameters, casts), and the points where a function runs when some of
its parameters are types. Each test's output must equal native's; each
runs in well under a second natively. A blowup (a value copied when its
representation changes) shows as allocation growth, checked by
`alloc-check.sh` at two sizes (the test's `.alloc`), not as a long run.
Sharing is checked by memory, not by addresses (`ptrAddrUnsafe` may differ,
site rule 7). The corpus also has a copy outside the repository, with
native's outputs, for other translators' cross-checks.

Tests from repros of earlier reviews (the scratch directories named in the
first column):

| source | test | what | `alloc-check` on dev |
|---|---|---|---|
| BA-01; dag-blowup, site-deptypes `DagTree`; fix-conv-sharing's RtConvShareDag | RtDepShareDag | a tree of n + 1 shared nodes (2^n paths) through existentials, also built by code over an unknown type and cast back; flat memory at n = 16 and 28 | exponential (`.xfail`: rule 1) |
| BA-02, BA-07; fix-conv-sharing's RtConvShareShapes | RtDepShareShapes | shared values of eight shapes (array diamond, mutual, nested `Rose`, one array twice, list suffixes, function values and thunks in a DAG) through existentials; flat memory | exponential (`.xfail`: rule 1) |
| fix-conv-sharing's RtConvShareHeld | RtDepShareHeld | unshared trees, lists and arrays packed while held and as their last use, read back with `unsafeCast`; linear | linear but 5 × native (`.xfail`: rule 1) |
| BA-17 (mode copy); fix-box-match's RtBoxMatchReads | RtDepBoxMatchReads | n reads by a match of a dependent payload; O(1) per read | quadratic (`.xfail`: rule 1) |
| BA-17; fix-box-match's RtBoxMatchFallback | RtDepBoxMatchFallback | matches on a dependent payload for every way it was built and every pattern shape | — |
| BA-18; fix-proof-builder's RtProofBuilder | RtDepProofBuilder | generic builders and structures over `Sort u` at a proposition and at data; linear | quadratic (`.xfail`: rule 1) |
| BA-18 (data); fix-proof-builder's RtUniformBuilder | RtDepUniformBuilder | a generic builder at a type with more than 256 nodes; linear | quadratic (`.xfail`: rule 1) |
| design-review-perf `ClosureLoopPack` (BA-09 in a closure) | RtDepClosureLoopPack | a growing list packed at every step of a loop run by a stored closure | quadratic (`.xfail`: rule 1) |
| design-review-perf `ColdPack` | RtDepColdPack | a hot `List Float` field loop with a cold packing branch | passes |
| design-review-perf `P1Rebox` | RtDepP1Rebox | a `Float` loop state stored into two packages per step | passes |
| design-review-correctness `closedpanic` (DRC2-01) | RtDepClosedPanic | a closed term whose callee traces and panics: evaluated once | — |
| review-opus `anytest` (Any1, Conf, Drop, Dyn, Fields, Layout) | RtDepReviewOpus | type fields, `Bool`-selected types, a proof-only function, `Dynamic`, computed field types, scalar fields | — |
| review-fable `c123`, `c4`, `c4b` | RtDepReviewFable | `pick`, proof fields, a computed `Σ`, recursion at `List α`, `f Nat` fields, closures over scalars | — |
| review-fable `mem` | RtDepListMem | lists of n `Float`s and small `Nat`s: allocations and peak memory | passes |
| site-lcnf2 `SiteEx` (the design site's program) | RtDepSiteEx | the page "Dependent types" in one program | — |
| site-deptypes `Spec` | RtDepSiteSpec | one generic function at `Tree Float` and `Tree String` | — |
| b0-cast `UnitAsNat` | RtDepUnitAsNat | the unit value read as a `Nat` (0) | — |

New cases:

| test | what | `alloc-check` on dev |
|---|---|---|
| RtDepExist | existential packages of nine types; `Sigma`/`PSigma` with a type-valued first component; a column with `Array ty.denote` for eight types; `Dynamic`; packages with their own `ToString`, `BEq`, `Hashable` | — |
| RtDepFieldLoops | each kind of type-parameter field (`α`, `List`, `Array`, `IO.Ref`, `Thunk`, `Task`, `α → β`, `α → α → α`, `Option`, `Except`, `Array (Array α)`, `List (α × β)`, `Std.HashMap`) read, changed and stored back in n steps by typed code and by code over the unknown type | quadratic in 11 of 13 modes (`.xfail`: rule 1) |
| RtDepPayloadScalars | every scalar kind (with a 300-constructor enum, `UInt64` around 2^63, float specials, `Nat`/`Int` boundaries) through nine generic routes, bit for bit | — |
| RtDepPayloadObjects | strings, byte/float arrays, arrays of each kind, structures, `Subtype`, `Fin`, closures, recursive/mutual/nested inductives, computed fields, sums and products of scalars, through the same routes | — |
| RtDepOneField | one-field structures over a type parameter (represented as their field) and `unsafeCast` between containers of them and of the field type | — |
| RtDepShareMany | one list and one array in K generic containers of every kind at once | K × M (`.xfail`: rule 1) |
| RtDepDeep | chains of 10^6 nested values of unknown type, built, read in loops and freed at an 8 MB stack (`RtDepDeep.pipe`; BA-00's shape) | — |
| RtDepPolyRec | polymorphic recursion with dictionaries built per level, nested datatypes over growing types, monad transformers added per level at an unknown monad | — |
| RtDepCasts | the library's casts (`Array.map`/`mapM`/`mapIdx`/`mapFinIdx`, `Array.modify`, `attach`/`pmap`, `ShareCommon`) and user casts (`NonScalar`, unit/`Fin`/`Subtype` as `Nat`) | — |
| RtDepEraseTiming | where bodies run when parameters are types (rule 4): traces and their counts equal native's | — |
| RtDepRoundTrip | references and function values through every generic container and back; aliasing holds | — |
| RtDepGenericOrder | sorting, equality, hashing and sums by generic code on boxed scalars around 2^63, floats, chars, strings | — |
| RtDepUnique | in-place updates of a value held in an existential by code over its unknown type | passes (linear: one box per step) |
| RtDepIOResults | IO results of every scalar kind through generic monads, `initialize` values of generic types, an exit code | — |
| RtDepFloatArrayAlloc | `get!`, `getD`, `modify`, `set!` on an `Array Float` and on arrays of one-field structures over `Float` and `UInt64`, constants pushed, reads out of bounds, `unsafeCast ()` read back (adversarial finding 2: a constant default is boxed once, `Array.modify`'s placeholder is `box(0)`) | passes (before the fix on this branch: a cell per `get!`, two per update) |
| RtDepBoxedClosedOnce | a closed term that traces, evaluated where it is used by a constant and boxed there, runs once (`boxed-consts` leaves such closed terms out) | — |
| RtDeadBoxedConst | a boxed closed term in a branch that never runs is not computed (a judged Lean compiler bug: natively its `_boxed_const` is computed at startup and the program hangs; expectation files, `.pipe` with a 3-second limit) | — |
| RtDepDropOrderBoxed | the order in which handles in boxes (a `List IO.FS.Handle`, a structure over a type parameter) close when user code drops the value by itself (adversarial finding 3; expectation files, plan §10) | — |

`RtDepX*` hold the cases of the shared dependent-type corpus (programs
another translator's team wrote and checked against native Lean), about
eleven to a test: each case in a namespace named after its case id, run by
the test's `main` with its own arguments after a line `-- <id>`
(docs/implementation/testing.md, "The shared cases are combined"). A case
that exits with another code than 0, has a global effect, or is checked at
a large size is a test of its own (`RtDepX<id>`). Left out as exact
duplicates: A936 (RtProcess) and A1028 (RtCseFnResult).

| test | cases (shared case ids) |
|---|---|
| RtDepXA01 | A1007 A1011 A1012 A1013 A1015 A1016 A1017 A1018 A1019 A1020 A1021 |
| RtDepXA02 | A1023 A1024 A1025 A1026 A1027 A1040 A1041 A1042 A1043 A1044 A1045 |
| RtDepXA03 | A1046 A1048 A1049 A1066 A1067 A1068 A1069 A1070 A1071 A1072 A1073 |
| RtDepXA04 | A1074 A1075 A1076 A1077 A1078 A1079 A1080 A1081 A1082 A1083 A1084 |
| RtDepXA05 | A1085 A1086 A1087 A1088 A1089 A1090 A1091 A1092 A1093 A1095 |
| RtDepXA06 | A1096 A1097 A1098 A1099 A1200 A1202 A587 A612 A743 A765Field A765Op |
| RtDepXA07 | A765Ref A765Shared A769 A796 A797 A798 A799 A801 A802 A805 A806 |
| RtDepXA08 | A808 A817 A831 A834 A867 A869 A871 A872 A874 A876 |
| RtDepXA09 | A880 A881 A883 A885 A886 A887 A888 A890 A892 A893 A894 |
| RtDepXA10 | A896 A897 A910 A911 A912 A913 A914 A917 A918 A919 A924 |
| RtDepXA11 | A927 A931 A934 A935 A937 A942 A943 A947 A948 A951 A957 |
| RtDepXA12 | A958 A959 A960 A961 A962 A963 A964 A965 A968 A969 A970 |
| RtDepXA13 | A971 A972 A973 A974 A975 A977 A978 A979 A981 A982 A983 |
| RtDepXA14 | A984 A986 A987 A988 A989 A990 A991 A992 A993 A994 A995 |
| RtDepXA15 | A996 A997 A998 A999 A1111 A1310 A1300 A1301 A1302 A1303 A1304 |
| RtDepXA16 | A1305 A1306 A1307 A1308 A1311 A1312 A1313 A1314 A1315 A1316 A1317 |
| RtDepXA830 | A830 (its own test) |
| RtDepXA833 | A833 (its own test) |
| RtDepXA866 | A866 (its own test) |
| RtDepXA1010 | A1010 (its own test) |
| RtDepXA1014 | A1014 (its own test) |
| RtDepXA1100 | A1100 (its own test) |
| RtDepXD01 | D71Breaker2Q01 D71Breaker2Q02 D71Breaker2Q03 D71Breaker2Q04 D71Breaker2Q05 D71Breaker2Q06 D71Breaker2Q07 D71Breaker2Q08 D71Breaker2Q09 D71Breaker2Q09A D71Breaker2Q09B |
| RtDepXD02 | D71Breaker2Q09D D71Breaker2Q09E D71Breaker2Q09F D71Breaker2Q10 D71Breaker2Q11 D71Breaker2Q12 D71Breaker2Q16 D71Breaker2Q17 D71Breaker2Q19 D71Breaker2Q20 D71Breaker2Q21 |
| RtDepXD03 | D71Breaker3R01 D71Breaker3R02 D71Breaker3R03 D71Breaker3R04 D71Breaker3R05 D71Breaker3R06 D71Breaker3R07 D71Breaker3R08 D71Breaker3R09 D71Breaker3R11 D71Breaker3R12 |
| RtDepXD04 | D71Breaker3R13 D71BreakerP01 D71BreakerP02 D71BreakerP03 D71BreakerP04 D71BreakerP05 D71BreakerP06 D71BreakerP07 D71BreakerP08 D71BreakerP08B D71BreakerP08C |
| RtDepXD05 | D71BreakerP10 D71BreakerP11 D71BreakerP11A D71BreakerP11D D71BreakerP11F D71BreakerP12 D71BreakerP13 D71BreakerP14A D71BreakerP14AD D71BreakerP14AE D71BreakerP14B |
| RtDepXD06 | D71BreakerP14BC D71BreakerP14C D71BreakerP14D D71BreakerP14E D71BreakerP15 D71BreakerP16B D71BreakerP17 D71BreakerP18 D71BreakerP19 D71BreakerP20 D71BreakerP21 |
| RtDepXD07 | D71BreakerP22 D71BreakerP24A D71BreakerP24C D71BreakerP24D D71BreakerP24E D71BreakerP24F D71BreakerP25 D71BreakerP27 D71BreakerP28 D71BreakerP29 D71BreakerP30 |
| RtDepXD08 | D71BreakerP30C D71ReviewerC1 D71Tester8e9R01 D71Tester8e9R02 D71Tester8e9R03 D71Tester8e9R04 D71Tester8e9R05 D71Tester8e9R06 D71TesterF33N01 D71TesterF33N02 D71TesterF33N03 |
| RtDepXD09 | D71TesterF33N05 D71TesterF33N06 D71TesterF33N07 D71TesterF33N08 D71TesterF33N09 D71TesterF33N10 D71TesterF33N11 D71TesterF33N13 D71TesterF33T24G1 D71TesterF33T24G2 D71TesterF33T24G3 |
| RtDepXD10 | D71TesterF33T24G4 D71TesterF33T24P D71TesterT01 D71TesterT02 D71TesterT02A D71TesterT02B D71TesterT03 D71TesterT04 D71TesterT05 D71TesterT06B D71TesterT07 |
| RtDepXD11 | D71TesterT08 D71TesterT09 D71TesterT10 D71TesterT11 D71TesterT12 D71TesterT14 D71TesterT16 D71TesterT17 D71TesterT18 D71TesterT19 D71TesterT20 |
| RtDepXD12 | D71TesterT24A D71TesterT24B D71TesterT24C D71TesterT24D D71TesterT24I D71TesterT24K40 D71TesterT24K62 |
| RtDepXD13 | D71TesterT24L1 D71TesterT24L2 D71TesterT24L3 D71TesterT24L6 D71TesterT24M63 D71TesterT24N16 D71TesterT24N4 D71TesterT24N8 D71TesterT24O D71TesterT25 D71TesterT26 |
| RtDepXD14 | D71TesterT27 D71TesterT28 D71TesterT28A D71TesterT28B D71TesterT28C D71TesterT29 D71TesterT30 D71TesterT31 D71TesterT33 D71TesterT35 D71TesterT37 |
| RtDepXD15 | D71TesterT38 D71TesterT39 D71TesterT41A D71TesterT41B D71TesterX66 |
| RtDepXD71BreakerP09A | D71BreakerP09A (its own test) |
| RtDepXD71TesterT06 | D71TesterT06 (its own test) |
| RtDepXD71TesterT06A | D71TesterT06A (its own test) |
| RtDepXD71TesterT23 | D71TesterT23 (its own test) |
| RtDepXD71TesterT36 | D71TesterT36 (its own test) |
| RtDepXPairs | A1094, D71TesterT24E, T24F, T24H at five types |

Dev results of the shared cases: every output equals native's except
RtDepXA833 (`.xfail`, a lean2rr crash) and RtDepXD71TesterT23 (expectation
files, as RtCseFnResult then); `alloc-check` passes RtDepXA1010 and
RtDepXD71TesterT36 and fails RtDepXA1014 (its shared inner list is copied
for each element). With rule 1 and Stage 1's merged calls at the instance
at `lcAny` (plan §2.3), both outputs equal native's: the `.xfail` and the
expectation files are removed.

The `alloc-check` column of the tables above is dev 922ca03's result. With
rule 1 and the one-word box (`LAny`), `alloc-check` passes every test it
lists as failing, and the `alloc-check:` `.xfail` files of those tests and
of the 16 RtRepr* tests are removed.

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
| none: gaps in the walk of `programCasts` (found 2026-10-09) | RtCastPartial (a `partial def`'s `_unsafe_rec` code), RtCastCsimp (a `@[csimp]` replacement), RtCastCsimpLocal and RtCastCsimpScoped (a `local` and a `scoped` one, review of that fix), RtCastCsimpMacroInline (a replaced constant that only a library `@[macro_inline]` body mentions), RtCastExternBody (an extern whose definition casts) |
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
| R9S2R-04 (review of RV9S-02: no test took `boxCastConv`'s rollback; the rollback was removed with rule 1, its simplicity review's finding 1) | RtConvProbeRollback (and `conv-count-check.sh`) |
| XT-6 (cross-test), XT6-01..XT6-04 | RtCseAcrossTypes, RtCseFnValues, RtCseResidual, RtCseFnField, RtCseFnTrivial, RtCseFnResult |
| Review of the dependent-type work: shared case A833 (merged calls whose types are equal because `lcAny` hides the type argument), A1028 and D71TesterT23 (merged calls whose results hold functions of `α` ran apart) | RtCseHiddenAny, RtCseUniform, RtCseClosed, RtCseApart (expectation files: the shapes that still run apart or more often than natively, plan §10 "Merging after erasure"), RtDepXA833, RtDepXD71TesterT23 |
| Review of the cleanups of rule 1 (F2: with rule 1, `Runtime.markPersistent`, `markMultiThreaded`, `forget` and `hold` did not compile at any type: the generic primitive's result was taken to be of the IO result field's type, a `Box`) | RtRuntimeMarks |
| Review of the deferral of a box's word (22bcf89: `any::release_last` defers a box's tagged word as one pending cell; since the release table, the payload's cell) | RtBoxPackFreeOrder (boxes and a record with a wide header deferred in a row: the order of the closes), RtBoxDeepChain (10^6 nested boxes freed on a 1 MiB stack, `RtBoxDeepChain.pipe`) |
| Adversarial review of the dependent-type work: K3, K2, TypesAsData (a function polymorphic in `α : Type u` at `α := Type`: its data parameters erased, two applications merged) | RtTypesAsValues |
| Review of deptypes-lowperf, finding 1 (a `[value]` struct over a `Box`, `ST.Out σ α`, got a payload number of its own for the box: a panic at the first unboxing, with `l2r_any_of_ptr` at the first boxing) | RtValueStructBox |
| A Lean 4.34.0 compiler bug, judged (plan §10, "Compiler: Lean bugs we do not reproduce"): a `match` whose one arm gives a type or a predicate and whose other arm gives data; `joinTypes` types the join point's parameter `◾`, so native reads `box(0)` in place of the data (a wrong value or a crash), and lean2rr did too | RtJoinErasedProp, RtJoinErasedType, RtJoinErasedFlow; from the review of the fix RtJoinErasedIndirect, RtJoinErasedMisc, RtJoinErasedMerge, RtJoinErasedLayouts (native crashes: exit 139) (expectation files: native's output and the kernel's values) |
| Performance review of the dependent-type work, item 7 (an array element unboxed at once at an immediate type, `Nat` or `Int`: no copy of an immediate's box) | RtArrayReadImm (and `ffi-inline-check.sh`'s list of reads) |
| Performance review of the dependent-type work, translation size (cast conversions that never return a value; functions equal up to names) | RtCastDeadConv, RtMergeFns |
| Performance review of the dependent-type work, item 5 (a field or `let` of a parameter's type unboxed only to be boxed again; issue 39's shape must stay away) | RtBoxPassOn, RtBoxPassOnCast (a `List Nat` read as `List UInt8` and copied read back truncated words before), RtCastMixedRebox (expected to fail: the same field also used at its type), RtProbeBump (`alloc-check.sh`: the rebuilt cells reuse the matched ones), RtArrayAppendFloat (reviewer's E19Append, `alloc-check.sh`: `a ++ b` on `Array Float` made a cell per appended element) |
| RVA-01 (review of perf-rvec) | RtReadIntoArray |
| LR1-01 (lean-runtime's oracle rows) | RtStringExtractBig |
| lean-runtime's case io/startup_fd_limit (`IO.stdGenRef`, the library's initializer, ran only when the program used it) | RtStartupInitUrandom, RtStartupInitRand |
| lean-runtime's fixes-8, 83f7127 (`RtTcp` hung about one run in 20: a wait for a pure task that the worker started during the wait, with a socket watched) | RtTaskPickedInWait |
| switch step 10: the equality of a small and a big `Int` without a call, which relies on every `Int` result being normalized | RtIntSmallBigEq |
| Performance review of the dependent-type work, item 1 (loop states and monad results built with boxed fields at every step): optional pass `flatten-structs` | RtFlattenLoops (loop states: six variables in `IO`, an Adler-32 fold, `while` with `return`, an array updated in place, inner loops over short lists, a closure, `Float`, `UInt64`, `Bool` and a proof in a state, a stepped range, a non-tail recursion, `ptrEq` of a loop's result), RtFlattenResults (structure results: hand-written state and exception transformers, results read and stored, mutual and non-tail recursion, nested and scalar results, a function value, a function field, `ptrEq`), RtFlattenSums (two-constructor results: an interpreter in `ReaderT`/`ExceptT`/`StateT` over `IO`, runtime `IO` errors, `Option` results matched and stored, closed constants, `Except Empty Nat`, `ForInStep`), RtFlattenAlloc (`RtFlattenAlloc.alloc`: no allocation per step of a monadic call; an empty inner loop costs nothing), RtFlattenShared (review of the pass: a join point at a loop's exit, a result returned unchanged and stored, a matched pair returned through a function value: never a copy of the shared object, `ptrAddrUnsafe` identities and `RtFlattenShared.alloc`; `dbgTraceIfShared` of a value built in two branches), RtFlattenCopies (third round of the review: a loop that runs no step returns the caller's record, which a caller that stored the result built again from the tuple; a call's result stored and also given to a split join point parameter was built twice; `ptrAddrUnsafe` identities and `RtFlattenCopies.alloc`), RtFlattenFnValue, RtFlattenPeelFirst and RtFlattenTrace (fourth round: the caller's record copied where a loop returns it at once, through a function value and in a peeled loop's first step; `dbgTraceIfShared` then saw no shared object), RtFlattenOrder (a call's result used whole in a join point's body and at the jump to it, built twice) and RtFlattenNested (a record and its inner record, a loop's state in a join point's body and at its argument, a state and its inner record at a loop's exit, a pair passed from one join point to another: each built once; identities and `.alloc` files), RtFlattenSumPayload (fifth round: a two-constructor value built behind a join on its tag, then matched, its payload stored: built once), RtFlattenWrapArgs and RtFlattenSelfWrap (calls through the wrapper whose arguments the analysis counted as passed field by field), RtFlattenEscape (sixth round: a fresh value given to another loop's worker and also to a peeled loop's next state or a split result: built once), and RtBorrowRelease (the pass leaves a declaration with a resource parameter alone: Lean's reset/reuse into the worker's tuple made the matched `Child` owned, which closed its stdin pipe early) |
| switch step 10: the set of an `Array` of a structure was not inlined (ffi-inline-check) | RtArraySets |
| switch step 10: the order of the closes and promise dependents when one release frees an array of structures (a guard for the free of arrays of records) | RtArrayRecordFreeOrder |
| RS10-01 (review of switch step 10: an array set or pop releasing the last reference to a record closed its fields in field order, natively the last first) | RtArraySetFreeOrder, RtArrayPopFreeOrder |
| switch step 11: the last reference to a record is one pending cell of the free (a set, a pop and a reference set freeing structures whose fields hold structures and a list) | RtArraySetFreeNested |
| perf review of the dependent-type work, item 3: `ByteArray.data`/`mk` and `FloatArray.data`/`mk` as one loop at the exact size (leanrt's textures; in a program that casts, after a check of the boxes, else the generated loop) | RtByteArrayData, RtByteArrayDataCast |
| F1 (review of the runtime's speed items: an array whose elements are shared inside it was freed from its last element while decrementing; natively in two passes, the elements decremented in index order, then those whose count reached zero freed last first) | RtArrayDupFreeOrder |
| Review of the runtime's speed items, checks that held up: nested arrays with shared siblings freed on a 256 KiB stack, scalar cells and array conversions, the cast conversions, raw NaN payloads, boxes made and freed before `main`, leaf payloads | RtArrayDeepSharedFree (10^6 levels, `.pipe`), RtScalarCells, RtCastArrayConv, RtFloatArrayNanRaw, RtInitBoxes, RtBoxLeafRelease |
| leanrt-perf-1: the array free calls a boxed payload's release where the pending stack would pop it next (in the second pass's step; an array that keeps one element, outside a free, without a step): the closes in native's order | RtArrayFreeDirectOrder |
| switch step 11: a reference set that is the reference's last use freed the new value before the old one (runtime/README.md, Requests for lean2rr 33, done: `l2r_rc_set_ref` releases the reference after the old value) | RtRefSetLastUse |
| RS11-01 (review of switch step 11: below the first cell of a free, Reussir's glue released a cell's last record field before a later array field that had already pushed its free; Reussir patch 13-d, issue 13; its first part needed switch step 10 before rule 1; with rule 1 an array element is a box, which leanrt's worklist frees in Lean's order) | RtNestedArrayFreeOrder |
| review of Reussir patch 13-d (a record field before an array, a thunk, in a variant's arm, after an `Option` of a record, three cells below the start of a free; needs Reussir patch 13-d, which `scripts/l2r.py` requires) | RtDropDepth3Order |
| switch step 13, lean-runtime's LB-39 (review RF12-02 of its fixes-12): a dependent kept its priority as 32 bits, so 2^32 + 1 was a pool priority, and a priority of 2^64 or more was its low 64 bits, 0 (expectation files: natively 2^32 + 1 is a pool priority) | RtTaskPrioBig |
| switch step 13, lean-runtime's LB-36: `scaleB` by an `Int` outside the C `int` range, moved from RtFloat and RtSweepFloat (expectation files: natively `+0.0` for a NaN, an infinity, `-0.0` and a negative value scaled down) | RtFloatScaleBBig |
| `float-lits` missed a float literal whose `Bool` flag Lean's simp had replaced by a discriminant (in the alternative `true` of `cases b`, `Bool.true` becomes `b`), also after `simpJpCases` made the alternative a join point with that parameter: `Float.ofScientific` ran at every iteration of a loop (seen in an f64 loop of the boxed-constants work); `RtFloatLitDiscr.alloc` checks that lean2rr's allocations do not grow with N | RtFloatLitDiscr |
| HR-01 (hunt of references, promises and thunks; switch step 14): a promise resolved after a pipe handle's close whose bytes went to a writer thread: the generated test came before the store's writers point, where another task resolved it, and the store replaced that resolution | RtHandOffResolveAgain |
| HR-02 (the same hunt; switch step 14): `IO.mapTask (sync := true)` after such a close, over a task that finished during the wait: queued as a `sync` task, which printed the `Task.get` panic, the lines reversed; the handle closed by itself and inside a tree (a drain's end) | RtHandOffSyncMap, RtHandOffTreeSyncMap |
| HR-03 (the same hunt; switch step 14): `Std.Sync`'s try functions right after such a close took a lock that a task takes first natively (the task then waited for good) | RtHandOffTryLock |
| HSK-01 (hunt of stack sizes; switch step 16, lean-runtime's fixes-16): nested waits under deep recursion overflowed, as the single-thread scheduler ran each awaited task on its waiter's stack, where natively each runs on a worker thread of its own with a whole stack (`LEAN_STACK_SIZE_KB=16384`) | RtNestedWaitDeepStacks |
| HSK-03 (the same hunt): a deep recursion in a timer's `sync` dependent overflowed the event loop's context, which followed `LEAN_STACK_SIZE_KB`; natively libuv's loop thread always has 1 GiB | RtLoopDeepSyncDependent |
| HCO-01 (lean-runtime-side hunt of the cooperative IO layer; switch step 14): a pipe handle's last reference went inside its own primitive with the pipe full, and the close's wait for its writer (the drain-end hook) let a task's IO overwrite the primitive's recorded outcome: a `putStr` failed with the task's error, and a failed `truncate` succeeded | RtHandOffLastError |
| RS15-01 (review of switch step 15): a dedicated task's value, which the program dropped, was freed after the task's stream context had closed, so a promise's `sync` dependent that its free released printed to the process's stdout instead of the task's | RtDedicatedValueStreams |
| HTG-01 (hunt of the task glue): a dedicated task whose last reference went while it ran was ended in lean-runtime inside its job (`end_running_task`) before the job's reference to the cell went, so its finish woke an `IO.waitAny` that natively waits for the next finish (natively the task is deleted and freed without a notification) | RtDroppedDedicatedNotify |
| HTG-02 (the same hunt): `IO.cancel t` as `t`'s last use released the cell before the cancel read it (a read of freed memory for a finished task; no output shows it): the test exercises the path, a pure task that the release deletes after the cancel and a running task that sees the cancel | RtTaskCancelLastUse (`NAME.pipe`: one worker) |
| HIO3-01 (hunt of the io boundary): `IO.Process.forceExit` had only the writers point, not the effect point of `IO.Process.exit`, so a task queued before a computation without scheduling points that ends in `forceExit` never ran; natively a pool worker prints its line first | RtForceExitEffect |
| HTSK2-01 (hunt of the task, reference and sync glue, round 2): `Runtime.forget` released its argument, where native `lean_runtime_forget` never decrements it: a forgotten unresolved promise was resolved with `none`, a forgotten pure task was deleted before it ran, a forgotten file handle was closed at once | RtRuntimeForget (`NAME.pipe`: one worker; prints the file after the exit) |
| HTSK2-02 (the same hunt): `Runtime.markPersistent` did not wait for a promise its value reaches (the walk skipped a `Box` holding an `LPromise`); natively `lean_mark_persistent` pushes the promise's result task and waits for it | RtMarkPersistentPromise |
| Review RV-01 of HTSK2-02: no walk remembered what an earlier walk or the startup had reached, and the walk was skipped while no task was unfinished (always at startup; `[init]` results were never walked), so a closed term that reaches a reference made by an initializer or a constant read its current value and waited for the promise or task `main` had stored in it (natively the reference is persistent and not looked into): the program hung when `main` resolves the promise only after it reads the term, or printed its lines in another order; a second `Runtime.markPersistent` waited for what a reference and a thunk the first one marked got later. The walk now marks each cell it visits persistent (`leanrt::persist::mark`) and skips a marked one | RtPersistInitRef, RtPersistConstRef (each with `NAME.pipe`: a hang stops after 20 s), RtPersistConstRefPromise, RtPersistConstRefTask, RtMarkPersistentAgain |
| Review RV-02 of HTSK2-02: a closed term that makes a promise through unsafe code and starts its resolver did not wait for the promise (natively its first evaluation does) | RtPersistClosedPromise |
| Review RV-03 of HTSK2-02: `Runtime.markPersistent` made nothing persistent, so a marked file handle was closed at its last reference (natively it is never freed, and its bytes reach the file at the exit) | RtMarkPersistentHandle (`NAME.pipe`: prints the files after the exit) |
| The persistent walk of HTSK2-02's review: an initializer's result is walked after the initializer in a program that creates tasks, and the cells it visits are persistent, so a file handle in an initializer's `IO.Ref (Option IO.FS.Handle)` stays open when `main` sets the reference to `none`, as natively (hunt HSG-02's example; it still closes in a program without tasks) | RtPersistInitHandle (`NAME.pipe`: prints the file after the exit) |
| Review RS-01 of the persistent walk: at a box the walk marked the payload only when the payload's type could hold a task, so a file handle that a marked reference held directly (an initializer's `IO.Ref IO.FS.Handle`, a reference `Runtime.markPersistent` marked) was closed when the program set the reference to another handle; natively it stays open. A payload that cannot hold a task is now marked where its box is met | RtPersistInitHandleDirect, RtMarkPersistentRefHandle (each with `NAME.pipe`: prints the files after the exit) |
| HMEM-01 (hunt of leanrt's memory core): a list whose heads are boxed program payloads (pairs, structures, `Option`s, lists), dropped whole, kept each head in a 24-byte entry of Reussir's pending stack until the glue's walk along the tail ended (a leaf head too: leanrt deferred it inside a free); n = 4M pairs peaked at 391 MB, native 258 MB, consumed cell by cell 195 MB. A leaf payload is now released directly; a payload type whose cell has a wide header gets `WIDE_BIT` and is deferred `_wide`, linked through the cells (195 MB) | RtListDropWhole (`RtListDropWhole.alloc`: peak within native's plus 4000 KB, allocations and bytes as native's; on dev 0bfc2018 every mode failed the peak bound), leanrt's `any::tests::wide_cells_link_into_one_run` |
| HRT2-02 (hunt of Reussir's drop worklist against leanrt's release paths, after HMEM-01): a boxed function value's payload number had no `WIDE_BIT` (its enum's constructors are known only at the end of the translation), so a `List (Nat → Nat)` dropped whole kept each head in a 24-byte entry of Reussir's pending stack: n = 10^6 peaked at 89 MB, native 70 MB. Function types are now numbered with `WIDE_BIT` (their enums are fused shared enums); the enum of such a type stops the translation if it has more than 2^16 constructors (46 MB) | RtListDropWhole (mode `fns`; `RtListDropWhole.alloc`: on dev 935a87fa it failed the peak bound and the bytes bound) |
| HST-01 (hunt of the per-thread standard streams; switch step 15): a stdout that one UV callback's `sync` dependent set was gone for a later callback when the next loop context started on another id; natively the loop is one thread (the limit RS4-06 recorded) | RtLoopStreamsKept |
| HST-02 (hunt of the per-thread standard streams; switch step 15): at `main`'s end the drop of its stderr stream released a promise whose `sync` dependent printed to stdout, whose cell the leave had already dropped; the leave's assertion aborted the program with no output | RtStdLeaveReentry |
| switch step 14, lean-runtime's HF-01 (semantics-5): `Float.sin` and `Float.cos` of one operand inlined into one block became one `sincos` call, whose sine is one ulp off at ±0x1.ad1fb54442d18p+0 | RtFloatSinCosPair |
| switch step 14, lean-runtime's LB-46 (io-fixes-2): a fresh `append` handle's cursor is at the end of the file, so `truncate` keeps the content (expectation files: natively the file is emptied) | RtFileAppendTruncate |
| switch step 14, lean-runtime's RF14-07 (fixes-14 round 2): one free of `#[stdin, p]`, the promise reached first; with the drain-end hook before the deferred resolutions, the context waited for stdin's writer, whose child waited for the reader, which waited for the promise: a hang | RtDeferredResolveBeforeHandOff |
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
| RtSplitMaps | rv7/opts O7Map; rv6/lower check 5 (SMapA); written for `split-map-loops`, deleted with rule 1 (the maps now run on the one array type) |
| RtConvUniform | rv7/repr R7Conv |
| RtReprFuzzCtx | rv7/repr fz/Gz5 (gen2.py) |
| RtReprFuzzTypes | rv7/repr fz/gen.py, seed 7, 6 types |

### Compact scalar arrays: the `RtCArr*` corpus

Tests for compact scalar arrays: an `Array S` whose element type `S` is a
scalar is to be stored as a vector of `S`'s storage kind (u8: `UInt8`,
`Bool`, enumerations; u16: `UInt16`; u32: `UInt32`, `Char`; u64: `UInt64`,
`USize`; f32: `Float32`; f64: `Float`), unless the program's flows connect
it to an array of unknown element type, to another kind, or to a cast. The
tests check behaviour, not layout: each output must equal native's with
today's boxed arrays and with compact arrays. Peak memory and allocation
growth are checked by `alloc-check.sh` (the test's `.alloc`). On dev
e4a1e5f (boxed arrays) every output equals native's.

| test | what | `alloc-check` on dev |
|---|---|---|
| RtCArrKinds | every storage kind (`UInt8`, `Bool`, an enum, `UInt16`, `UInt32`, `Char`, `UInt64` and `USize` at and above 2^63, `Float` and `Float32` with NaNs, -0.0, infinities, a denormal) through the operations of typed code: `push`, `set!`, `get!`, `getD`, `uget`/`uset`, swaps, `pop`, `back`, `extract`, `++`, `reverse`, folds, `any`/`all`, lists, `ofFn`, `replicate`, `range`, searches, `qsort`, `insertionSort`, `binSearch`, subarrays, inserts and erases, `get!` out of bounds | — |
| RtCArrMaps | `map` within a kind and across kinds (`UInt64` to `UInt8`, `Float` to `UInt64` by value and by bits, and others), to and from boxed element types, `mapIdx`, `mapFinIdx`, `mapM` in `IO`, `StateM` and `Except`, `mapMono`, `zip`, `zipWith`, `unzip`, `filterMap`, `flatMap`, a map repeated on a unique array, shared sources printed afterwards | — |
| RtCArrShare | copy on write for every kind: 13 operations on a shared array, the old array printed after the new one; snapshots of a unique array updated in a loop; `dbgTraceIfShared` on a shared and a unique array of each kind; constant arrays of each kind (literals, a computed table, a literal in a loop) updated by their users stay unchanged | — |
| RtCArrInPlace | a unique array of 1000 elements of each kind updated n times by `set!`, `uget`/`uset`, a swap, `push`/`pop` and a same-kind `map`: no copy (`RtCArrInPlace.alloc`, one line per kind) | passes |
| RtCArrContainers | scalar arrays in `Prod`, `Option`, `List`, `IO.Ref`, `Task`, `Thunk`, a structure, `Except`, `StateM`, `Std.HashMap`, `Array (Array UInt8)` (in place and through a shared row), an `Array (Array Float)` matrix product, three levels of `Array Bool` | — |
| RtCArrGeneric | user functions polymorphic in `α` that read and write `Array α`, class-generic folds, arrays through function values of generic type, existential packages beside typed arrays of the same kinds, polymorphic recursion from `Array UInt8` and `Array Float` | — |
| RtCArrColumn | a dependent column `Array ty.denote` for every kind (as RtUniformUpdates): updates, maps within and across kinds; typed arrays put into and taken out of a column, and typed arrays that never meet one | — |
| RtCArrAttach | `attach`, `attachWith`, `unattach`, `pmap` on every kind; `Array.modify` (its `unsafeCast ()` placeholder) unique, shared and out of bounds; `Subtype` arrays; proofs used for indices | — |
| RtCArrCast | `unsafeCast` between arrays that native Lean represents alike (`UInt64`/`Float` bits, `UInt64`/`USize`, `UInt8` as `Bool`, `UInt16`, `UInt32`, `Char`, `Nat`, an enum as `UInt8`), a view updated while the original is used; `Array UInt64` as `Array UInt8` has no defined native result and is not tested | — |
| RtCArrFields | a field `Array α` boxed in an inductive used with a compact array: `Subarray UInt64` values in a list read by a function not inlined, a subarray of an array updated afterwards, `Vector UInt16` set and read, a user structure with an `Array α` field at `Float` and at `Nat`, a `Subarray Nat` beside them | — |
| RtCArrDepUniverse | an array of boxes that arrives in a box read at a scalar array type where no binder has that type (review F1): a type-code universe (`Ty.denote`) read by externs at `UInt64`, by `ByteArray.mk` and `FloatArray.mk`, and an array cast by a proved equation read by externs and put into a structure field `Array UInt64` | — |
| RtCArrBytes | `ByteArray.mk`/`.data` and `FloatArray.mk`/`.data` round trips, also of shared arrays updated afterwards on either side; `ByteArray` operations next to `Array UInt8` ones; UTF-8 through `Array UInt8` | — |
| RtCArrPresize | lean-zip's presize (`ByteArray.mk (Array.replicate n 0)`) filled in place, and an `Array UInt8` filled by `uset` then converted, n = 5 * 10^7: peak memory at most 120000 KB (`RtCArrPresize.alloc`; its bytes may grow twice as much as native's: leanrt's size check of a big `Array.replicate` mallocs and frees an untouched block of the native size, which the counter counts) | passes with compact arrays: peak 56496 KB (bytes) and 56624 KB (array), native 448312 and 448572 KB; on dev e4a1e5f (boxed) it failed the bound: 447660 KB |
| RtCArrSieve | the sieve of Eratosthenes over an `Array Bool` of 5 * 10^7 + 1 elements: peak memory at most 120000 KB (`RtCArrSieve.alloc`, with the same factor 2 for bytes) | passes with compact arrays: peak 60524 KB, native 405372 KB, bytes 1.24 times native's; on dev e4a1e5f (boxed) it failed the peak bound (398512 KB) and the bytes bound (2.1 times native's) |
| RtCArrGenericFields | fields that hold arrays inside another type (hunt HCA-02): `Matrix Float` (`rows : Array (Array α)`) built and multiplied, `Rows UInt8` (`List (Array α)`), `Opt UInt64` (`Option (Array α)`, a value from 2^63), `Grid UInt16` (`Array (List (Array α))`), and a structure with `Option (Array α)` read through a dependent type `B b`; every kind stays compact (`L2R_DEBUG=1`; on dev 70a466d `u8`, `u64` and `f64` were off) | — |
| RtCArrGenericFieldsDep | the other side of RtCArrGenericFields: generic code builds or reads `List (Array α)` (a type-code universe read at `UInt64`, an existential payload stored at `UInt8` and `Float`, a dependent pair read at `UInt16`); the whole-program check turns those kinds off | — |
| RtCArrSharedNil | one `List.nil` that mono CSE shares between `List (Array UInt8)`, `List (Array Float)` and `List (Array UInt64)` (hunt HCA-01), `Option.none` and `Except.error` beside values of the same types that hold compact arrays; every kind stays compact (on dev 70a466d `u8`, `u64` and `f64` were off) | — |
| RtCArrBoxedAny | a compact `Array UInt64` that arrives in a box (an opaque `T b`) read by `Array.size` and `Array.toList` at `lcAny` through a proved cast: the check turns `u64` off (on dev 70a466d it stayed on and leanrt converted the array at each read, the safety net) | — |
| RtCArrExtern | externs of the program with Lean definitions over `ByteArray`, `Array UInt8`, `Array UInt64` and `Array Float` (lean-zip's `ugetUInt32LE` and `presize` shapes) and an extern bound to an `@[export]` definition, with `unread-fields` on: the program does not cast, every kind stays compact and `unread-fields` runs (`RtCArrExtern.l2r-debug`; on dev 5604d38f every extern of the program counted as a cast and turned every kind off) | — |
| RtCArrMatch | a `match` that takes an array apart into its list (`⟨l⟩`, `let ⟨xs⟩ := a`; hunt HARR2-01) at `Bool`, `UInt16`, an enum, `Char`, `UInt64` (from 2^63), `Array UInt8` and in a generic function at `Float`; a `match` on a `Thunk` and a `Task`; element types that are no scalar or that mono changes (functions, `Unit`, `Fin`, `Option`, `String`, `Int8`, `Float32`, a subtype, `Vector`) and a `match` on `extract`'s result: every kind stays compact (`RtCArrMatch.l2r-debug`; on dev 0b6ef980 every kind was off) | — |
| RtCArrMatchPatterns | array literal patterns, `a = #[]`, derived instances of a structure with array fields, and one `⟨xs⟩` pattern on an `Array Float`: every kind stays compact (`RtCArrMatchPatterns.l2r-debug`; on dev 0b6ef980 the `⟨xs⟩` pattern turned `f64` off) | — |
| RtCArrMatchBytes | `match b with \| ⟨arr⟩` on a `ByteArray` and a `FloatArray`: the data read, updated, mapped and rebuilt, `.data` of a byte array that stays in use, and both fields of a structure taken apart in a loop (`flatten-structs`): every kind stays compact (`RtCArrMatchBytes.l2r-debug`; on dev 0b6ef980 `u8` and `f64` were off) | — |
| RtCArrMatchBytesMap | `match b with \| ⟨arr⟩ => ⟨arr.map (· + 1)⟩` on a `ByteArray`, the program's only `Array UInt8`: the map runs in place over the bytes and every kind stays compact (`RtCArrMatchBytesMap.l2r-debug`; on dev 0b6ef980 the bytes were copied into boxes and back, and `u8` was off, also for an unrelated `Array Bool`) | — |
