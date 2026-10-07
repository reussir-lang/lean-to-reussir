# Testing: checks of costs, determinism and representation changes

Special cases in the test tooling that checks more than a program's
output: allocations against native Lean, determinism and locality of the
translation, and the cost of the uniform layout for programs that do not
use it, and the corpus of dependent-type programs. The checks themselves
are listed in [`../../tests/README.md`](../../tests/README.md)
("Representation changes" and "Dependent types"); the runtime tests of the
suite are `tests/runtime/RtRepr*.lean` and `tests/runtime/RtDep*.lean`.
Paths are relative to the repository root.

### Allocations are counted by wrapping mimalloc at link time

- **What:** `tests/runtime/alloccount/alloccount.c` defines `__wrap_` versions
  of mimalloc's allocation entry points (`mi_malloc`, `mi_malloc_small`,
  `mi_zalloc`, `mi_zalloc_small`, `mi_calloc`, `mi_mallocn`,
  `mi_malloc_aligned`, `mi_zalloc_aligned`, `mi_realloc`,
  `mi_realloc_aligned`) that count calls and requested bytes and call the
  `__real_` one; both builds link it with `-Wl,--wrap=…`
  (`alloccount.sh`: `AC_LEANC` for `leanc`, `AC_RRC` for rrc through
  `L2R_RRC_FLAGS`). A destructor prints `alloccount: allocs A reallocs R
  bytes B` to stderr at exit. The file includes only the compiler's own
  headers and declares `write` itself: Lean's `leanc` has no C library
  headers.
- **Why:** the conversion counter (`L2R_COUNT_CONVERSIONS`) exists only in
  lean2rr's build and distorted it (blowup audit BA-00: it broke the
  conversion machine's loop); counting at the allocator measures both
  builds the same way. Both runtimes link mimalloc statically (Lean's
  libleanrt; Reussir's runtime crate `reussir-rt`, also Rust's global
  allocator), and `--wrap` redirects only references between object
  files, so mimalloc's internal calls are not counted twice. Bytes are
  counted because a copy of a whole array is one allocation (C03R-01,
  BA-13 are quadratic in bytes only).
- **Where:** `tests/runtime/alloccount/alloccount.c`, `alloccount.sh`;
  used by `tests/runtime/alloc-check.sh` and
  `tests/runtime/paynothing-check.sh`.
- **Remove only if:** a runtime stops using a statically linked mimalloc
  (then the checks fail with "no allocation count"), or the linker has no
  `--wrap` (ELF linkers only).

### A run stops at an allocation limit

- **What:** when the environment sets `ALLOCCOUNT_MAX_ALLOCS` (allocations
  and reallocations) or `ALLOCCOUNT_MAX_BYTES` (bytes requested), the
  counter (`alloccount.c`, read by a constructor before `main`) stops a
  run that goes past either: it prints `alloccount: stopped at the limit:
  allocs A reallocs R bytes B` and exits with status 125. `alloc-check.sh`
  sets both for every run (5 × 10^7 allocations and 1 GiB by default;
  `ALLOC_CHECK_MAX_ALLOCS`, `ALLOC_CHECK_MAX_BYTES`) and reports such a run
  as "stopped at the allocation limit".
- **Why:** a safety net. Each test's sizes are chosen so that a blowup of
  today's lean2rr shows as allocation growth and stays well under 1 GB
  and a few seconds (an exponential case at n = 18, not at n = 28, where
  copying every path of a shared tree needs tens of GB; the large inputs
  are kept outside the suite). The bytes requested bound the memory a run
  can hold, so a run that blows up more than expected stops after seconds
  instead of filling the memory cgroup. Native runs stay far below.
- **Where:** `tests/runtime/alloccount/alloccount.c` (`count`,
  `alloccount_limits`), `tests/runtime/alloc-check.sh` (`MAX_ALLOCS`,
  `run_one`).
- **Remove only if:** never; a test that must allocate more lowers its
  sizes, or the run raises the limits through the environment.

### Allocation growth, not allocation counts, is compared with native

- **What:** `alloc-check.sh` runs each test at two sizes and compares the
  growth: `L_large − L_small ≤ FACTOR × (N_large − N_small) + OFFSET` for
  allocations, and the same with `64 × OFFSET` for bytes, per line of
  `NAME.alloc`; optionally the large run's peak RSS against native's.
- **Why:** the two runtimes allocate very differently at startup (native
  Lean about 11000 allocations before `main`, lean2rr about 100), and in
  steady state by a constant factor (boxes, wrappers); the property to
  keep is "linear where native is linear" (the audit's quadratic and
  exponential cases). The startup cancels out in the difference.
- **Where:** `tests/runtime/alloc-check.sh`; `tests/runtime/Rt*.alloc`.
- **Remove only if:** never; adjust a test's FACTOR when a known constant
  factor changes.

### An `.xfail` can mark only the allocation check

- **What:** a `NAME.xfail` whose first line starts with `alloc-check:`
  marks only `alloc-check.sh`'s check as known to fail; `run.sh` skips such
  a file and expects the output to match native. Every other `.xfail`
  applies to both scripts.
- **Why:** the audit's cost findings give native's output; only their
  allocations grow too fast. One marker per test, with the reason and the
  fixing branch (or the layout redesign), keeps them visible in the lists
  of known failures.
- **Where:** `tests/runtime/run.sh` (the `.xfail` test),
  `tests/runtime/alloc-check.sh`.
- **Remove only if:** the tests it marks pass (each fix removes its
  test's `.xfail`).

### Canonical fingerprints ignore lean2rr's numbering

- **What:** `tests/runtime/rr-fingerprint.py` splits the generated part of
  a `.rr` file (after `// ---- generated types ----`) into items and hashes
  a canonical text of each: local names renamed per item in order of use;
  numbered types (`T_List_15`, `L2RRef245`, `Tuple12`, `L2RConvK827`),
  numbered helpers (`l2r_zero_836`, `l2r_vconv_301`, `jp_77`) and Lean
  instances (`l_f___l2r_1_`) replaced, where they are defined or used (also
  inside longer names, without the length prefix `13n` of a function
  type's name), by a label of the name without its number and a hash of
  the canonical definition, refined over four rounds; numbered
  constructors (a state machine's `j123`) named by their fields and rank;
  string literal indices replaced by the literals, once cells by their
  rank in the item; the payload numbers of `Box` (where a box is made or
  taken apart, where an unboxing compares a word's number, in an arm on a
  number, in the program's releases `l2r_any_rel_<n>` and their table)
  replaced by the label of their type, which the release
  `fn l2r_any_rel_<n>(x : T)` gives.
- **Why:** `fresh` (LowerBase.lean) numbers types, helpers, constructors
  and locals with one counter for the program, the payload numbers of
  `Box` follow the order in which Stage 4 boxes types, and Stage 1 numbers a
  declaration's instances in the order it finds them
  (`freshInstName`): a definition added anywhere shifts names in code it
  does not touch, so a plain diff cannot tell a real change from a
  renumbering.
- **Where:** `tests/runtime/rr-fingerprint.py` (`FRESH_FN`, `INST`,
  `Program`); new numbered name families need a pattern there.
- **Remove only if:** lean2rr emits canonical names itself (a sorted,
  canonically named output was asked for by the redesign's reviews).

### The determinism check adds an entry point, not a call in `main`

- **What:** the variant of each program appends a structure of two numbers,
  a recursive function over it that uses only `Nat` arithmetic, and an
  entry point `l2rDetRoot` with `main`'s type that runs `main` and prints
  the function's result; it is translated with `--root l2rDetRoot`.
  Functions named `l_main___*` are not compared.
- **Why:** a call added inside `main` would change `main`'s code and its
  specializations. A first version of the added function folded an
  `Array String` with a sum of lengths: Lean's specializer reused the
  program's own specialization of that fold (same lambda), so the
  "unrelated" code added a typed caller and `uniformParams` stopped
  making that helper's parameter uniform (the C03R-01 shape), which is
  sharing, not non-locality.
- **Where:** `tests/runtime/determinism-check.sh`.
- **Remove only if:** never.

### A known locality failure: join-point parameter order

- **What:** `determinism-check.sh` lists RtTaskConvSync in `KNOWN`
  (XFAIL): with the unrelated definition, a join point of its `check` gets
  its parameters in another order from the mono phase (`--emit mono`: the
  same variables with other `_uniq` ids), so the join point's tuple type
  and `check`'s code change.
- **Why:** Stage 2 runs Lean's passes over the whole program in one
  session, so one counter draws the unique ids, and some order (likely a
  hash-ordered set of free variables) follows them. Results are not
  affected; a golden comparison of generated code is.
- **Where:** `tests/runtime/determinism-check.sh` (`KNOWN`).
- **Remove only if:** the order no longer depends on the ids (the check
  then reports XPASS).

### Pay-nothing baselines

- **What:** `tests/runtime/paynothing/NAME.fp` records, for programs
  without values of unknown type, the pay-nothing counts of
  `rr-fingerprint.py show` (conversion helpers and uses, box constructions
  and the program's pointer payload types of `Box`), the allocations and bytes of a run at a
  fixed size (lean2rr's, with native's beside them), and every item's
  canonical hash. `paynothing-check.sh` fails when a count or the
  allocations (1% plus 100) or bytes (1% plus 10000) grow, and lists the
  changed items; `--update` rewrites the baselines.
- **Why:** a redesign of the layouts must not make programs that never
  cross layouts slower (review DRP-10: "no new conversion, no new clone,
  no extra allocations", rather than byte-identical output, since a
  redesign may retype positions that are never crossed).
- **Where:** `tests/runtime/paynothing-check.sh`,
  `tests/runtime/paynothing/`.
- **Remove only if:** never; update the baselines after an intended
  change, saying why in the commit.

### Sharing is checked by memory, not by addresses

- **What:** RtDepShareDag, RtDepShareShapes and the DAG cases of the
  shared corpus print depths, leaves and sums along one path. That shared
  values stay shared is checked by `alloc-check.sh` at n = 16 and n = 28
  (with `rss`): a copy of every path is 2^n cells.
- **Why:** `ptrAddrUnsafe` and `ptrEq` may give other answers through
  lean2rr than natively (site rule 7, plan §10), so an address comparison
  is not an output both builds must share. The branch fix-conv-sharing
  compared addresses in its tests (RtConvShareDag, RtConvShareShapes);
  these tests are those programs without the address checks.
- **Where:** `tests/runtime/RtDepShare*.lean`, `RtDepShare*.alloc`.
- **Remove only if:** never.

### The timing tests follow Lean's own arities

- **What:** RtDepEraseTiming prints a trace in each body whose parameters
  include types, and its expected output (stdout and the traces on stderr)
  is native's. Lean 4.34 gives every lambda and every definition the full
  arity of its type, also through a non-reducible definition of a function
  type (`fun α => let c := work k; fun xs => …` is one function of `α` and
  `xs`: `work` runs at each application to a list); it merges equal
  applications (`f ◾ ◾` twice is one call) and extracts closed terms.
- **Why:** these are the native counts that rule 4 must keep. A value that
  completes before the end of its static type comes only from a partial
  application before trailing type parameters (`fx 3`, `endT 2 Nat`) or
  from a type family that unfolds to a function type at the use site
  (`mkW true : (α : Type) → T3 true`, used as `(α β : Type) → Nat`); the
  test has both.
- **Where:** `tests/runtime/RtDepEraseTiming.lean`.
- **Remove only if:** never; when Lean's compiler changes, the native
  counts change and the test follows them.

### The shared cases are combined, one namespace each

- **What:** `tests/runtime/RtDepX*.lean` hold the cases of the shared
  dependent-type corpus (programs another translator's team wrote and
  checked against native Lean), about eleven per test. Each case's code
  is in a namespace named after its case id; its `main` is `caseMain`; a
  declaration `T.f` whose `T` the case does not declare is rooted
  (`_root_.T.f`, so that `x.f` still finds it); a case's own `_root_.x`
  names its namespace. The test's `main` runs each case with that case's
  arguments, after a line `-- <id>` (and prints `exit <code>` after a
  `main : IO UInt32`). A case that exits with another code than 0, reads
  stdin, has a global effect (`initialize`, `@[export]`, syntax) or is
  checked at a large size is a test of its own (`RtDepX<id>`), at a size
  that keeps dev's blowups small (the large inputs stay in the shared
  corpus). Left out: exact duplicates of existing tests (A936 is
  RtProcess, A1028 is RtCseFnResult) and the translation scaling cases
  (A1094 and D71TesterT24E, T24F, T24H: existentials at every pair of 12,
  33, 8 and 17 types, whose builds take 4.5 GB or more on dev), which
  RtDepXPairs keeps at five types. A case that fails on dev is a test of
  its own with an `.xfail` (A833, removed once it passed) or, for a
  documented difference, its expectation files (D71TesterT23, removed once
  it printed as natively).
- **Why:** one test per case would add about 320 builds to every run of
  the suite; a combined test is one build. Each case's section of the
  output was checked against that case's own native output before it was
  combined (the only differences are `deriving Repr` printouts, which name
  the namespace).
- **Where:** `tests/runtime/RtDepX*.lean`, `.args`, `.alloc`.
- **Remove only if:** never; a case that fails is split out into its own
  test with an `.xfail`.

### An application test compares the files it writes, at settings that give one result

- **What:** `tests/apps/raytracer/run.sh` builds lean4-raytracer from a
  copy of its Lake package in the build directory (`lake build`, then
  `scripts/l2r.py Main --lean-path <copy>/.lake/build/lib/lean`). It
  compares the PPM image that each build writes, byte for byte, in
  addition to stdout, stderr and the exit code. It runs only THREADS = 0
  (the main thread, a change of ours to the program; see its `NOTICE`)
  and THREADS = 1 (one task).
- **Why:** the image is the program's result; its stdout is only progress
  lines. All tasks of the program take random numbers from one
  `IO.stdGenRef`, so with two or more tasks native Lean gives another
  image at each run. The copy keeps `.lake/` out of the source tree.
- **Where:** `tests/apps/raytracer/run.sh`, `tests/apps/raytracer/NOTICE`.
- **Remove only if:** never; a new setting must give one image natively
  (check two native runs) before the test uses it.
