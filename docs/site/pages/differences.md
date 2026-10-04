# Known differences

<p class="lead">Where a lean2rr build can behave differently from the native
build of the same program. This is a readable summary of
<a href="repo:docs/translation-plan.md">translation plan</a> §10, which has every
item with its examples and tests. An index of all §10 items is at the end of
this page.</p>

<div class="note" markdown="1">
**How to read this page.** Most items show only through unsafe functions,
timing, or errors. A program that uses `Init` and `Std` in the usual way
gives the same output. Each item says what differs and when you can see it.
</div>

## Not supported

| What | What happens |
|---|---|
| A program with its own `@[extern]` C code | Today the build fails in rrc with an unknown function. The rule (implemented, in review): the extern is compiled from its Lean definition and its C code is ignored; an extern with no Lean definition is refused at translation with a clear message. See [the extern rule](index.html#the-extern-rule). Support for calling C is parked. |
| `Lean`'s externs implemented in C++ (`Expr.mkData`, `evalConst`, `Dynlib`, the LLVM bindings) | The same: an unknown function at the rrc build. Data structures from `Lean` work. |
| A constant that `main` never uses but that reaches an unsupported extern | The whole program fails to link, because every constant is translated (native Lean evaluates every constant at startup). |
| A program module named `Init.*`, `Std.*`, `Lean.*`, `Lake.*` or `L2RShim.*` that is not the toolchain's | Rejected at load. lean2rr trusts modules with these names. |

## Identity and sharing

lean2rr does not copy native pointer identity or sharing.

- `ptrAddrUnsafe` answers the address of a value's cell in its own
  representation, or a word computed from a scalar. So `ptrEq`, `ptrEqList`
  and `withPtrAddr` can answer otherwise than natively: for a value and its
  conversion to another representation, two boxings of one value, a wrapped
  function value, a converted thunk or task.
- Equal `UInt64`s, `Float`s and small numbers are `ptrEq` (natively each
  boxing of a `UInt64` is a new cell).
- `ptrEq` answering `true` still means equal values. `ST.Ref.ptrEq` is exact.
- `isExclusiveUnsafe` answers `false`. `shareCommon` shares nothing.
  `dbgTraceIfShared` reads lean2rr's own counts.
- **When you can see it:** only through these unsafe or debug functions.

## Tasks and concurrency

All tasks run on one thread, as one of the schedules native Lean can
produce. See [Runtime](runtime.html#tasks-and-the-scheduler).

- A loop that polls a reference set by another task, with no sleep and no
  output, never sees the change. With a sleep in the loop, it does.
- A context that computes without output or blocking delays the others.
  Output ordered by sleeps comes in time order only when the code between
  outputs is shorter than the sleeps.
- `IO.waitAny` does not pick the fastest of several unfinished tasks.
- A task needed by `main` runs at once, before tasks queued earlier.
- A blocking system call (reading a pipe, waiting for a child) blocks every
  task. Name resolution (`getaddrinfo`) runs at once.
- `IO.getTID` inside a task is main's id plus a worker number.
- **When you can see it:** in programs whose output depends on timing races
  between tasks. Natively such output is a race too.

## Startup and evaluation

- **Startup order of unrecorded constants.** The `.olean` does not record
  the order of some constants: members of a `mutual` block that do not use
  each other, some names that macros make. lean2rr chooses an order. You can
  see it only when such constants trace or panic.
- **Dictionary rebuilding.** lean2rr specializes a callee on every static
  dictionary, also where Lean's specializer does not. Instance code can then
  run more or fewer times than natively. You can see it through traces or
  panics in instance code, or as extra time.
- **Merging after erasure.** Lean's mono `cse` can merge two calls at
  different types into one. lean2rr does that too, except in two shapes
  (results that differ at a function type; a call inside a local function
  merged with one outside). There both calls run, and a trace or panic in
  them prints twice. Test `RtCseFnResult` is marked `.xfail` for this.
- **Compiler options** of the program's modules (`set_option compiler.…`)
  are not in the `.olean`. lean2rr runs Lean's passes with the defaults.
- **Order of panics in pure code.** When several pure computations panic,
  their messages can come in another order: closed-term extraction can group
  them differently in lean2rr's instances.

## Resources and releases

- **Order of releases in one free.** Natively a freed value releases what it
  holds last pushed, first released. lean2rr does the same inside every free
  that starts at a container. When user code drops a record of handles by
  itself, Reussir's inline release goes in field order: a list of handles
  `L0 … L7` closes `L0 L7 L6 … L1` (natively `L7 … L0`).
- **Release time of borrowed parameters.** lean2rr emulates Lean's borrowing
  for values that can hold a resource, with Lean's inference run on
  lean2rr's instances. Where Lean infers its own specializations
  differently, the release time follows lean2rr's instance. Resources inside
  closures and thunks are released at their last use.
- **Promises released inside a free.** Their `sync` dependents run when the
  whole free is over, not when the free reaches the promise. Without Reussir
  patch 0040, a free that Reussir's glue started ends unseen, and the
  dependents run at the next output, block or task question.
- **Child processes.** `IO.Process.output` reads both pipes together.
  Natively `Child.pid` leaks the child's pipes; lean2rr closes them.

## Casts that read addresses

`unsafeCast` of an object to a number natively gives its address, which
changes on every run. lean2rr gives a deterministic word with the
properties of an address: `2^44 + 8i` for constructor `i`, `2^44` for other
objects, the low bits of the value for a big number. A cast with no native
meaning (a number read as a constructor with fields) panics with `INTERNAL
PANIC: unreachable code has been reached`, where native Lean crashes or reads
garbage.

## Limits

- **Out of memory.** lean2rr ends every failed allocation with `INTERNAL
  PANIC: out of memory` and exit 1. Natively the end depends on where it
  happens (GMP and `getLine` abort with 134). The two builds use different
  amounts of memory, so they run out at different points. A `Nat` or `Int`
  result too big for GMP (more than 2^31 limbs) ends at once with `INTERNAL
  PANIC: out of memory`, where native GMP raises SIGFPE (LB-05, below).
- **Stack depth.** Frame sizes differ, so the depth of a stack overflow
  differs. The report itself is native's (`Stack overflow detected.
  Aborting.`, exit 134). lean2rr adds no recursion of its own: conversions,
  list folds and the constant walk are loops, and frees use a stack of
  pending work.
- **Build time.** rrc compiles about 80 small functions per second. A
  program with thousands of constants takes minutes (natively seconds).

## Runtime details

- `IO.getNumHeartbeats` is 0. `dbgStackTrace` prints nothing. A panic's
  backtrace line is `(stack trace unavailable)`.
- The `errno` after a sticky handle error can differ.
- `ShareCommon.Object.eq` holds at most for the same cell.
- The Windows-only time zone functions fail, as natively on other systems.

## Costs (time and memory, not results)

| Cost | Why |
|---|---|
| Structural conversions rebuild a value as a tree | sharing is lost; a value converted at each call costs O(size) per call |
| `Array.map` that changes the representation | the input and the new result live together until the map ends |
| `ElemBox` for array elements that cannot cross the FFI | one allocation per element |
| Reads take their container owned | an increment and a release per read, unless LLVM cancels them |
| One-block arrays | a 16 MiB payload (a hash table's 2^21 buckets) becomes a huge mimalloc segment, freed late |
| Constants read in a loop | a once-cell check at each read |
| No borrowed parameters | a traversal that keeps the nodes it visits writes counts native Lean only reads (about 1.5×) |

## Lean bugs we do not reproduce

<div class="rule" markdown="1">
lean2rr does not copy bugs of Lean's own runtime. A suspected bug becomes
an intended difference only after a judge confirms it: the C source lines,
why it is wrong (the C standard, POSIX, Lean's documentation, data loss or a
crash), and a minimal native repro. lean-runtime's `docs/lean-bugs.md`
lists the confirmed ones (entries `LB-nn`).
</div>

{{gen:leanbugs}}

## Index of plan §10

Generated from the translation plan: every group and item of §10, so that
this page can be checked against it.

{{gen:diffindex}}
