# Runtime

<p class="lead">What every lean2rr build contains besides the program's own code.
Sources: the <a href="repo:runtime/README.md">runtime README</a>,
translation plan §5.8 to §5.14 and §6, and the implementation notes'
<a href="repo:docs/implementation/tasks/README.md">tasks</a>,
<a href="repo:docs/implementation/startup/README.md">startup</a> and
<a href="repo:docs/implementation/ownership.md">ownership</a> areas.</p>

## Layers

{{svg:layers}}

| Part | Language | Role |
|---|---|---|
| `runtime/prelude.rr` | Reussir | Prepended to every program. Defines the runtime types and one function per Lean extern, named after the extern's C symbol (`lean_nat_add`). Fast paths are inline Reussir code; the rest calls `leanrt` or `lean-runtime`. |
| `runtime/leanrt/` | Rust | Linked into every program. lean2rr's representations: big numbers (GMP), strings, arrays, cells, once-cells. The glue to lean-runtime: its rules, its IO (handles, the last-error slot), its scheduler (the task objects, the one `unsafe` step of a context switch, the current standard streams) and its event loop. One crate, so one copy of all global state. |
| `third_party/lean-runtime` | Rust | The shared crate, a git submodule pinned by commit. Lean's runtime rules, the IO, the startup, the scheduler with its wait cores, `Std.Sync`, the event loop and the networking. The driver builds it with cargo. |
| `lean2rr/L2RShim.lean` | Lean | lean2rr's own Lean library: the `Std.Internal.UV` externs (timers, sockets, name resolution, signals), `Std.Time.Timestamp.now`, `ShareCommon.Object.eq`/`hash`, over primitives of lean-runtime's event loop. Exported under the C symbols and compiled with the program. |
| generated glue | Reussir | Made by lean2rr for externs over Lean-defined types: `IO.Error`, `Option`, `List`, processes, references, tasks. |

Semantics follow Lean 4.34's C runtime (`lean.h`, `src/runtime/*.cpp`).
A comment at each function names the C function it follows.

### Calling convention

- The extern `lean_xxx` is the prelude function `lean_xxx`. Its parameters
  are the extern's mono parameters without the erased ones and without the
  IO world.
- Every function consumes its arguments (Reussir's rule). A function that
  only reads a handle releases it. An array or string read releases it
  first, before the index check.
- A function never changes a value in place unless the value is unique
  (count 1). The cells of references, thunks and tasks are mutable by design.
- A polymorphic extern takes explicit storage type arguments:
  `lean_array_push<E>(arr, x)`.
- A runtime function cannot build a Lean-defined type (it does not know the
  generated names). So generic helpers take the result type's constructors
  as arguments, and lean2rr's glue makes a single call.

## Memory management

**Reference counting and reuse are Reussir's job.** Reussir inserts every
increment and release (Perceus), and its token reuse builds a new cell in
the memory of a cell that dies at the same point. lean2rr only arranges the
code so that this works: it keeps "take apart" and "build" in one function,
and several optional passes help token reuse (see
[Optional passes](passes.html)).

{{svg:freestack}}

- **Containers of the runtime** (arrays, string blocks, task and thunk cells)
  are `leanrt` types. Their `Drop` frees the last reference through the same
  per-thread stack that Reussir's drop glue uses (local patch 0014). So a
  value deep through records and containers is freed at a bounded depth.
- **Order of releases.** File handles close (and flush) and promises resolve
  in Lean's order: last pushed, first freed. An array set or pop frees the
  record that it removes the same way. Two differences stay: the first
  cell of a free that user code starts at a record, and a cell below the
  first one whose last record field comes before an array field (plan
  §10).
- **Reference `set`.** `l2r_rc_set` stores the new value first, then releases
  the old one as `lean_dec` does. So code that the release runs (the `sync`
  dependents of a promise it drops) sees the new value.
- **Borrowed parameters.** Reussir has none. Natively a parameter that Lean
  borrows is released by the caller after the call. Only resources can show
  the difference (a file handle still open, a pipe not yet at end of file).
  So for a program that creates resources, lean2rr runs Lean's own borrow
  inference and keeps such arguments alive until the call returns.

## Tasks and the scheduler

All tasks run on one thread, on the scheduler of the shared crate
lean-runtime (its `sched` module). A task is *deferred*: it runs when its
value is needed, when the running code blocks, or when `main` returns. This
is one of the schedules that native Lean can produce. Why not run a task at
once? A task can wait for something that `main` does later: run at
creation, it would never finish.

A pending task runs at the first of these events:

1. `IO.wait` or `Task.get` of it, when a free worker would start it;
2. the running code blocks and a worker is free;
3. an output, when the task waits for 5 ms or more and a worker is free;
4. the program polls it (`IO.hasFinished`) after time has passed;
5. `main` returns: the queued tasks run in the order of Lean's task manager.

**A task that a worker starts during the wait.** In event 1, the waiting
context runs the task on its own stack. Before the scheduler decides, it
lets the worker take the work that the worker would have taken by then. If
the worker takes the awaited pure task at that time, the waiting context
runs the task. Before switch step 9, the wait did not see that start: the
context waited for a signal that had already gone. If a socket was open,
nothing woke it, and the program did not end (`RtTcp` did not end in
about one run in 20). If a sleep or a timer was pending, the wait
continued until it ended: a `Task.get` could wait for an unrelated
`IO.sleep` to end.
The test `RtTaskPickedInWait` checks this case.

**Contexts.** A thread that blocks natively lets other threads go on.
lean-runtime copies that with *contexts*: `main`'s stack, and one stack per
task that it starts (1 GiB, with a guard page). When the running context
blocks, the scheduler chooses:

{{svg:scheduler}}

**What lean2rr keeps.** The rules are lean-runtime's. lean2rr keeps the
glue: the task objects (cells with a generated state), the code that
connects them to the crate's task ids, the one `unsafe` step of a context
switch (with its written proof), and the current standard streams of each
context and of each emulated worker. The generated task code did not
change.

**Waits.** A context that needs a thunk or a constant that another context
computes waits for it. These waits, the reference rule below and the
resolution of promises released inside a free use lean-runtime's *wait
cores* (switch step 6). Their fast paths stay inline in the program's loops
(`tests/runtime/wait-inline-check.sh` checks the machine code).

**Lazy start.** The scheduler starts at the first task, promise,
`Std.Sync` object, timer, signal watcher, socket or name lookup. The lazy
start is lean-runtime's too (switch step 7).

**References in a program with tasks.** lean2rr knows when it translates a
program whether the program can make tasks: the program reaches an extern
that makes a task or a promise (timers and sockets make promises too). Only
then do reference operations do more than read or write the cell. Every
1000th read lets the other tasks go on, so a loop that polls a reference set
by another task ends. While `modify` holds a reference, the other tasks wait
for its store, as in Lean 4.35. A program without tasks pays nothing: its
code is the same, and the scheduler does not start.

**Promises** are runtime objects that hold their task's cell. Dropping the
last reference to an unresolved promise resolves it with `none`, as
natively. When a free releases the promise, the resolution waits until the
free ends (Reussir patch 0040 reports the end). **`Std.Sync`** mutexes
and condition variables are lean-runtime's objects in runtime handles; a
thread that waits blocks its context.

## Input and output

- **IO is lean-runtime's.** Files, the standard streams, the file system,
  processes, the system queries, the startup descriptors and the exit come
  from the shared crate's `io` module. `leanrt` only converts lean2rr's
  values (strings, byte arrays, handles) to the crate's views and back.
- **The stdio model.** Files and the standard streams follow glibc's `FILE`
  function by function (lean-runtime's `io::cfile`): one buffer per handle,
  line-buffered terminals, the same system calls in the same order. So the
  `errno` values are native's. At exit, stdout is flushed first, as natively.
- **Fallible IO.** A runtime primitive records its outcome in a last-error
  slot: nothing, or the crate's `IO.Error`. The glue turns it into `ok` or
  into the `IO.Error` that Lean's own exported builder makes, with libuv's
  kind and message (Lean 4.34).
- **Processes.** `IO.Process` follows `process.cpp`. The crate starts a
  child with `posix_spawn` and does what Lean's forked child does before
  `execvp`. `IO.Process.output` reads both pipes together.
- **IO and tasks.** A read of an empty pipe, a write to a full pipe,
  `flock` and the wait for a child let the other contexts run, as other
  threads natively go on.
- **The event loop** is lean-runtime's: timers, signals, sockets and name
  resolution. It works, but it is not a target now.
- **Standard streams per thread.** A pool task uses the streams of its
  worker, and the worker keeps them for its next task, as a native worker
  thread does. A dedicated task starts with the process's streams, as a new
  native thread does.

## Startup

{{svg:startup}}

- **Entry.** The startup logic is lean-runtime's (switch step 7). Its ELF
  constructor opens native Lean's startup descriptors before Rust's runtime
  starts. The initializers run on the process's main thread (8 MiB stack).
  Then `main` runs on a thread with a 1 GiB stack, which lean-runtime makes.
- **Huge pages.** No constructor of lean-runtime allocates: they run before
  mimalloc's own constructor. So the process's main thread reserves
  mimalloc's first arena with large pages, and the heap of `main`'s thread
  is on transparent huge pages, as natively. From switch step 3 to step 6,
  a constructor allocated first. The heap lost its huge pages, until a
  workaround in `leanrt` restored them. Step 7 removed the allocation and
  the workaround.
- **Constants.** Every zero-parameter declaration of the program's modules
  runs at startup, in Lean's initialization order. Each constant is a
  once-cell. A context that needs a constant that another context is
  computing waits for it, as a native thread waits for a lock.
- **Library initializers.** The `initialize` declarations of `Init` and
  `Std` run at their module's place in the import order, as natively. They
  run also when the program does not use them, because their effects are
  visible. Lean 4.34.0 has one: `IO.stdGenRef`, which reads 8 bytes from
  `/dev/urandom` to seed `IO.rand`. If no file descriptor is free, the
  program stops before `main` with `uncaught exception`, as natively.
- **Other toolchain constants and closed terms** are evaluated lazily,
  once. They are pure, so the time of their evaluation is not visible.
- **Order.** The `.olean` records part of Lean's compilation order. lean2rr
  rebuilds the rest from the source structure (declaration ranges, `where`
  helpers, `mutual` blocks). A few orders are not recorded; see
  [Known differences](differences.html#startup-and-evaluation).

### The walk of a closed term for its tasks

{{svg:persist}}

The walk is a loop over a work list, not a recursion, and it visits each
cell once. So a value 300000 cells deep, or a DAG with 2^40 paths, is no
problem.

## The shared runtime crate

lean2rr uses the shared crate **`lean-runtime`**
(github.com/QueClr/lean-runtime-rs, public). The crate implements Lean's
runtime behaviour once, as a library that a translator of Lean programs
can use. lean2rr switched to it in nine steps, from 2026-10-04 to
2026-10-05; a tenth step (2026-10-06) took faster code from it.

| Point | Decision |
|---|---|
| What is shared | Lean's runtime semantics: hashes, floats, strings, numbers, arrays, IO, the startup, the scheduler. |
| What stays in lean2rr | The representation of values and the memory protocol: lean2rr keeps thin glue over its own layouts, and its hot paths. |
| One runtime | Every runtime function is implemented once, in the crate. lean2rr keeps no copies and no fallbacks. |
| Safety | The default build compiles no `unsafe` code of the crate. A few native behaviours that no safe API can give (the process title, the startup descriptors, the stack-overflow report) are small files behind their own features, each with a written proof (the crate's `UNSAFE.md`); lean2rr enables these features. Other unsafe code comes only through vetted crates (such as nix, rustix, corosensei and mimalloc). A faster unsafe path can come later behind an opt-in `unsafe-fast` feature, with a written proof. |
| Speed | The safe default must be at least as fast as Lean 4.34.0's native runtime. |
| Big numbers | Behind a trait; lean2rr keeps GMP. |
| Tasks | Deferred tasks, polling yield points, Lean's exit behaviour; the stack switch through corosensei. |
| Order | Semantics first, then IO, then the scheduler. Each step must pass lean2rr's test suites. |
| Reuse | Existing runtime code moves into the crate; it is rewritten only where it does not fit. |
| Bugs | Every bug found becomes a test. Bugs of Lean's own runtime are not copied; lean-runtime's `docs/lean-bugs.md` lists them. |

The switch steps:

| Step | What lean2rr takes from lean-runtime since then |
|---|---|
| 1 | the rules for hashes, string positions, floats, fixed-width integers and `libm` |
| 2 | the `Nat` and `Int` slow paths, the array edge rules, panics, the text of numbers |
| 3 | the IO: files, the standard streams, the file system, processes, the system queries, the startup descriptors, the exit |
| 4 | tasks, promises, `Std.Sync`, the event loop, timers, signals, sockets, Lean's stack-overflow report |
| 5 | the last copies of shared functions: the toolchain facts, UTF-8 encoding and lossy decoding, the accessors of `IO.Error`, the clocks, `IO.getTID`, and others |
| 6 | the wait cores: waits for a thunk or a constant, references in a program that creates tasks, promise resolutions put off to the end of a free |
| 7 | the startup: `main`'s thread, the constructor that opens the startup descriptors, the scheduler's lazy start |
| 8 | the panic and exit executor: it carries out a panic's plan (the stream, the flush of stdout, the abort or the exit), and does the internal panic, the uncaught error and `IO.Process.exit` |
| 9 | no new part: a fix in the scheduler (lean-runtime's fixes-8). A wait for a pure task that the worker starts during the wait now runs the task; before, it could wait for ever |
| 10 | no new part: speed (lean-runtime's perf-2). `Float.toString` computes its six decimals exactly with integers; the `Int` rules let lean2rr compute with a word and a big number without a block for the word. lean2rr's own runtime changed at the same step (see below) |
| 11 | no new part: fixes in the signal watchers (lean-runtime's fixes-9 to fixes-11). A one-shot watcher gets one signal, as with `SA_RESETHAND` natively. lean2rr's own runtime changed at the same step (see below) |

Status (2026-10-06): the submodule `third_party/lean-runtime` is pinned at
`dce982d`. `scripts/l2r.py` builds it with cargo (the features `io`,
`proc-title`, `startup-fds`, `sched`, `stack-overflow` and `net`) and links
it with `leanrt` ([runtime README](repo:runtime/README.md), "The shared
crate lean-runtime"). lean2rr keeps its hot paths: the inline
small-`Nat`/`Int` arithmetic, the one-block big numbers with GMP (behind
lean-runtime's big-number traits), the one-block arrays' reads, writes and
pushes, and the current standard streams, which `IO.println` reads at each
call. Each step passed lean2rr's full suite before its merge.

### Fast paths of the runtime library (step 10)

- **`Float.toString`** (lean-runtime) computes the six decimals of a value
  below 2^53 with exact integer arithmetic.
- **`Int` with one small operand** (lean-runtime and `leanrt`). The runtime
  changes the big number in its own block when the block is unique. The
  small operand does not become a big number.
- **`Int` equality.** A small and a big `Int` are never equal, because
  every result is normalized. This comparison does not call the runtime.
- **String equality.** Strings of different lengths are not equal. Two
  references to the same string are equal. Other strings compare their
  bytes.
- **Array sets and pops of records.** A set decrements the record that it
  replaces in line, so LLVM inlines the set into the loop. A set or pop
  that frees the last reference to a record releases its fields last
  first, as Lean does. The record goes on the pending stack as one cell
  (step 11). This costs about 74 instructions per freed record.
- **Block sizes.** Up to 64 bytes, the runtime knows mimalloc's block size
  without a call.

Instruction counts at steps 10 and 11, against step 9 (small sizes):

| Program | Step 10 | Step 11 |
|---|---|---|
| strings | −20.2% | −20.2% |
| liasolver | −14.4% | −14.4% |
| unionfind | +5.0% | +0.8% |
| monadic-interp | −1.9% | −1.9% |
| qsort | −0.15% | −0.15% |
