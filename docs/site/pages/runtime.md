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
- A polymorphic extern takes an explicit type argument:
  `lean_array_push<LAny>(arr, x)`. The elements of an array are boxes.
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
  per-thread stack that Reussir's drop glue uses (local patch 13-b). So a
  value deep through records and containers is freed at a bounded depth.
- **Order of releases.** File handles close (and flush) and promises resolve
  in Lean's order: last pushed, first freed. An array set or pop frees the
  record that it removes the same way. One difference stays: the first
  cell of a free that user code starts at a record (plan §10).
- **Reference `set`.** `l2r_rc_set_ref` stores the new value first, then
  releases the old one as `lean_dec` does, and then the reference. So code
  that the release runs (the `sync` dependents of a promise it drops) sees
  the new value. When the set is the reference's last use, the old value is
  freed before the new one, as natively.
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
change (later, only the call for `IO.cancel` changed).

**A task that the program drops.** When the program drops its last
reference to a task that runs, the task runs to its end. Its end wakes no
waiter, as natively: a native task that nobody holds is deleted without a
notification. The task's job holds a reference of its own while the task
runs. The job releases it when the task has its value, and only then does
the scheduler end the task. This order is the same for pool tasks and
dedicated tasks. `IO.cancel` cancels the task first and releases the
reference after, as the native caller does.

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

**Promises** are runtime objects that hold their task's cell. Only the
first resolution has an effect: the crate's `resolve` examines the promise
and stores the value in one step, after its wait for the context's writer
threads. Dropping the
last reference to an unresolved promise resolves it with `none`, as
natively. When a free releases the promise, the resolution waits until the
free ends (Reussir patch 40-a reports the end). **`Std.Sync`** mutexes
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
- **The close of a stream in a free.** A free must not suspend its
  context. So when the close of a stream cannot write all its bytes, a
  writer thread of the crate writes the rest. At the end of that free, the
  context waits for the writer thread, and the other contexts run (the
  crate's `after_drain`). Natively the close blocks the thread until the
  bytes are written. So the code after the free sees the same state as
  natively.
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
| 12 | no new part: speed (lean-runtime's perf-3). `Float.toString` gives its text as bytes; the character count of a new string takes eight bytes at a time. lean2rr's own runtime changed at the same step (see below) |
| 13 | no new part: fixes of Lean runtime bugs that the crate no longer copies (lean-runtime's semantics-4, io-fixes-1 and fixes-12; LB-36, LB-37, LB-39 to LB-45). A capacity that cannot be reserved gives the empty array; every task priority above 8 makes a dedicated task. lean2rr's glue changed at the same step (see below) |
| 14 | the drain-end hook `after_drain` (lean-runtime's fixes-14), with fixes of the single-thread scheduler (fixes-13, fixes-14), `sin` and `cos` as two calls (semantics-5), and two Lean runtime bugs that the crate no longer copies (io-fixes-2; LB-46, LB-47). lean2rr's glue changed at the same step (see below) |
| 15 | fixes in both schedulers and the network code (lean-runtime's fixes-15), and three Lean runtime bugs that the crate no longer copies (LB-50, LB-51, LB-52). A connect that a shutdown interrupts stays pending until the connection exists. The crate tells the glue which context is the event loop's. lean2rr's glue changed at the same step (see below) |
| 16 | no new part: fixes in the single-thread scheduler (lean-runtime's fixes-16). A task runs on the stack of the task that waits for it only when that stack has the room of a native worker's stack; otherwise it runs on a context of its own. The event loop's context has at least 1 GiB of stack, as libuv's loop thread natively. A spawn's helper thread holds no directory after the spawn |
| 17 | no new part: fixes in the single-thread scheduler (lean-runtime's fixes-17). A pool task that starts on a context of its own holds its worker until it begins, so no more pool tasks run than `LEAN_NUM_THREADS` permits. The owner of a recursive mutex is the thread that `IO.getTID` names, as natively. lean2rr's glue changed at the same step (see below) |
| 19 | no new part: fixes in the single-thread scheduler (lean-runtime's fixes-19 to fixes-21). A task that waits while it keeps its pool worker runs the awaited task on a context of its own, so no more pool tasks run than `LEAN_NUM_THREADS` permits. `IO.Process.forceExit` uses the crate's shared sequence. lean2rr's glue changed at the same step (see below) |

Status (2026-10-07): the submodule `third_party/lean-runtime` is pinned at
`ab1ce21`. `scripts/l2r.py` builds it with cargo (the features `io`,
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
  (step 11). This costs about 74 instructions per freed record. An array
  of a Lean type holds boxes: the last reference to a boxed record goes on
  the pending stack as one cell in the same way.
- **`ByteArray.data` and `ByteArray.mk`** (and those of `FloatArray`).
  The runtime makes the new array at its exact size and converts the
  elements in one loop, as Lean does.
- **Arrays of boxes.** A free of an array has two passes, as in Lean.
  The first pass goes through the elements in index order: it skips the
  immediates and decrements the shared values in line. The second pass
  releases the values whose last reference went, the last one first,
  through the pending stack. So a value that the array holds twice is
  released at its last index. The second pass calls the release of a
  boxed record at once when the stack would pop that record next. When
  no free runs, no work is pending and the first pass keeps one value
  only, the runtime frees the array and then releases that value without
  a step on the stack (not if the value is an array). The order of
  releases does not change.
  A copy of an array copies the words in one block and increments only
  the pointers.
- **Boxed `Float` and `UInt64` values.** The runtime allocates their
  small cells with mimalloc's small-block call and reads a cell in line.
- **Release of a boxed value.** The program has one release function for
  each type that it boxes. `leanrt` keeps these functions in a table by
  type number. When the last reference to a boxed record goes, `leanrt`
  puts the record's cell on the pending stack with the function of its
  type. There is no dispatch on the type number in the program.
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

### Fast paths of the runtime library (step 12)

- **`Int` beyond `int32`.** A big `Int` whose value fits 64 bits is
  released and computed as a small value. The arithmetic, the divisions,
  `natAbs` and the comparisons use the word rules of lean-runtime. The
  result is a small value or a new big number.
- **Substrings.** A string with as many characters as bytes is ASCII. A
  substring of it gets its character count from its length. Other
  substrings count their characters eight bytes at a time.
- **`Float.toString`.** For a finite value below 2<sup>53</sup>, the
  runtime copies the bytes that lean-runtime writes. It does not check
  that they are UTF-8.

Instruction counts at step 12, against step 11 (small sizes; for each
binary, the run with the fewest instructions):

| Program | Step 12 |
|---|---|
| liasolver | −6.5% |
| strings | −2.9% |
| sieve | −1.6% |
| other programs | from −0.1% to +0.15% |

mimalloc's free path changes the counts from run to run. A Rust
allocation asks for 16-byte alignment, and mimalloc can give it a larger
block in a page of 8-byte size classes. Every later free in that page
then takes a slower path. This cost goes up to 8% of monadic-interp's
instructions.

### Lean runtime bugs the crate no longer copies (step 13)

lean-runtime fixes these bugs of Lean's runtime, and lean2rr follows (the
list with each test: [Known differences](differences.html#lean-bugs-we-do-not-reproduce)):

- **Capacities** (LB-37). `Array.mkEmpty c` and the `emptyWithCapacity`
  functions reserve `c` elements when they can. Otherwise they reserve
  nothing. The result is the empty array in both cases, as in the Lean
  definitions. Natively a capacity that cannot be reserved ends the
  process. `Array.replicate` keeps native's ends.
- **Task priorities** (LB-39). lean2rr gives the whole priority to the
  scheduler, and a priority of 2^64 or more becomes 2^64 - 1. Every
  priority above 8 makes a dedicated task. Natively the priority is cut
  to 32 bits: 2^32 - 1 runs the task at once on the spawning thread, and
  2^32 + 1 is a pool priority.
- **`Float.scaleB`** (LB-36) gives `x * 2^i` for every `Int`.
- **IO** (LB-40 to LB-45). `IO.Process.output` writes a large input while
  it reads the output. `getLine` reports only the error of its own call.
  A child that cannot start does not write the parent's pending output.
  Two descriptor leaks are closed. `Std.Internal.UV.System` takes ids and
  priorities whole.

### Streams of the event loop and of dedicated tasks (step 15)

- **The event loop.** Natively libuv's loop is one thread for the whole
  program. Here the loop runs on a context that ends when no callback is
  due, and a new context runs the next callbacks. lean2rr keeps one record
  of the loop's stream cells for all of these contexts. So a stream that
  one callback sets is the stream of the next callbacks, as natively.
- **The end of a dedicated task.** A dedicated task has a fresh set of
  streams. The runtime closes that set at the end of the task, after the
  task's value is freed and after its `sync` dependents run. So the code that the free runs uses the task's
  streams, as natively on the task's thread.
- **The leave of a thread's streams.** When the drop of one stream sets
  another cell of the same thread again, that cell stays as it is, as
  natively.

### The end of a free, and promise resolutions (step 14)

- **The end of a free.** A stream that a free closes can give its last
  bytes to a writer thread (above, "Input and output"). lean2rr calls the
  crate's `after_drain` at the end of that free. When no other release of
  the free is pending, the call comes right after the close. When other
  releases are pending (a handle in an array, a list or a structure), the
  call comes at the end of the drain that does them. The context waits for
  its writer threads there, and the other contexts run, as natively the
  close blocks the thread. At the end of a drain, the promise resolutions
  that the drain put off run first. Each waits only for the writer threads
  of the streams that the free closed before it reached the promise. Then
  the context waits for the other writer threads. The free reaches the
  elements of an array from the last, as natively. So a promise after a
  handle in an array is resolved before the handle's close blocks, as
  natively.
- **The result of an IO primitive.** The generated code reads the result
  of an IO primitive from a slot of leanrt, after the call. Each context
  has its own slot: leanrt changes the slot at each switch, with the
  stream cells. So when the primitive releases the last reference to a
  handle and waits for its writer thread, the other contexts do not
  change its result.
- **Promise resolutions.** The generated resolution is one call of the
  crate's `resolve`. The crate examines the promise and stores the value
  after its wait, so a second resolution never replaces the first.
- **`sync` dependents.** A `sync := true` dependent of a task that ends
  during the wait of `depend` runs at once, in the call, as the caller's
  code: Lean applies the function at once when the task has ended. A
  `sync` bind task whose task ends during its wait continues at once, on
  the thread of its first run.
- **`sin` and `cos`.** The crate's `sin`, `cos`, `sinf` and `cosf` are
  never inlined. So a sine and a cosine of one value stay two calls, as
  natively. One `sincos` call can give another sine.
- **IO** (LB-46, LB-47). A new `append` handle starts at the end of the
  file, so `truncate` keeps the content. `EBADMSG` is
  `inappropriateType`, as `IO.Error` documents.
