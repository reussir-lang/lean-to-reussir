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
| `runtime/prelude.rr` | Reussir | Prepended to every program. Defines the runtime types and one function per Lean extern, named after the extern's C symbol (`lean_nat_add`). Fast paths are inline Reussir code; the rest calls `leanrt`. |
| `runtime/leanrt/` | Rust | Linked into every program. Big numbers (GMP), strings, arrays, float printing, the stdio model, files, processes, once-cells, tasks and the scheduler, `Std.Sync`, the event loop. One crate, so one copy of all global state. |
| `lean2rr/L2RShim.lean` | Lean | lean2rr's own Lean library: the `Std.Internal.UV` externs (timers, sockets, name resolution, signals), `Std.Time.Timestamp.now`, `ShareCommon.Object.eq`/`hash`. Exported under the C symbols and compiled with the program. |
| generated glue | Reussir | Made by lean2rr for externs over Lean-defined types: `IO.Error`, `Option`, `List`, processes, references, tasks. |

Semantics follow Lean 4.34's C runtime (`lean.h`, `src/runtime/*.cpp`).
A comment at each function names the C function it follows.

### Calling convention

- The extern `lean_xxx` is the prelude function `lean_xxx`. Its parameters
  are the extern's mono parameters without the erased ones and without the
  IO world.
- Every function consumes its arguments (Reussir's rule). A function that
  only reads a handle releases it at the end.
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
  in Lean's order: last pushed, first freed. One difference stays: the first
  cell of a free that user code starts at a record (plan §10).
- **Reference `set`.** `l2r_rc_set` stores the new value first, then releases
  the old one as `lean_dec` does. So code that the release runs (the `sync`
  dependents of a promise it drops) sees the new value.
- **Borrowed parameters.** Reussir has none. Natively a parameter that Lean
  borrows is released by the caller after the call. Only resources can show
  the difference (a file handle still open, a pipe not yet at end of file).
  So for a program that creates resources, lean2rr runs Lean's own borrow
  inference and keeps such arguments alive until the call returns.

## Tasks and the scheduler

All tasks run on one thread. A task is *deferred*: it runs when its value is
needed, when the running code blocks, or when `main` returns. This is one of
the schedules that native Lean can produce. Why not run a task at once? A
task can wait for something that `main` does later: run at creation, it
would never finish.

A pending task runs at the first of these events:

1. `IO.wait` or `Task.get` of it, or a task that needs it runs;
2. `IO.waitAny` on a list where no task has finished;
3. the program polls it (`IO.hasFinished`) after time has passed;
4. the running code blocks and a worker is free;
5. `main` returns: the queued tasks run in the order of Lean's task manager.

**Contexts.** A thread that blocks natively lets other threads go on. The
runtime copies that with *contexts*: `main`'s stack, and one stack per task
the scheduler starts (1 GiB reserved, with a guard page). When the running
context blocks, the scheduler chooses:

{{svg:scheduler}}

What one thread cannot do: a loop that polls a reference that another task
sets, with no sleep and no output, never sees the change. A blocking system
call (reading a pipe) blocks every task.

**Promises** are runtime objects that hold their task's cell. Dropping the
last reference to an unresolved promise resolves it with `none`, as
natively. **`Std.Sync`** mutexes and condition variables are runtime
handles; a thread that waits blocks its context.

## Input and output

- **The stdio model.** Files and the standard streams follow glibc's `FILE`
  function by function (`leanrt/src/cfile.rs`): one buffer per handle,
  line-buffered terminals, the same system calls in the same order. So the
  `errno` values are native's. At exit, stdout is flushed first, as natively.
- **Fallible IO.** A runtime primitive records its outcome in a last-error
  slot. The glue turns it into `ok` or into the `IO.Error` that Lean's own
  exported builder makes, with libuv's kind and message (Lean 4.34).
- **Processes.** `IO.Process` follows `process.cpp`: `fork` and `execvp`,
  pipes with `O_CLOEXEC`. `IO.Process.output` reads both pipes together,
  because a deferred task cannot read one pipe while `main` reads the other.
- **The event loop** (`leanrt::net`) for timers, sockets, name resolution and
  signals. It works, but it is not a target now.
- **Standard streams per thread.** A task starts with the process's streams,
  as a new native thread does.

## Startup

{{svg:startup}}

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

## The shared runtime crate (plan)

lean2rr uses the shared crate **`lean-runtime`**
(github.com/QueClr/lean-runtime-rs, public). The crate implements Lean's
runtime behaviour once, as a library that a translator from Lean to Rust
can use. lean2rr's `leanrt` moves into it step by step.

| Point | Decision |
|---|---|
| What is shared | Lean's runtime semantics: hashes, floats, strings, numbers, arrays, IO, the scheduler. |
| What stays in lean2rr | The representation of values and the memory protocol: lean2rr keeps thin glue over its own layouts. |
| One runtime | Every runtime function is implemented once, in the crate. lean2rr keeps no copies and no fallbacks. |
| Safety | `#![forbid(unsafe_code)]` by default. Unsafe code comes only through vetted crates (nix/rustix, mimalloc, corosensei). A faster unsafe path can come later behind an opt-in `unsafe-fast` feature, with a written proof. |
| Speed | The safe default must be at least as fast as Lean 4.34.0's native runtime. |
| Big numbers | Behind a trait; lean2rr keeps GMP. |
| Tasks | Deferred tasks, polling yield points, Lean's exit behaviour; the stack switch through corosensei. |
| Order | Semantics first, then IO, then the scheduler. Each step must pass lean2rr's test suites. |
| Reuse | Existing runtime code moves into the crate; it is rewritten only where it does not fit. |
| Bugs | Every bug found becomes a test. Bugs of Lean's own runtime are not copied; lean-runtime's `docs/lean-bugs.md` lists them. |

Status (2026-10-04): lean-runtime has Lean's semantics (hashes, floats,
fixed-width integers, strings, `libm`, `Nat` and `Int`, the array edge
rules, panics, the text of numbers), and lean2rr uses it for all of them:
the submodule `third_party/lean-runtime`, which `scripts/l2r.py` builds and
links with `leanrt` ([runtime README](repo:runtime/README.md), "The
shared crate lean-runtime"). lean2rr keeps its hot paths: the inline
small-`Nat`/`Int` arithmetic, the one-block big numbers with GMP (behind
lean-runtime's big-number traits) and the one-block arrays' reads, writes
and pushes. IO and the scheduler follow.
