# lean2rr runtime

The runtime has two parts:

- `prelude.rr` — Reussir source that lean2rr prepends to every generated
  program. It defines the runtime types and one function per Lean extern
  (`lean_xxx` for the extern whose C symbol is `lean_xxx`), plus `l2r_*`
  primitives for lean2rr-generated glue.
- `leanrt/` — a Rust crate (rlib) linked into every program. The prelude's
  `#[ffi(import)]` textures call into it. It holds the bignum code (GMP),
  string algorithms, float formatting, buffered stdio, files, once-cells,
  panics and the main-thread setup, the task scheduler and its contexts,
  `Std.Sync`'s locks and the event loop of timers and sockets — and, being
  a single crate, the one copy of all global state (statics in the
  prelude's `extern "rust"` block would be duplicated per texture).
- `lean2rr/L2RShim.lean` (built with lean2rr) — Lean implementations of the
  `Std.Internal.UV` externs (timers, sockets, name resolution, signals,
  `Std.Net` addresses), `Std.Time.Timestamp.now` (over
  `l2r_shim_realtime_nanos`), the Windows-only time zone externs (their
  error elsewhere) and `ShareCommon.Object.eq`/`hash`, exported under their
  C symbols, which lean2rr compiles with the program over the event loop's
  `l2r_shim_*` primitives (below).

Semantics follow Lean 4.34's C runtime (`lean.h`, `src/runtime/*.cpp`)
exactly; comments at each function say which C function it mirrors.

Generated sections of the prelude (edit the generator, then run it):
`runtime/gen_scalars.py` (UIntN/IntN/USize/ISize) and
`runtime/gen_tagarr.py` (`Array Nat`/`Array Int`).

## Building and linking

`scripts/l2r.py` does everything:

1. builds `leanrt` with the pinned rustc (`L2R_RUSTC`) into
   `runtime/leanrt/target/libleanrt.rlib` (`target/rt-<hash>/` for another
   Reussir checkout), cached by a hash of its sources;
2. runs lean2rr (`L2R_LEAN2RR`) with `--prelude runtime/prelude.rr`;
3. runs rrc (`L2R_REUSSIR`; with `--reuse-across-call` unless `l2r.py` gets
   `--no-reuse-across-call`) with
   - `--polyffi-rust-path <leanrt dir>/rustc-native`: a wrapper that
     adds `-C target-cpu=native -C target-feature=-outline-atomics`. With the
     plain rustc, textures are not inlined into Reussir code, and calls through
     the packed-argument boundary (float or `str` arguments, four or more
     parameters) leave an escaping stack slot that blocks tail-call
     elimination: loops that print floats overflow the stack. It also adds
     `--extern leanrt=<rlib>` (and `--edition 2018` when rrc gives no
     edition): the drop hooks Reussir generates for the prelude's opaque
     types are textures without the prelude's `extern crate leanrt;`, and
     the containers' Rust types are `leanrt`'s (below).
   - `--polyffi-libdir runtime/leanrt/target` (so textures find `leanrt`),
   - `--link-lib libleanrt.rlib --link-lib libgmp.a` (GMP from the Lean
     toolchain, `$(lean --print-prefix)/lib/libgmp.a`, or `L2R_GMP`).

## Representations

| Lean (mono) | Reussir | Notes |
|---|---|---|
| `Nat` | `Nat` = `leanrt::nat::LNat`, one word, declared `tagged` (Reussir patch 0050) | odd: the small value `(n << 1) \| 1`, n < 2^63; even: an owned `LBig` pointer (below) |
| `Int` | `Int` = `leanrt::nat::LInt`, likewise | odd: `lean_box((unsigned)(int)i)` for i in the `int32` range; even: an owned `LBig` pointer |
| big numbers | `LBig`, one `mi_malloc` block: count `u32`, flags `u32`, signed size `i32` (limbs in use, negative for a negative value), capacity `u32`, then the limbs | GMP `mpn` operations on the limbs, in a unique operand's block with room (grown by a carry, shrunk when a result leaves most of it unused) or a fresh one; `mpz` operations on read-only views for `pow`, `gcd`, parsing and printing; normalized (only values outside the small ranges); only behind a `Nat`/`Int` word |
| `String` | `LStr` = `leanrt::string::LStr`, a pointer to one block: count, byte size, capacity, character count (32 bytes, as Lean's header), bytes | valid UTF-8, no terminator, and the character count (Lean's `m_length`, kept by every operation: `String.length` is O(1)); copy-on-write; grows by `realloc` (below) |
| `Array α` | `RVec<E>` = `leanrt::drop::Vec<E>`, a transparent wrapper of `reussir_rt::collections::vec::Vec<E>` | `E` = storage type of `α` (lean2rr boxes non-boundary types); freed without recursion (below); two allocations, a 32-byte counted box and the buffer (Lean: one block, 24-byte header) |
| `Array Nat`, `Array Int` | `LNatArr`, `LIntArr` = `leanrt::tagvec::TagVec` | the elements' own words, one block with Lean's 24-byte header (below) |
| `ByteArray`, `FloatArray` | `RVec<u8>`, `RVec<f64>` | `String.toUTF8`/`fromUTF8` copy the bytes, as natively |
| `ST.Ref σ α` / `IO.Ref α` | a lean2rr-generated shared record `L2RRefN(Cell<E>)` around a Reussir cell (two allocations: the record and the cell); a `Nat`/`Int` reference holds the handle like any other | mutated through every alias; `take` leaves the placeholder |
| `Thunk α`, `Task α` | `LCell<S>` = `leanrt::drop::Cell<S>`, a transparent wrapper of `Rc<S>` | one mutable value, seen through every alias; `S` is a state enum lean2rr generates (below) |
| `IO.FS.Handle` | `LHandle` | shared buffered file, closed with its last reference |
| `UInt8..64`, `USize` | `u8..u64`, `u64` | |
| `Int8..64`, `ISize` | `u8..u64`, `u64` (bit patterns) | signed semantics as `lean_int8_*` etc. |
| `Char` | `u32` | |
| `Float`, `Float32` | `f64`, `f32` | |
| `Bool` | `bool` | |
| `Unit`, `PUnit`, erased | `L2RUnit` | `enum [value] L2RUnit { u }` |

Every function consumes its arguments (Reussir's convention). Strings,
arrays and big numbers are updated in place when uniquely referenced
(count 1), otherwise copied once. Textures that only read a handle
release it through `leanrt::rc_release` (any `leanrt::Release` handle:
Reussir's `Rc`, `LStr`, `TagVec`)/`array::release`, whose last-reference
drop is out of line; together with `#[inline(always)]` fast paths and
`#[cold]` slow paths this lets LLVM inline the hot textures (array
get/set/push/size, string get/next/push, the Nat helpers) into Reussir code
(checked with `rrc --emit llvm-ir`). Inlined, a read's release meets the
caller's increment, and LLVM folds the pair (the free check included,
thanks to the `old count >= 1` that Reussir's `rc.inc` asserts) as long as
no other store or call lies on a path between them. So indices that are
in bounds by a proof (`fget`, `fset`, `fswap`, and the checked variants
after their bounds test) and positions proved valid (`String.Pos.get`,
`next`) are converted by `l2r_index_of_nat`, whose impossible big case
ends the program instead of rejoining the read with refcount traffic on
the big number; a checked index (`get!`, `set!`) is taken as its word once
(`l2r_word_index_ok`), so in bounds there is no refcount traffic on it at
all.

**`Nat`/`Int`.** One word each, with Lean's exact encoding
(`leanrt::nat`): an odd word is a small value, `lean_box(n)` for a `Nat`
below 2^63 and `lean_box((unsigned)(int)i)` for an `Int` in the `int32`
range; an even word is an owned reference to a big number, one block
with a 16-byte header and the limbs inline (`leanrt::big`; native Lean's
`lean_mpz_object` keeps the limbs in a second allocation). C code written
against `lean.h` could take and return the small words unchanged; a big
number would be converted. Reussir copies and drops them as handles of an opaque type declared
`#[ffi(rust = "::leanrt::nat::LNat", tagged)]`: with Reussir patch 0050 it
counts only even words (`rc.inc` and the drop hook, `LNat`'s `Drop`, run
only when the low bit is clear). The prelude's functions take each `Nat`
argument as its word once (`l2r_nat_raw`, which then owns the reference),
compute small results inline, and call `leanrt::nat`'s slow paths
(`nat_add`, ... taking owned words, every small/big combination) for the
rest; `l2r_nat_of_raw` makes a handle of a word, `l2r_nat_drop_raw`
releases one. The slow paths normalize: a `Nat` below 2^63 (an `Int` in
`int32`) is always small, so two small words are equal exactly when the
values are. A build with `L2R_LEANRT_RUSTFLAGS="--cfg leanrt_count_bigs"`
counts the big numbers made and freed and prints the counts at exit
(`tests/runtime/nat-alloc-check.sh`).

**`Array Nat`/`Array Int`.** `LNatArr`/`LIntArr` (`leanrt::tagvec`, the
`nat-arrays` pass) store the elements' words, like Lean's array object:
the handles move in and out as their words (`l2r_natarr_get` wraps the
owned word it reads, `l2r_natarr_set` stores `l2r_nat_raw(x)`). Without
the pass an `Array Nat` is an `RVec<Nat>`, one word per element too, in
two allocations (the `Rc` box and the buffer). Every
`lean_array_xxx<E>` / `l2r_array_xxx<E>` has `lean_natarr_xxx` /
`l2r_natarr_xxx` (and `intarr`) with the same arguments and element type
`Nat` (`Int`); `lean_mk_array`/`lean_mk_empty_array_with_capacity` become
`lean_mk_natarr`/`lean_mk_empty_natarr_with_capacity`. A tag vector is one
allocation laid out like Lean's array object: the count (a `u32`, padded
to a word), the size, the capacity, then the words, so a three-element
array takes 48 bytes as natively. A copy of a shared one keeps its
capacity (`lean_copy_expand_array`), so a literal `#[a, b, c]`, which
pushes onto a shared empty array of capacity 3, allocates once.

**Runtime-owned objects.** `LStr` and `TagVec` are `leanrt` types: a
`#[repr(transparent)]` pointer to a block allocated with `mi_malloc`, whose
first word is the `u32` count. That is all Reussir needs of an opaque type
(its `rc.inc` increments the count inline; `rc.dec` calls the type's drop
hook, a texture that drops the Rust value), so their `Clone` and `Drop` do
the counting, the drop's last reference out of line. A unique block grows
in place with `mi_realloc` (at least doubling; the capacity is the whole
block: mimalloc's size class, `mi_good_size`, for small blocks, a power of
two above 4 KiB); a shared one is copied with room to spare (a string:
at least doubled, as `lean_string_push`; an array: its capacity kept).
`dbgTraceIfShared` recognizes them by their Rust type names
(`leanrt::string::`, `leanrt::tagvec::`) besides `reussir_rt::`.

## Calling convention

As fixed by lean2rr:

- The extern `lean_xxx` is called as the prelude function `lean_xxx`, with
  the extern's mono-phase parameters in order minus erased ones (types,
  proofs, `lcErased`) and minus the IO world (`lcVoid`).
- Polymorphic externs take explicit storage type arguments:
  `lean_array_push<E>(arr, x)`.
- Functions whose results mention Lean-defined inductive types (`List`,
  `Option`, `Prod`, `Ordering`, `EST.Out`, ...) cannot be written here: the
  prelude offers primitives and generic helpers for lean2rr's glue (below).

Nat positions and indices: a big `Nat` is never a valid position or
index. Where Lean's C code distinguishes "not a scalar" (`>= 2^63`, exactly
the big `Nat`s here) from "out of range", the prelude reproduces that too
(`lean_string_utf8_extract`, where a big position counts as `SIZE_MAX`
since Lean 4.34: a big start gives `""`, a big end extracts to the end;
`Float.scaleB` with Ints outside 32 bits). `String.extract`'s positions are
proved valid: its `lean_string_utf8_extract_fast` (new in Lean 4.34) takes
them with `l2r_index_of_nat`.

## Glue helpers

Generic helpers take the result type's constructors as arguments (nullary
constructors as values, others as curried closures), so lean2rr's glue is a
single call:

| extern | helper |
|---|---|
| `lean_string_compare` (→ `Ordering`) | `l2r_string_compare_with<O>(a, b, lt, eq, gt)`; or `l2r_string_compare(a, b) -> u8` (0/1/2) |
| `lean_string_data` (`String.toList`) | `l2r_string_to_list<L>(s, nil, \|c\| \|t\| cons(c, t))` |
| `lean_string_utf8_get_opt` (→ `Option Char`) | `l2r_string_utf8_get_opt_with<O>(s, p, none, \|c\| some(c))`; or `l2r_string_utf8_get_opt(s, p) -> u32` (`0x110000` = none) |
| `lean_array_to_list` (→ `List α`) | `l2r_array_to_list<E, L>(a, nil, \|x\| \|t\| cons(unbox(x), t))`; `l2r_natarr_to_list<L>`, `l2r_intarr_to_list<L>` |
| `lean_float_frexp`, `lean_float32_frexp` (→ `Float × Int`) | `l2r_float_frexp_with<P>(x, \|m\| \|e\| mk(m, e))`; or `l2r_float_frexp_mant`/`_exp` |
| `lean_io_getenv` (→ `Option String`) | `l2r_io_getenv_with<O>(name, none, \|s\| some(s))` |
| `lean_slice_hash`, `lean_slice_dec_lt` (take `String.Slice`) | `l2r_slice_hash(s, b, e)`, `l2r_slice_dec_lt(s1, b1, e1, s2, b2, e2)` |
| `lean_byteslice_beq` (takes `ByteSlice`s) | `l2r_byteslice_beq(a, startA, stopA, b, startB, stopB)` (fields `byteArray`, `start`, `stop`) |

**IO externs that cannot fail** (BaseIO) have a payload primitive named
`l2r_` + the symbol without `lean_`, taking the same passed arguments;
lean2rr wraps its result with `wrapIOResult`: `l2r_io_mono_ms_now()`,
`l2r_io_mono_nanos_now()`, `l2r_io_process_get_pid()`, `l2r_io_get_num_heartbeats()`,
`l2r_io_check_canceled()`, `l2r_io_get_tid()`, `l2r_io_initializing()`,
`l2r_io_set_heartbeats(n)`, `l2r_runtime_mark_persistent<T>(a)`,
`l2r_runtime_mark_multi_threaded<T>(a)`, `l2r_runtime_forget<T>(a)`,
`l2r_runtime_hold<T>(a)`, `l2r_io_prim_handle_is_eof(h)`,
`l2r_io_prim_handle_is_tty(h)`. (`l2r_io_app_path()`, `l2r_io_current_dir()`
and `l2r_io_process_get_current_dir()` are infallible stand-ins for the
fallible primitives below.) References are Reussir cells in a
lean2rr-generated record (`L2RRef_N(Cell<T>)`, two allocations;
translation plan §5.1), read and written by the plain-Reussir helpers
`l2r_rc_get/set/swap<T>` (a `Nat` or `Int` reference holds the handle
like any other). Promises hold the `LCell` of their task
(below). `LRef<T>` and its `l2r_ref_*` functions (a runtime cell, a
0-or-1 element vector) are no longer used by generated code. A `set`
(`l2r_rc_set`, and `l2r_lcell_set` for task and thunk cells) stores the
new value first and then releases the old one as `lean_dec` does
(`leanrt::drop::release`, through `l2r_release_value`): a shared value is
decremented; the last reference to a record is freed inside a free the
runtime starts (`drop::run`), so its fields go last first and the `sync`
dependents of the promises it drops run when that free ends. A unit or
enumeration value cannot cross the FFI boundary and its release runs
nothing: lean2rr stores it with `l2r_rc_put` (`refSetFn`).

**Freeing containers.** Native Lean frees an object iteratively: the
children whose count drops to zero go on a stack of objects to free, popped
last first. Reussir's drop glue does the same for records with the local
patches 0013 and 0014: the record members it frees go on a stack of
pending work per thread (`reussir_rt::drop`), and it releases a container
field through the container's Rust `Drop` (the opaque type's drop hook),
which releases the elements. The prelude's containers are therefore
`leanrt::drop`'s wrappers, whose `Drop` frees the last reference through
that same stack (so the runtime needs Reussir with 0014): a container
freed while another free runs (from an element's release, or from record
glue) is pushed instead, and the outermost free, glue or container, pops
the stack until it is empty. An array is emptied from its last element,
and what an element's release pushes is done before the next element, so
the order of observable releases matches Lean's (file handles closed, and
so flushed, promises resolved; `fs` and `task` push those too while a free
runs), except at the top of a free that starts at a record that user code
drops by itself (translation plan §10). For an
array of Reussir records (`Bridge` elements), a shared element is
decremented inline instead of through `<record>_ffi_release` (the
compiler's glue, an out-of-line call; it decrements the same count), and,
outside a running free, an array none of whose elements is freed is freed
without the stack (`ReleaseElems`): only an element whose last reference
goes takes the glue and the stack, so the order of releases is unchanged.
(Inside a free the array is pushed as before: a later field of the record
being freed may hold one of its elements.)

**Constants.** A constant's accessor tests its once-cell inline
(`once::claim`'s fast path); the slow path, out of line, computes it or
waits for the scheduler context computing it.

**Thunks and tasks.** A thunk or task is an `LCell<S>` holding a
lean2rr-generated state `enum S { pending(L2RUnit -> α), busy, done(α),
conv(L2RUnit -> α, L2RBox) }` (a task's `conv` also holds the original's
address, its identity for `leanrt::task`, and tasks also have
`bind(L2RUnit -> LCell<S>)`; a shared enum, so any `α` fits). Cell primitives: `l2r_lcell_new<S>(v)`,
`l2r_lcell_get<S>(c)`, `l2r_lcell_set<S>(c, v)`, `l2r_lcell_swap<S>(c, v)`
(returns the old state), `l2r_lcell_addr<S>(c)` (the cell's address).
lean2rr generates the forcing functions (run the closure once, store
`done`); `l2r_lazy_cycle<T>()` waits forever, for a thunk or task needed by
its own computation, as native Lean does. Tasks are deferred until needed
(translation plan §5.14); `leanrt::task` keeps an entry per unfinished task
(in a slab; the cell's 4 bytes of padding after its count hold the entry's
index, initialized by `l2r_lcell_new`), the queues of pending tasks (one per
priority, in the order Lean's task manager with one worker would start
them; the runtime holds one reference per pending task), each task's
dependents (an intrusive list, newest first), the walks of finished tasks'
dependents, the stack of running tasks, cancellation flags and their
propagation, and the state of the single worker it models. A task is
identified by an address: its cell's, or the one a converted task records.
`l2r_task_register<S>(c, tag, prio, kind)` records a new task (`tag`
identifies `S` for the generated dispatchers; `prio` as Lean passes it,
taken modulo 2^32; `kind`: 1 pure, which the runtime deletes rather than
runs when only it refers to it, 2 a dependent; result 1: run it now, at
priority 2^32-1), `l2r_task_depend_at(src, dep, sync)` records that `dep`
depends on `src` (result 1: run it now), `l2r_task_begin<S>(c)` /
`l2r_task_end<S>(c)` bracket a run (`begin` takes the task off the queue
and drops the runtime's reference; its result is 1 when the task runs as
on a worker thread, with stream cells of its own, 0 when it runs on the
current thread; `end`'s is 1 when the caller must walk the dependents now,
`l2r_task_walk_if(e)`, 0 when the walk that handed the task over continues
with them), `l2r_task_bind_wait<S>(c, src)` (a `bind` task that now waits
for its continuation `src`), `l2r_task_walk_next()` (the `sync` dependents
to run), `l2r_task_source_next_at(a)` (the pending tasks a task about to
run waits for, deepest first, or queued tasks while it waits for a promise)
and `l2r_task_next_tag()` (the next queued task), all handed over by
`l2r_task_handed<S>()` / `l2r_task_take<S>()` (a handed task is off its
queue and its source's dependents, and is handed to no one else before it
begins: the generated code may block before that, forcing its sources),
to be dropped instead of run when `l2r_task_deleting()` (a pure task the
program has dropped: only the runtime refers to it; deleting it releases
what it holds, so a whole chain or tree of dropped pure tasks goes),
`l2r_task_status_at(a)` (0 waiting, 1 running or an unresolved promise, 2
finished), `l2r_task_wait_status_at(a)` (for `IO.waitAny`; 3: waits for an
unresolved promise), `l2r_task_query_at(a)` (for `IO.getTaskState`; 3: run
it first; 4: run queued tasks until the promise is resolved),
`l2r_task_cancel_at(a)`, `l2r_task_check_canceled()`,
`l2r_task_tid_offset()` (added to `IO.getTID` inside tasks: the running
task's worker number), `l2r_task_deferring()` (false during
initialization, when Lean runs tasks at once), `l2r_task_manager_start()`
(before `main`) and `l2r_task_shutdown()` (after `main`, before the final
run of queued tasks). `l2r_sleep_ms` goes through `leanrt::task` (sleeps
count as time passing for its heuristics) and the scheduler (below). Standard streams are per task,
as they are per thread natively: `l2r_std_push(base)` / `l2r_std_pop(base)`
set the stream cells aside and put them back
(`leanrt::once::push_context`), and `l2r_once_take<T>(slot)` empties a
cell.

**The scheduler** (`leanrt::sched`, `coro`; translation plan §5.14,
*Blocking*). Code that blocks (a contended lock, a condition variable, a
task running on another context or a promise not resolved yet, a sleep, the
final run after `main`) suspends its *context* (`main`'s thread stack, or a
stack of a worker thread's size, 1 GiB reserved, with a guard page that the
stack-overflow handler recognizes: the scheduler records the running
context's stack at each switch, `coro::set_running`) and the scheduler
runs: a context that
can go on, else a queued task on a new context if one of Lean's task
manager workers is free (`LEAN_NUM_THREADS`, or the number of online
processors, as `std::thread::hardware_concurrency`: not limited by the CPU
affinity mask or a cgroup quota;
a context waiting for a task frees its worker; dedicated tasks always
start), else the event loop's timers and sockets or the earliest sleeper.
Nothing can go on: the program waits forever. A switch saves and restores
the per-context state: the running tasks, walks and chains of
`leanrt::task` (`task::CtxState`) and the mutable cells (the current
standard streams) with their saved contexts (`once::CtxState`). A free's
pending work is the thread's (`reussir_rt::drop`), so no context is
suspended inside a free (`sched::switch_to` checks): a promise dropped
there is resolved in its turn, but its dependents, which run Lean code that
may block, are walked as soon as the free is over (`task::run_later_walks`,
through the program's `l2r_task_walk_c`): when the drain ends, through
Reussir's `__reussir_drop_drained` (local patch 0040; `task::resolve`
stores `task::drained` there, linking the symbol weakly, so the runtime
also builds against a Reussir without it), when a free that one of the
runtime's containers started ends (`drop::run`), and otherwise (the record
glue's frees, without patch 0040) at the context's next effect point,
block, Std.Sync wait (`sync::settle`, before the object is looked at) or
question about a task. A wait that registers in `sched::block` returns at
once when those walks ran (its caller looks again). The
context switch (`coro::switch`) saves the callee-saved registers on the
stack and swaps stack pointers (aarch64 and x86-64 assembly). The program
exports `l2r_task_run_one_c` (lean2rr's `l2r_task_run_one`), which a new
context calls to run its first queued task. Output (`io::stream_put`,
`fs::put_str`, `fs::flush`), spawning a process and `IO.Process.exit` are
effect points (`sched::effect`): a context whose sleep is over, a due timer
and what its completion releases, ready descriptors (`net::poll_now`, at
most every 50 µs), a
context able to run for 5 ms, a task queued 5 ms ago with a worker free run
first, round after round (up to 64; what runs in those rounds starts no
tasks at its own effect points); `IO.sleep 0` lets them run whatever
their age (`sched::zero_sleep`). `l2r_task_wait_running(a)` waits for a
`busy` task that runs on another context; `l2r_thunk_wait_busy(a)` for a
`busy` thunk until `l2r_thunk_done(a)`; `l2r_task_wait_progress()` for some
task to finish (`IO.waitAny`). Forcing a task that waits for one running on
another context waits for that one first (`task::source_next`); polling a
task that cannot finish without the others lets them go on once per
question (`sched::poll_yield`). A worker context remembers its first task
with the entry's serial number. Forcing
chains remember tasks by their entry's serial number (entries and cell
addresses are reused). A constant's accessor calls `l2r_once_claim(slot)`
(`once::claim`): a context that needs a constant another is computing
waits for it. `LEAN_NUM_THREADS=0` (C's `atoi`) is no task manager: tasks
run at once (`task::start` does not start deferring).

**`Std.Sync`** (`leanrt::sync`): `BaseMutex`, `Condvar`,
`BaseRecursiveMutex`, `BaseSharedMutex` are `LHandle`s; the externs'
payloads are `l2r_io_basemutex_new()`, `l2r_io_basemutex_lock(m)`, ... (over
`l2r_sync_new(kind)`, `l2r_sync_op(op, h)`, `l2r_condvar_wait_h(c, m)`).
A lock is owned by a thread: the context and its innermost running task's
thread number; waiting blocks the context; an unlock hands the lock to the
longest waiter. Relocking a held `BaseMutex` waits forever (glibc); the
shared mutex is libc++'s (an entered writer keeps new readers out).

**The event loop** (`leanrt::net`, for `lean2rr/L2RShim.lean`): timers,
signal watchers and sockets are `LHandle`s; an operation returns an `Op`
handle (`OpSt`: done, canceled, code, a synchronous error, bytes, address,
strings, a new socket) read by `l2r_shim_op_*`. An operation completing
later takes a promise `r` from the shim and drops it (on the event loop's
own context, `sched::ensure_evloop`) when it completes, which runs the
shim's continuation (a `sync` dependent of `r`). A timer's `stop` and
`cancel` (`timer_ctl`) instead hand the program's promise and `r` back
(`net::GivenUp`), and a socket's `cancel_accept` and `cancel_recv` hand
`r` back, to the glue, which drops them once the primitive has returned,
on the caller's context, as natively. `net::wait` polls the
watched descriptors (and the signal handler's pipe: libuv's loop signal
pipe, which the runtime opens at startup, `rt::signal_pipe`) with the
earliest timer as timeout. The primitives (`l2r_shim_*`, the payloads of
the shim's `lean_shim_*` externs): timers and signals
(`timer_new`, `signal_new`, `timer_next_kind`, `timer_promise`,
`timer_start`, `timer_set`, `timer_ctl`), TCP (`tcp_new`, `tcp_bind`,
`tcp_listen`, `tcp_connect`, `tcp_send`, `tcp_accept`, `tcp_try_accept`,
`tcp_cancel_accept`, `tcp_shutdown`, `tcp_nodelay`, `tcp_keepalive`), both
(`sock_recv` (size 0: `waitReadable`), `sock_cancel_recv`, `sock_name`),
UDP (`udp_new`, `udp_bind`, `udp_connect`, `udp_send`, `udp_option`,
`udp_membership`, `udp_multicast_interface`), name resolution
(`dns_get_info`, `dns_get_name`), interfaces (`ifaces`), and the pure
`lean_shim_uv_kind`, `lean_shim_uv_strerror` (libuv's error kinds and
messages, by libuv code; the shim stores the positive errno, `-code`, in the
`IO.Error`, as Lean 4.34's `lean_decode_uv_error`), `lean_shim_pton`, `lean_shim_ntop`; `Std.Internal.UV.System`
over `leanrt::sys` (`sys_title_set`, `sys_query(which)` for the queries
with a string or several results, the process title included,
`sys_group`, `sys_getenv`, `sys_priority`, `sys_word(which)` for single
numbers, `sys_chdir`, `sys_setenv`, `sys_setpriority`, `sys_random`),
following libuv's Linux code (`/proc/uptime`, `/proc/stat`,
`/proc/meminfo`, the cgroup's memory limit, `getpwuid_r`, ...) with the
buffers Lean passes (`UV_ENOBUFS` for a home or temporary directory of
`PATH_MAX` bytes or more, a process title of 512 or more) and libuv's
argument checks (a priority outside [-20, 19], `random` of more than
`0x7FFFFFFF` bytes, an empty host name or one of 256 bytes or more for
`getAddrInfo`). An operation's strings are decoded as `lean_mk_string`
does (invalid UTF-8 becomes U+FFFD). Addresses are byte arrays:
the family (4 or 6), the port (big-endian, for socket addresses), the
address bytes. `l2r_uv_event_loop_alive()` is true, as natively. A promise
the loop gives up unresolved (a timer stopped, reset or re-armed, an
operation whose start failed) is released on the loop's context too
(`net::release`), so no generated code runs inside a primitive. The shim's
`l2r_shim_promise_is_resolved(p)` answers `IO.Promise.isResolved`
(`task::promise_is_resolved`, as `IO.getTaskState` answers for the
promise's task) and then releases `p`: natively `isResolved` borrows the
promise, so a last reference resolves it with `none` only after the
question.

**Promises.** `LPromise` is a runtime object holding the cell of the
promise's task (`leanrt::task::Promise`): `l2r_promise_new<S>(c)` (Lean's
internal panic before `main`), `l2r_promise_cell<S>(p)` (the task, a new
reference), `l2r_promise_release(p)`, and `l2r_task_resolve_at(a)` after
the generated code has stored the value (1: walk the dependents now). When
the last reference to a promise goes, the runtime calls the program's
`l2r_promise_drop_c(cell)` (a trampoline lean2rr exports), which resolves
an unresolved promise with `none`. `l2r_option_get_or_block_none<T>()` is
`Option.getOrBlock!` on `none` (`Promise.result!` of a dropped promise):
Lean's forced panic message, then the running context blocks forever
(`task::hang`), as natively the calling thread does: the other tasks and
`main` go on.

**Fallible IO** (files, standard streams): primitives record their outcome
in a global last-error slot; the glue is

    let v = l2r_fs_open(path, modeIndex);
    l2r_io_finish(v, |v| EST.Out.ok(v), |kind| |errno| |fname| |details| mkError)

where `mkError` builds the `IO.Error` with the `lean_mk_io_error_*`
constructor (exported Lean functions) numbered `kind`, as Lean's
`decode_io_error`:

| kind | constructor (`lean_mk_io_error_…`) | kind | constructor |
|---|---|---|---|
| 0 | `other_error(errno, details)` | 12 | `no_such_thing_file(fname, errno, details)` |
| 1 | `interrupted(fname, errno, details)` | 13 | `already_exists(errno, details)` |
| 2 | `invalid_argument(errno, details)` | 14 | `already_exists_file(fname, errno, details)` |
| 3 | `invalid_argument_file(fname, errno, details)` | 15 | `hardware_fault(errno, details)` |
| 4 | `no_file_or_directory(fname, errno, details)` | 16 | `unsatisfied_constraints(errno, details)` |
| 5 | `permission_denied(errno, details)` | 17 | `illegal_operation(errno, details)` |
| 6 | `permission_denied_file(fname, errno, details)` | 18 | `resource_vanished(errno, details)` |
| 7 | `resource_exhausted(errno, details)` | 19 | `protocol_error(errno, details)` |
| 8 | `resource_exhausted_file(fname, errno, details)` | 20 | `time_expired(errno, details)` |
| 9 | `inappropriate_type(errno, details)` | 21 | `resource_busy(errno, details)` |
| 10 | `inappropriate_type_file(fname, errno, details)` | 22 | `unsupported_operation(errno, details)` |
| 11 | `no_such_thing(errno, details)` | 23 | `IO.userError(details)` |

Since Lean 4.34 the kind and the details come from libuv's code for the
errno (`decode_uv_error_impl` in io.cpp; `leanrt::fs::crt_to_uv`, which
maps the errnos libuv cannot represent to the closest code it can, e.g.
`EBADMSG` to `EPROTO`, a protocol error): the details are `uv_strerror`'s
("illegal operation on a directory" for `EISDIR`, "Unknown system error
-122" for an errno libuv has no name for), not `strerror`'s; the error code
stays the errno. The operations Lean implements with libuv (`removeFile`,
`hardLink`, `metadata`, `symlinkMetadata`, `createTempFile`,
`createTempDir`) report errors as `decode_uv_error`: classified by libuv's
code (errnos it has no case for are kind 0), `uv_strerror`'s details, and
the positive errno as the error code (`2` for `ENOENT`; Lean 4.33 stored
libuv's negated code, `4294967294`). `leanrt`'s unit test `fs_tests.rs`
checks both decoders against native Lean for every errno 0..140 (test
`RtIOErrorDecode` checks reachable cases end to end). Kind 23 is Lean's
`io_result_mk_error(msg)` (`IO.currentDir`, `IO.appPath`).

File primitives: `l2r_fs_open(path, mode)` (mode = `IO.FS.Mode` constructor
index), `l2r_fs_put_str`, `l2r_fs_write`, `l2r_fs_flush`, `l2r_fs_read(h, n)`,
`l2r_fs_get_line`, `l2r_fs_rewind`, `l2r_fs_truncate`,
`l2r_fs_lock(h, exclusive)`, `l2r_fs_try_lock`, `l2r_fs_unlock`,
`l2r_fs_remove_file`, `l2r_fs_create_dir`, `l2r_fs_remove_dir`,
`l2r_fs_rename`, `l2r_fs_hard_link`, `l2r_fs_set_access_rights` (for
`lean_chmod`), `l2r_fs_real_path`, `l2r_fs_read_dir(p) -> RVec<LStr>` (names
in `readdir` order), `l2r_fs_metadata(p, follow) -> RVec<u64>` ([atime s,
ns, mtime s, ns, size, `FileType` index, numLinks]; the seconds are `i64`
bit patterns), `l2r_fs_current_dir()`, `l2r_fs_app_path()`,
`l2r_fs_process_get_current_dir()`, `l2r_fs_process_set_current_dir(p)`,
`l2r_fs_create_tempfile() -> LHandle` (then `l2r_fs_temp_file_path()` is
its path, for the `Handle × FilePath` pair), `l2r_fs_create_tempdir()`,
`l2r_fs_get_random_bytes(n)` (`IO.getRandomBytes`, from `/dev/urandom`).
The current directory (`getcwd`) and `realPath` (`realpath`) use a
`PATH_MAX` buffer, as natively, so a longer path fails.
**stdio model.** Handles and the standard streams are models of glibc's
`FILE` (`leanrt/src/cfile.rs`, following libio's `fileops.c`/`genops.c`
function by function): one `st_blksize` buffer shared by reading and
writing with libio's get/put areas and cached offset; `fwrite`
(`_IO_new_file_xsputn`, line-buffered tails flushed at each newline),
`fread` (`_IO_file_xsgetn`, including direct reads of whole blocks),
`getc`, `fflush`, `fseek` (in-buffer seeks), `ftello`; `EBADF` for the
wrong direction after the same mode switch; sticky end-of-file and error
indicators (after any failed operation on a handle, `getLine` fails, as
natively); reading a terminal first flushes a line-buffered stdout. The
same system calls happen in the same order, so the `errno`s are native's.
At exit, stdout is flushed first (libc++'s `ios_base::Init`), then every
`FILE`'s pending output, newest first, then used streams are synced (a
seekable stdin is left at the position the program read up to).

Standard-stream primitives (`fd` = 0 stdin, 1 stdout, 2 stderr; the fields
of `IO.FS.Stream`): `l2r_stream_putStr(fd, s)`, `l2r_stream_write(fd, b)`,
`l2r_stream_flush(fd)`, `l2r_stream_read(fd, n)` and
`l2r_stream_getLine(fd)` record their outcome like the file primitives
(`EPIPE`, `EBADF` for the wrong direction, `EINVAL` on streams that were
closed at startup); `l2r_stream_isTty(fd)` cannot fail.

**Child processes** (`src/runtime/process.cpp`: `fork` + `execvp`, pipes
with `O_CLOEXEC`, stdout flushed first when the child inherits stdin):
`l2r_proc_spawn(cmd, args, cwd, has_cwd, env_names, env_values, env_set,
modes, inherit_env, setsid) -> u32` (the pid; fallible; `modes` = stdin |
stdout << 8 | stderr << 16 as `IO.Process.Stdio` indices; `env` as parallel
arrays, `env_set[i]` for `some`), then `l2r_proc_end(0/1/2) -> LHandle` (the
parent's end of a piped stream, a closed handle otherwise);
`l2r_proc_wait(pid) -> u32` (128 + signal when killed),
`l2r_proc_try_wait(pid) -> u64` (`1 << 32 | code` once exited, 0 while
running), `l2r_proc_kill(pid, setsid)` — all fallible. A child that cannot
change directory or execute prints Lean's message and exits with 255; as
natively (`std::cerr` is tied to `std::cout`), it first flushes the stdout
bytes the parent had pending, into its own descriptor 1.
`IO.Process.output` reads stdout in a dedicated task while it reads
stderr; without threads, `l2r_proc_drain(out, err) -> RVec<u8>` reads both
pipes to end of file together (`poll`), returning stdout's bytes, then
`l2r_proc_drained_err() -> RVec<u8>` gives stderr's (fallible: the first
read error). The glue applies `readToEnd`'s UTF-8 check (`Tried to read
from handle containing non UTF-8 data.`) to stderr before `wait` and to
stdout after, as natively (but stderr's check comes once both pipes are at
end of file; natively as soon as stderr is). A read error stops the drain
and is reported at once.

**Other glue primitives.**

| Lean | primitives |
|---|---|
| `initialize`, closed terms | once-cells `l2r_once_claim(slot)` (`l2r_once_has` for the mutable cells), `l2r_once_get<T>(slot)`, `l2r_once_set<T>(slot, v)` |
| `IO.setStdout`/`setStderr`/`setStdin` | a cell per stream: `l2r_once_*` plus `l2r_cell_swap<T>(slot, v) -> T` (returns the previous value) |
| `timeit`, `allocprof` | `l2r_io_timeit_with<R>(msg, act)`, `l2r_io_allocprof_with<R>(msg, act)` |
| `Void.mk` | `lean_void_mk<T>(x)` |

**Main thread.** `leanrt::rt::run_main(|| body())` runs the program on a
thread with a 1 GiB stack and Lean's stack-overflow report (a fault in the
stack guard page prints `\nStack overflow detected. Aborting.` and aborts,
exit 134, without flushing stdout — as native; also a fault below the stack
while the stack pointer is below it, which a frame without stack probes,
such as GMP's scratch space, causes when it skips the guard page).
`leanrt::rt::run_main2(|| init(), || body())` first runs `init` (the
module initializers) on the calling thread, as native `main` does. Every
thread that runs Lean code calls `install_stack_overflow_handler` (its
guard page is recorded per thread). Before `main`, an ELF constructor
opens the descriptors native Lean's runtime has open at startup (libuv's
epoll descriptor, two io_uring rings when the kernel has them, two signal
pipes and an eventfd, close-on-exec, in that order at the lowest free
numbers; signal watchers use the second pipe, as libuv's loop does):
`/proc/self/fd`, descriptor numbers and `EMFILE` thresholds are native's,
and a standard descriptor closed at startup is taken by the first of
them, as natively (using it fails with `EINVAL`, children see it
closed). Running before Rust's runtime, the constructor also keeps Rust
from putting `/dev/null` in the place of closed standard descriptors.
`l2r_set_initializing(b)` sets what `IO.initializing` answers.

## Requests for lean2rr

Found while testing the runtime; items marked *done* are handled by
lean2rr's dev branch (the tests pass with it).

1. *done* — Constructors with extern implementations (`Int.ofNat`,
   `Int.negSucc`) are extern calls, not constructors of `Int`.
2. *done* — Propositions (`ByteArray.IsValidUTF8`) have no representation,
   and proofs are not passed to externs.
3. *done* — Extern type arguments are mono types (one-field structures
   unwrapped).
4. *done* — Only type-variable positions of polymorphic externs are boxed
   (`Array.get!Internal @[Nat]` used to box the index).
5. *done* — Glue for `String.compare`, `String.toList`, `String.get?`,
   `Float.frExp`, `String.intercalate`, `Array.toList`, `ST.Ref`.
6. *done* — Element-wise `RVec` conversion between instantiations
   (`RtHashMap`), and the `unsafeCast`-based `Array.mapMUnsafe`/
   `Array.modifyM` implementations (`RtArrayUnsafe`).
7. *done* — `BaseIO.asTask` (symbol `lean_io_as_task`): the task glue is
   keyed on `IO.asTask`, which is not the extern (Lean 4.33, 4.34).
8. *done* — `dbgTrace` (and `dbgSleep`, `dbgStackTrace`, `Thunk.mk`) at a
   boxed `α`: the `PUnit → α` closure argument must be wrapped to return the
   box (`lean_dbg_trace<ElemBox>(msg, f : L2RUnit -> Nat)` does not
   type-check). lean2rr now instantiates generic prelude functions that are
   plain Reussir code at the value type (`lean_dbg_trace<Nat>`), and thunks
   and tasks are cells of a generated state type.
9. *done* — BaseIO payload primitives above (`IO.monoMsNow`, `IO.getRandomBytes`,
   ...) and the file protocol need `wrapIOResult` glue; `IO.FS.Handle`
   (`lcAny` in mono code) must be represented as `LHandle`.
10. *done* — Externs implemented by `@[export sym]` Lean code (all
    `Substring.Raw.Internal.*`, many `String.Internal.*`,
    `lean_array_to_list_impl`, `IO.eprint(ln)`, `lean_stream_of_handle`, the
    `IO.Error` constructors, `Lean.Name.beq` has a reference body) should
    compile and call that code; the prelude has hand-written versions of the
    `String.Internal.*` ones.
11. *done* — `Array Nat`/`Array Int` as `LNatArr`/`LIntArr` (names above).
12. *done* — `Nat.repr`/`Int.repr` of big numbers are Lean code dividing by 10 digit
    by digit (quadratic); `l2r_nat_repr`/`l2r_int_repr` are exact
    replacements using GMP.
13. *done* — The generated entry should run `l2r_main_body` through
    `leanrt::rt::run_main(|| unsafe { l2r_main_body() })` instead of its
    own `std::thread` (Lean's stack size incl. `LEAN_STACK_SIZE_KB` and
    `LEAN_MAIN_USE_THREAD`, and Lean's stack-overflow message; test
    `RtStack`).
14. *done* — The standard-stream glue should check each `l2r_stream_*` call with
    `l2r_io_finish`, as for files (tests `RtBrokenPipe`, `RtClosedStreams`).
15. *done* — `lean_io_prim_handle_is_tty` and `lean_io_prim_handle_is_eof` are
    `BaseIO`: the `lean_io_prim_handle_` prefix rule sends them to the
    fallible glue, which rejects them ("IO result ... cannot fail"). Use the
    BaseIO payloads `l2r_io_prim_handle_is_tty`/`_is_eof` (test
    `RtHandleIsTty`).
16. *done* — `ST.Prim.Ref.take` is lowered to `l2r_ref_get`, so the value stays in
    the cell and the taken copy is shared: every `modify`/`modifyGet`
    copies the array or string it updates (quadratic loops). Map it to
    `l2r_ref_take` (now `l2r_rc_swap` with the placeholder).
17. *done* — `allocprof` (`lean_io_allocprof`) has no glue: use
    `l2r_io_allocprof_with(msg, act)` (test `RtAllocProf`); likewise
    `timeit` → `l2r_io_timeit_with`.
18. *done* — `lean_chmod` (`IO.setAccessRights`) is not a fallible IO symbol yet; its
    primitive is `l2r_fs_set_access_rights(p, mode)`.
19. *done* — Glue for `IO.FS.createTempFile` (`l2r_fs_create_tempfile` then
    `l2r_fs_temp_file_path` for the pair) and `IO.FS.createTempDir`
    (`l2r_fs_create_tempdir`).
20. *done* — `IO.currentDir`, `IO.appPath` can fail with a user error (kind 23), and
    `IO.Process.getCurrentDir`/`setCurrentDir` with errno errors: use
    `l2r_fs_current_dir`, `l2r_fs_app_path`,
    `l2r_fs_process_get_current_dir`, `l2r_fs_process_set_current_dir`
    with `l2r_io_finish`; kind 23 needs `IO.userError`.
21. *done* on the runtime side — native `panic!` (outside
    `LEAN_ABORT_ON_PANIC`), the runtime's own panics (`index out of
    bounds`, `String.get!`), `dbgTrace`, `dbgTraceIfShared`, `timeit` and
    `allocprof` print to the *current* stderr stream (`io_eprintln`):
    every program defines `fn l2r_stderr_put(s : LStr) -> u64` (lean2rr),
    which the prelude calls. Internal panics, uncaught exceptions and
    abort-mode panics go to descriptor 2, as natively. The runtime's own
    panics are raised inside the prelude's array helpers, which the stream
    code behind `l2r_stderr_put` uses too; a Reussir-level call there
    makes rrc crash in `TokenReusePass` under `--reuse-across-call` (a
    Reussir bug), so they (and `dbgTraceIfShared`, an FFI import) reach it
    from Rust (`leanrt::io::diag_put`) through the trampoline
    `extern "C" trampoline "l2r_stderr_put_c" = l2r_stderr_put;`, which
    lean2rr must emit in every program (a weak symbol: without it they go
    to descriptor 2; test `RtStreamsRedirectOob`).
22. *done* — `String.mk`/`List.asString` (`lean_string_mk`) take a `List Char`: glue
    folding the list with `lean_string_push` onto `lean_mk_string("")`.
23. *done* — `IO.initializing` is true while module initializers run (native
    `g_initializing` until `lean_io_mark_end_initialization`): the entry
    should call `l2r_set_initializing(true)` before the initializers and
    `l2r_set_initializing(false)` after (test `RtInitializing`).
24. *done* — Native `main` runs the module initializers on the process's main thread
    (8 MiB stack) and only `main` on Lean's big thread: the entry should be
    `leanrt::rt::run_main2(|| init(), || body())`, which runs `init` on the
    calling thread (with the stack-overflow report) and then `body` as
    `run_main` (test `RtInitStack`: a deep initializer overflows natively).
    An initializer's uncaught error prints `uncaught exception: ...` and
    exits 1 without running `main`, as natively.
25. *done* — `IO.getEnv` (`lean_io_getenv`) is emitted as a direct call to
    `lean_io_getenv`, which the prelude cannot define (its result is
    `Option String`); use `l2r_io_getenv_with(name, none, some)`.
26. *done* — `IO.Process.forceExit` (`lean_io_force_exit`, `std::_Exit`: nothing is
    flushed) has no glue: as `IO.Process.exit`, with
    `l2r_process_force_exit(code)` (test `RtForceExit`).
27. *done* — `Nat.repr`/`Int.repr` (request 12): besides the quadratic big case,
    `Nat.reprFast` clones the `Nat.reprArray` once-cell and drops it out of
    line for every number ≥ 128 (13% of the Sieve benchmark).
28. *done* — `ByteSlice.beq` needs glue (`l2r_byteslice_beq` above);
    `ShareCommon.State.shareCommon` (`lean_state_sharecommon`, hash-consing
    natively) can use its reference body `(a, s)`, which is observably the
    same (sharing is not observable here).
29. *done* — Child processes: `IO.Process.spawn` and `Child.wait`/`tryWait`/`kill`/
    `pid`/`takeStdin` need glue over the `l2r_proc_*` primitives (above).
    Natively a `Child` object also carries the pid (`uint32`) and whether it
    was spawned with `setsid` (`uint8`) after its three Lean fields, so
    lean2rr's `Child` record needs those two extra fields, set by the spawn
    glue and kept by `takeStdin` (test `RtProcess`). `IO.Process.output`
    should use `l2r_proc_drain` (above) instead of its task-based reads.
30. *done* — `Lean.Name.beq` (`lean_name_eq`): the prelude cannot define it (`Name`
    is a Lean type); its reference body (structural equality) is what the
    native code computes.
31. *done* — `ptrAddrUnsafe` of a value lean2rr wrapped at the call
    (`ElemBox{x}`, function-value wrappers) measured the temporary wrapper,
    whose memory the next wrapper can reuse. lean2rr now takes the value in
    its own representation (not converted for the call): a heap value's
    handle goes to `l2r_ptr_addr_obj`/`l2r_ptr_addr_rec`, which answer the
    pointer whatever the count (`ptrEq a b` may release `a`'s last other
    reference before `b`'s address is taken), and a `[value]` struct
    answers its field's (translation plan §9; tests `RtPtrAddr`,
    `RtPtrSound`).

For Reussir: `[value]` records across the FFI boundary would let arrays
store enum-like values directly; and `mi_free` takes mimalloc's
generic path (`mi_free_generic_local`, `_mi_page_ptr_unalign`) for most
frees in allocation-heavy loops (30% of an array-update benchmark).

## Known divergences from native Lean

- Panics print `backtrace:` and `(stack trace unavailable)` instead of a
  stack trace (unless `LEAN_BACKTRACE=0`, which prints neither, as native).
- Sharing is not observable: `isExclusiveUnsafe` answers `false`, and
  `dbgTraceIfShared` of values held by value (`[value]` structures, small
  `Nat`s) never reports sharing. Pointer identity is not emulated (translation
  plan §9): `ptrAddrUnsafe` answers the handle pointer of a heap value in
  its own representation (`l2r_ptr_addr_obj`, `l2r_ptr_addr_rec`, which
  give the reference back inline), the boxed scalar `2n+1` for
  `UInt8/16/32`, `Char`, `Bool`, enumerations and `Unit` (`l2r_addr_word`),
  a `Nat` or `Int` its own word, which is native Lean's (`l2r_addr_nat`,
  `l2r_addr_int`: the boxed scalar when small, else its big number's
  pointer), the bits of a `UInt64` or `Float`, and a number answered only
  once (`l2r_addr_fresh`: even, in `[2^62, 2^63)`) for a value of a type
  `addrOf` does not know. For two values alive at the same time, equal answers
  mean the same cell or equal values; a value lean2rr converted to another
  representation is a new object.
- Everything runs on one thread: tasks run when they are first needed,
  when the running code blocks, or when `main` returns (a schedule native
  Lean can produce; translation plan §5.14). Contexts switch only when one
  blocks or at an effect point (above): a loop polling shared state that
  another task sets without sleeping or output never sees it change, a
  context that computes without blocking or output delays the others,
  and `IO.waitAny` does not pick the fastest of several unfinished tasks.
  Blocking system calls (reading a file, pipe or standard input, waiting
  for a child, name resolution) block the whole program: code that reads
  one of a child's pipes in a task while it reads the other itself (as
  `IO.Process.output` does natively, stdout in the task; its glue drains
  both together) deadlocks if the child writes more than a pipe holds
  (64 KiB) to the task's pipe before closing the other one.
- Child processes: natively `Child.pid` leaks its argument (Lean passes
  the child owned, the C function treats it as borrowed), so the child's
  pipes are never closed after a `pid` call, and a child waiting for end of
  file on its stdin after `takeStdin` waits forever; lean2rr releases it
  as usual. Natively the `Child` that `takeStdin` returns does not copy the
  `setsid` flag (its byte is uninitialized memory, read by `kill`); here it
  is kept. `IO.Process.output` reports a non-UTF-8 stderr once both pipes
  are at end of file (natively as soon as stderr is; a grandchild can hold
  stdout open), and a read error on either pipe at once (natively a stdout
  read error after `wait`); the bytes and messages are the same, only when
  it happens differs.
- `IO.getNumHeartbeats` is 0 (natively it counts small allocations);
  `dbgStackTrace` prints nothing.
- The C `errno` reported by a handle's sticky error indicator (see file
  primitives) is the current `errno`, which may differ from native after
  unrelated failing calls (the runtime's own calls are not libc++'s).
- `IO.FS.createTempFile`/`createTempDir` with `TMPDIR` naming a missing
  directory report `no such file or directory` with an empty file name;
  natively `decode_uv_error` dereferences a null file name and crashes.
  The same crash happens natively whenever an error without a file name
  has errno `ENOENT` or `EINTR` (e.g. `getLine` on a handle whose error
  indicator is set, after a failed `metadata` left `errno = ENOENT`); the
  runtime reports `no such file or directory` with an empty file name.

## Testing

`tests/runtime/run.sh [NAME...]` builds every `tests/runtime/Rt*.lean`
natively (`lean` + `leanc -O3 -DNDEBUG`, like Lake's release build) and
through lean2rr, runs both (`LEAN_BACKTRACE=0`, optional `NAME.args` and
`NAME.stdin`; `NAME.pipe` is a shell command line run instead, with `$BIN`
the program, for redirections and pipes), and compares stdout, stderr and
the exit code byte for byte. `NAME.xfail` marks tests blocked by a lean2rr
request. The Rust unit tests of `leanrt` (bignums, one-word `Nat`/`Int`
at the boundaries, tagged arrays, hashes, the lookup of glibc's `cbrt`,
and a differential test of the `FILE` model against glibc's own `FILE`
over random operation sequences)
run with `tests/runtime/leanrt-unit.sh`. `tests/runtime/nat-alloc-check.sh`
builds `RtNatStress` with leanrt's big-number counters and checks that
every big number made is freed exactly once. `tests/runtime/conv-count-check.sh`
builds `RtUniformUpdates` and `RtUniformUpdatesJp` with lean2rr's
conversion counter (`L2R_COUNT_CONVERSIONS`: each generated conversion
counts the elements it rebuilds, printed at exit) and checks that they grow
at most linearly with the size (no container converted per update).
