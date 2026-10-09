# lean2rr: what is implemented

Status as of 2026-10-05 (`dev`, Lean v4.34.0). This is a plain-language overview
for someone who knows Rust but not Lean. The full rules are in
[`translation-plan.md`](translation-plan.md); the runtime is described in
[`../runtime/README.md`](../runtime/README.md); the Reussir issues met on
the way (bugs, costs and the others) are in
[`../reussir-bugs/`](../reussir-bugs/README.md). The implementation's
tricks and special cases, each with its reason, its place in the code and
what would break without it, are cataloged in
[`implementation/`](implementation/README.md). An illustrated overview of
the design, with diagrams, is [`site/index.html`](site/index.html).

## In one paragraph

lean2rr compiles Lean 4.34 programs to native executables through
Reussir. It does not parse Lean source: it reads what Lean's own compiler
already produced for a compiled module (its intermediate code, LCNF, stored
in the `.olean` files), so every Lean feature that Lean can compile is
input lean2rr understands (dependent types, type classes, `do` notation,
mutual and nested inductives, `partial`/`unsafe` definitions, macros…: by
then they are all ordinary functions and data). lean2rr turns that into
typed Reussir source, Reussir compiles it (reference counting and in-place
reuse of memory are Reussir's job), and a small runtime library supplies
what Lean's C runtime supplies natively (big numbers, strings, files,
processes, tasks, sockets…).

```
scripts/l2r.py Main.lean -o main      # or: scripts/l2r.py ModuleName -o main --lean-path DIR
```

The driver runs lean2rr, then Reussir's `rrc`, and links the runtime.
Everything is checked against the native build of the same program:
same standard output, standard error and exit code.

## Where it stands

| Check | Result |
|---|---|
| Classic benchmark corpus (18 programs × 3 input sizes, `tests/classic`) | all outputs identical to native (Lean 4.34.0's outputs are those recorded with 4.33) |
| Runtime test suite (596 programs, `tests/runtime`) | at its last full run (the combined gate on dev acb6375e, 2026-10-08, lean-runtime 50840bb, Reussir upstream 943f2195 + 35 patches), 586 of 588 identical to native Lean 4.34.0 and 2 expected failures (`RtLeanUnsupported`, `RtCastMixedRebox`); the classic corpus 36 of 36 (18 programs at two sizes) with all optional passes on and with all off, and 18 of 18 with `unread-fields` on; every check passes (14); the raytracer's images equal native's. At the gate of switch step 10 ( branch `lean-runtime-step10` at 0410be6 on dev d39294a, lean-runtime e5e502e, 2026-10-06), 336 of 337 identical to native Lean 4.34.0 and 1 expected failure (`RtLeanUnsupported`); the classic corpus 54 of 54 with all optional passes on and with all off; the Reussir benchmark suite 18 of 18. At the gate of `perf-const-reads` (e7bc212 on dev 9a2ddf6, lean-runtime 83f7127, 2026-10-06), 331 of 332 identical to native Lean 4.34.0 and 1 expected failure (`RtLeanUnsupported`). At the gate of switch step 8 (branch `lean-runtime-step8` at 8e5c5eb on dev d3032e4, lean-runtime e34cd61, 2026-10-05), 326 of 327 identical to native Lean 4.34.0 (`RtNetEffectPoll` counted after one re-run: in the gate's run its native build printed `accepted during the loop: false`, a timing flake of native's that its re-runs did not repeat; lean2rr's output was the expected one), nine of them through expectation files: eight where lean2rr does not reproduce a Lean runtime bug (`RtReadAfterWrite`, `RtStdioStdoutRead`, `RtErrorNoFileName`, `RtProcessNullFd`, `RtProcessNullOpenFails`, `RtStartupFdExhausted`, `RtRefSetDuringModify`, `RtRefSwapDuringModify`; plan §10, "Runtime: Lean bugs we do not reproduce"), and `RtCseFnResult` (its trace prints once natively and twice through lean2rr, which Lean allows: plan §10, "Merging after erasure"); 1 expected failure: `RtLeanUnsupported` (an expected refusal until the runtime has the `Lean` package's C++ functions); five tests (`RtExternRefused`, `RtExternOpaqueRepr`, `RtExternOpaqueRedecl`, `RtExternPrivate`, `RtCastExtern`) check that lean2rr refuses an extern it cannot serve; `RtLiftedLimits` and `RtInternalPanic` compare each side with its own expectation files where lean2rr lifts a limit of Lean's runtime (plan §10, LB-04 to LB-12). lean-runtime's own program cases through lean2rr's builds: of its IO areas (io, process, streams, temp, uvsys, time) 90 of 90 at lean-runtime 9d27ce0 (switch step 5); of its task areas (tasks, sync, refs, taskio, uvloop, net) 163 of 163 at lean-runtime ed1e8af (switch step 6), a subset of 26 of them (references shared with tasks, promises) 26 of 26 at 528fcbb (switch step 6), at 471f458 (switch step 7) a subset of 39 (those 26, the other `sync` cases, `tasks/poll_threshold_mutex`, and the startup and title cases `io/initializing`, `io/startup_*`, `uvsys/process_title`, `uvsys/title_*`) 39 of 39, and at e34cd61 (switch step 8) a subset of 94 (those 39, 31 panic, exit and stream cases such as `panics/replicate_overflow`, `process/output_*oom*`, `tasks/get_in_sync_task*`, `tasks/promise_in_initialize*`, `io/exit_*`, `streams/stream_redirect`, and the 27 `net` cases) 94 of 94 |
| Reussir's own benchmark suite (18 Lean programs, used unchanged) | 18/18 identical to native |
| Applications (`tests/apps`: lean4-raytracer, two modules, built with Lake) | the image file, stdout, stderr and exit code identical to native at all three settings (60×40 pixels on the main thread and in one task; 200×133 pixels, 4 samples per pixel, depth 30, on the main thread), dev e1e5dde, 2026-10-07 |
| The corpus with every optional optimization turned off | 18/18 identical (the core translation is correct on its own) |
| Lean library C functions (externs) of `Init` and `Std` | all 717 of Lean 4.34 (767 declarations) available: 706 checked by programs that call each one, the other 11 (internal or private helpers) by direct tests |
| Adversarial testing | 9 review rounds (the first 4 wrote about 1,300 test programs to break it; the later ones work by inspection with targeted programs), Lean's own compile tests (72 programs of `tests/compile` and `compile_bench`, Lean 4.33: all identical), and cross-tests on 550 external fixture programs (542 identical; the 6 causes of the 8 differences are XT-1 to XT-6, XT-6 fixed, XT-1 to XT-5 fixed (merged 36a5f92)); every other finding fixed or documented |
| Speed (classic corpus against native Lean 4.34.0, 2026-10-04) | faster than native Lean on 15 of the 18 classic programs and about equal on the other three (bignum 1.00×, binarytrees 1.02×, nqueens 1.04×); geometric mean 0.71× time, 0.69× memory; less memory on all 18. Reussir's suite last measured against 4.33 (faster on 17 of 18); tables below |

## How a program is compiled

1. **Collect and monomorphize.** Starting from `main`, lean2rr collects
   every function the program uses and makes a separate copy of each
   function for each type it is used at (as Rust does with generics):
   `List.map` at `Nat` and at `String` become two functions. Data keeps one
   layout per datatype: `List Nat` and `List String` are one Reussir type,
   whose element is a one-word box (dependent types, rule 1). lean2rr
   recovers precise types for parameters, results and local values where
   Lean erased them.
2. **Lean's optimizations.** lean2rr runs Lean's own optimization passes
   (inlining, specialization, case-of-known-constructor…) on the
   monomorphic code, with two passes replaced so they keep types.
3. **Check and recover types.** Places where Lean's types say "unknown"
   (`lcAny`) get their real type back where it can be inferred from callers
   and callees.
4. **Lower to Reussir.** Each function becomes a Reussir function, each
   type a Reussir record or enum. Join points (Lean's local continuations)
   become inline code, loops or small functions; function values become
   data (below).
5. **Reussir** compiles the `.rr` file with LLVM, inserting reference
   counting and reusing memory cells in place when they are unique.

## How Lean values are represented

Think of each Lean type as becoming a Rust type.

### Numbers

| Lean | Reussir / runtime | Notes |
|---|---|---|
| `Nat` (natural numbers, unbounded) | `Nat`, one machine word, as natively | see below |
| `Int` (unbounded integers) | `Int`, one machine word, as natively | small in the 32-bit range |
| `UInt8/16/32/64`, `USize` | `u8/u16/u32/u64`, `u64` | 64-bit targets only |
| `Int8…Int64`, `ISize` | the same unsigned words, signed operations on the bit pattern | as Lean's C runtime does |
| `Float`, `Float32` | `f64`, `f32` | printing follows Lean's exactly |
| `Char` | `u32` | |
| `Bool` | `bool` | |

**How `Nat` works.** A `Nat` is one machine word, as in native Lean: a
small value `n` (below 2^63) is stored in the word itself as `2n+1` (an
odd number), and a bigger one is a pointer (an even number) to a
reference-counted big number. Arithmetic on two small values is inline
code: `a + b` is a test of both low bits, an add and an overflow check;
only a big operand or an overflow calls the runtime. Big numbers use GMP
(the same library Lean uses), stored as a reference-counted sign and limb
vector, updated in place when unique. `Nat.repr` (printing) of big
numbers uses GMP too. Lean's rules (subtraction stops at 0, division by
0 gives 0, the limits of shifts and exponents, which result is too big)
are those of the shared crate lean-runtime, written once for both Lean
translators that use it: the runtime calls them for everything but the
inline small cases, with its GMP numbers behind lean-runtime's big-number
traits.

Reussir generates the reference counting itself, and normally treats every
handle as a pointer whose count it increments when the value is copied. A
small `Nat` is not a pointer, so lean2rr declares `Nat` and `Int` as
*tagged* opaque handles, a small local Reussir extension (patch 41-a):
Reussir counts such a handle only when its low bit is clear, exactly as
Lean's C runtime tests the bit before every count update. Copying or
dropping a small `Nat` is a bit test; it is never allocated.

`Int` works the same way, with Lean's encoding too: a value in the 32-bit
range is stored in the word, any other is a big number. Every result is
normalized (a big number never holds a value that fits the word), so a
small and a big `Int` are never equal: that comparison needs no call
(switch step 10, after an audit of every place that makes an `Int`;
builds with debug assertions check the rule where a big `Int` is made and
read).

A small value is exactly Lean's `lean_box(n)`. A big number is lean2rr's
own: one block with the reference count, the sign and size, and the limbs
(native Lean's `lean_mpz_object` keeps the limbs in a second allocation,
made by GMP). C code written against `lean.h` could take the small words
as they are and a big number after a conversion, but calling a program's
own C code is not supported (below).

Compared with native Lean:
- a `Nat` or `Int` field in a record takes 8 bytes, as natively;
- a big number is one allocation (natively two: the object and GMP's
  limbs), 32 bytes for a two-limb number (natively 56);
- a `Nat` in the generic `Box` (a field or an array element of a type
  parameter's type, code whose types cannot be made concrete, below) is
  its own word when small, as natively: boxing it allocates nothing.

Peak memory (max RSS, 2026-10-03, against the native build): `rbmap`
(a red-black tree with `Nat` keys and values) 0.84× (with the earlier
two-word `Nat`: 1.00×); an array of 2 million records with four `Nat`
fields and a list of `Nat` pairs 0.80× (1.26×); `bignum` about 1.1×
(1.2–1.3×; a few MB, noisy). With big numbers in one block (perf-big,
2026-10-03, measured without transparent huge pages, which round RSS to
2 MiB steps): a million live two-limb numbers 49.5 MB, 0.67× native
(65.2 MB with the two-allocation layout); the classic Bignum 3.6 MB and
Liasolver 5.8 MB, within a few hundred KB of the two-allocation layout
(3.2 and 5.5 MB) and below native (5.8 and 7.4 MB).

### Text, arrays, references

| Lean | Representation | Notes |
|---|---|---|
| `String` | runtime `LStr`: one block like Lean's string object (reference count, byte size, capacity, character count, then the UTF-8 bytes) | copy-on-write: modified in place when unique, like Lean |
| `Array α` | runtime vector of boxes, one word each, for every `α` without a storage kind: one block, header (count, size, capacity) then the elements | in place when unique; a small `Nat` is the word itself, a `Float` a cell, as natively |
| `Array S`, `S` a scalar | runtime vector of the scalars inline: `u8` (`UInt8`, `Bool`, an enumeration of at most 256 constructors), `u16`, `u32` (`UInt32`, `Char`), `u64` (`UInt64`, `USize`), `f32`, `f64` (`Float`) | optimization `compact-arrays`, per storage kind, when the program's array of that kind never reaches generic code (a whole-program check); otherwise an array of boxes |
| `ByteArray`, `FloatArray` | arrays of `u8`, `f64` | `ByteArray.mk`/`data` are the identity with a compact `Array UInt8`; with an array of boxes they copy the elements in one loop, as natively |
| `IO.Ref α` / `ST.Ref` | a shared mutable cell | mutations seen through every alias, as in Lean |
| `Thunk α`, `Task α` | a shared cell holding a state machine (pending / running / done) | lazy, computed once |
| file handles, processes, sockets, timers | runtime handles | closed when the last reference goes, as in Lean |

### Your own types

Each inductive type becomes one Reussir type, whatever its type
arguments, with the same constructors and fields. A field whose type is a
type parameter is a `Box` (one word, as Lean's `lean_object*`):

```
inductive Tree α | leaf | node (l : Tree α) (k : α) (r : Tree α)
```

means "a `Tree α` is either `leaf` or `node` with a left subtree, a value
and a right subtree", and for every `α` it becomes roughly

```rust
enum Tree { leaf, node(Tree, Box, Tree) }   // heap-allocated, reference counted
```

A type whose constructors have no fields (like `Ordering`) is a plain value
enum, never allocated. A structure with one field is represented by that
field. Fields are reordered by size so records have no padding.

### Functions and closures

A function value (a closure, a partial application, `fun x => …`) becomes
data: one generated enum per function type, with one variant per function
that can be stored there plus its captured variables, and an `apply`
function that matches on it (defunctionalization). Calls of known
functions are direct calls; tail calls become loops.

### Polymorphic code that cannot be made concrete

Monomorphization makes almost everything concrete. What stays generic
(polymorphic recursion such as a monad transformer applied to itself, or
an unsafe inductive family holding itself at a larger index, `Nest (α × α)`
in `Nest α`; existential types; values stored in `Dynamic`) uses a uniform
type `Box`: one word, which holds a small value itself or points to an
object and records the object's type number. Each datatype has one
layout, so a value goes into a box and out of it as it is: nothing is
rebuilt.

## An example

Input (`Example.lean`), with comments for Rust readers:

```lean
-- Rust: enum Tree { Leaf, Node(Box<Tree>, Nat, Box<Tree>) }
inductive Tree where
  | leaf
  | node (l : Tree) (key : Nat) (r : Tree)

-- fn insert(t: Tree, k: Nat) -> Tree, by matching on both arguments
def insert : Tree → Nat → Tree
  | .leaf, k => .node .leaf k .leaf
  | .node l x r, k =>
    if k < x then .node (insert l k) x r
    else if x < k then .node l x (insert r k)
    else .node l x r                        -- key present: the same tree

def sum : Tree → Nat
  | .leaf => 0
  | .node l x r => sum l + x + sum r

def main : IO Unit := do
  let t := [5, 3, 8, 1, 4].foldl insert .leaf  -- iter().fold(Leaf, insert)
  IO.println s!"sum = {sum t}"                 -- format!("sum = {}", …)
```

Output (`scripts/l2r.py Example.lean -o example --keep-rr Example.rr`),
trimmed to the program's own functions and lightly simplified (a few
temporary `let`s folded, comments added; the full file is generated by
the command above):

```rust
enum T_Tree_346 {                       // heap cells, reference counted by Reussir
    c_leaf,
    c_node(T_Tree_346, Nat, T_Tree_346)
}

fn l_insert___l2r_0_(a347 : T_Tree_346, a348 : Nat) -> T_Tree_346 {
    match a347 {
        T_Tree_346::c_leaf => {
            let nc349 : T_Tree_346 = T_Tree_346::c_leaf{};
            let x350 : T_Tree_346 = T_Tree_346::c_node{nc349, a348, nc349};
            x350
        },
        // only the key is taken here: the tree itself may be returned
        T_Tree_346::c_node(_, f352, _) => {
            let x354 : bool = lean_nat_dec_lt(a348, f352);          // k < x
            if x354 {
                // matched again where the old node dies, so Reussir can
                // reuse its memory for the new node (in place when unique)
                match a347 {
                    T_Tree_346::c_node(f355, f356, f357) => {
                        let x358 : T_Tree_346 = l_insert___l2r_0_(f355, a348);
                        let x359 : T_Tree_346 = T_Tree_346::c_node{x358, f356, f357};
                        x359
                    },
                    _ => { l2r_unreachable<T_Tree_346>() }
                }
            } else {
                // … the same for k > x, going right …
                a347                                               // key present
            }
        }
    }
}

fn l_sum___l2r_0_(a372 : T_Tree_346) -> Nat {
    match a372 {
        T_Tree_346::c_leaf => { l2r_nat_small(0) },
        T_Tree_346::c_node(f374, f375, f376) => {
            let x377 : Nat = l_sum___l2r_0_(f374);
            let x378 : Nat = lean_nat_add(x377, f375);    // inline add, overflow → big number
            let x379 : Nat = l_sum___l2r_0_(f376);
            lean_nat_add(x378, x379)
        }
    }
}

// main: the list, the tree, the sum and the message depend on no input, so
// Lean made them a constant, computed once on first use and cached; IO is
// a function of a world token returning ok or an IO error.
fn l_main___l2r_0_(a420 : L2RUnit) -> T_EST_Out_381 {
    let x421 : LStr = l_main___l2r_0____closed__9();
    l_IO_println___at___00main_spec__1___l2r_0_(x421, a420)
}
```

Both the native build and this one print `sum = 21`. The whole `.rr` file
is longer (the runtime prelude, and the `IO` error types and printing that
`IO.println` brings in); Reussir then adds reference counting and memory
reuse when it compiles it.

## What is supported

Everything a Lean program can do through `Init` and `Std`, with the
exceptions listed further down:

- **All of the language** (it arrives already compiled by Lean).
- **Program structure:** `main` with or without arguments and exit code,
  module initializers and `initialize` declarations (run in Lean's order,
  taken from what the `.olean` records; under the module system, `meta`
  declarations and `meta import`s run only where natively they do),
  `IO.initializing`, top-level
  constants computed once on first use, `@[extern]`/`@[export]` functions
  implemented in Lean, `@[implemented_by]`.
- **Numbers and data:** `Nat`/`Int` of any size, fixed-width integers,
  `Float`/`Float32` (with Lean's exact printing), `Char`, `String` (all of
  the library: slices, iterators, UTF-8 validation, `toNat?`, …), arrays,
  byte and float arrays, `HashMap`/`HashSet`/`TreeMap`, lists, options…
- **Errors:** `panic!` and `get!`-style failures print Lean's message and
  continue with the default value, as natively; `IO` errors with Lean's
  error kinds and messages; `throw`/`try`/`catch` in `IO` and `ExceptT`;
  stack overflow is reported with Lean's message and exit status.
- **Files and the system:** reading and writing files (buffered like glibc),
  directories, metadata, links, temporary files, locks, the standard
  streams and their redirection (`IO.setStdout`, `withIsolatedStreams`),
  environment variables, the current directory, time (`IO.monoMsNow`,
  `IO.monoNanosNow`, and the wall clock: `Std.Time.Timestamp.now`), random
  bytes, `IO.Process.exit`.
- **Child processes:** `IO.Process.spawn`, `output`, `run`, pipes, `wait`,
  `tryWait`, `kill`.
- **Tasks and concurrency:** `Task.spawn`, `map`, `bind`, `IO.asTask`,
  `IO.wait`, `IO.waitAny`, cancellation, priorities, promises,
  `IO.Ref`-based state, `Std.Sync` (mutexes, recursive and shared mutexes,
  condition variables, channels built on them).
- **Asynchronous IO (`Std.Async`/`Std.Internal.UV`):** timers and sleeps,
  TCP and UDP sockets, name resolution (DNS), signals, network addresses.
- **Debugging helpers:** `dbgTrace`, `dbgTraceIfShared`, `timeit`.

### How tasks run

Tasks run on one thread, on the shared crate lean-runtime's scheduler
(switch step 4): there is no parallelism. A task runs when its value is
needed, when the running code blocks (sleeping, waiting for a lock, a
promise, a socket, an empty pipe), or when `main` returns; contexts switch
at those points, at output and at polling points (task-state questions,
clock reads, every 1000th reference read), in an order native Lean's
scheduler could have used. In a program that creates tasks (lean2rr
decides it at translation time, from the externs the program reaches) a
reference's `get`, `set` and `swap` wait while a `modify` of it is blocked
(Lean 4.35's rule); a program without tasks pays nothing for any of this:
its code is the same, and the scheduler does not start. Programs get the
same output as natively as long as their output does not depend on timing
races. A pool task's standard streams are its emulated worker's, kept from
one task to the next, and a task's `sync` dependents see the streams it
left, as natively. lean2rr's generated task code is the same as before
the switch: its task primitives call lean-runtime.

### Memory

Reference counting and in-place reuse are done by Reussir. Freeing a deep
structure (a long list, a deep tree, nested arrays) uses a stack of
pending work instead of recursion, as Lean does, so it never overflows the
stack; resources inside (file handles) are closed in Lean's order. Memory
use is usually at or below native (Reussir's records and reuse are
tighter). Strings and arrays are single blocks with Lean's own header
sizes (six million three-element `Array Nat` rows: 328 MB, native
330 MB). Like natively, a hash table of 2^21 buckets (`Std.HashMap` with
about a million keys) needs a block just past mimalloc's large-object
limit, which is returned to the system late: such programs peak up to a
quarter higher than they did when arrays kept their elements apart.

## What is not supported, or differs from native

Translation always succeeds; the differences are behaviours that cannot
match because the information is not in the `.olean`, because there are no
real threads, or because they read raw memory addresses. The full list,
with examples, is §10 of the translation plan.

- **No parallelism** (see "How tasks run"). Output that depends on timing
  races between tasks can come out in another order (natively a race).
- **An internal panic in a program with tasks** (`INTERNAL PANIC: ...`,
  the end of the program) does not wait for a write to stderr in progress
  by another context (a task or `main`, suspended in it on a full pipe),
  and, from the thread that drains `IO.Process.output`'s stdout after a
  failure, for any write to stderr in progress: its line can land inside
  that write, where natively it comes after it. Same bytes; without tasks
  it waits as natively (lean-runtime's `io::panic`, switch step 8).
- **Pointer identity and raw addresses** are not preserved: `ptrAddrUnsafe`
  answers the address of the value's own cell, or a word computed from a
  scalar value (`UInt64` and `Float` their bits), so `ptrEq`,
  `ptrEqList` and `withPtrAddr` may answer otherwise than natively (a
  value cast to an inductive whose layout differs is a new object, not
  `ptrEq` to its original), but `ptrEq` answering `true` still means equal values,
  and `IO.Ref.ptrEq` is exact. Casting an object to a number
  (`unsafeCast` to read an address) gives a deterministic stand-in
  instead of a real address.
- **Startup order** of a few constants Lean compiled without recording an
  order (members of one `mutual` block that do not use each other, some
  macro-generated names) is chosen by lean2rr; visible only if their
  initialization prints or panics.
- **Per-module compiler options** (`set_option compiler.…`) are not
  recorded in the `.olean`, so Lean's defaults are used.
- **Order of a few releases:** when user code drops a record holding
  several file handles by itself, they can be closed in another order than
  natively.
- **Stubs:** `IO.getNumHeartbeats` is 0, `isExclusiveUnsafe` answers
  `false`, `shareCommon` shares nothing (and `ShareCommon.Object.eq` holds
  at most for the same object, by address), a panic's backtrace line says the trace is
  unavailable; the Windows-only time zone functions fail as they do
  natively on other systems.
- **Lean runtime bugs not reproduced** (plan §10, "Runtime: Lean bugs we
  do not reproduce", from lean-runtime's docs/lean-bugs.md): an
  `IO.Ref.set` from a task is never undone by a concurrent `get` (natively
  it can be, LB-01, fixed in Lean 4.35), nor overwritten by a blocked
  `modify`'s store (LB-01's other half; a `swap` then gets modify's value,
  LB-18); a pool task enqueued
  after `main` returned still runs (LB-13); timers, signal watchers and
  sockets follow lean-runtime's fixes of LB-19 to LB-28, LB-33 and
  LB-34; a waiter of a
  dropped promise's `result!` walk wakes (LB-32); a read of at
  least one buffer right after output on the same handle writes the
  pending output first, where natively glibc drops it (LB-02); an error
  without a file name (`getCurrentDir` after its directory was removed) is
  the class's `IO.Error` with an empty file name, where natively the
  program crashes (LB-03); a child's `null` stream leaves the program no
  extra descriptor on `/dev/null` (natively one per `null` stream, LB-15),
  and when `/dev/null` cannot be opened the spawn fails with `EMFILE`,
  where natively the program silently gets the parent's own stream
  (LB-17); after `takeStdin`, `kill` still reaches a `setsid` child's
  process group (LB-14); an over-long temporary directory is an `IO.Error`
  (natively an assertion abort, LB-16); startup without room for the event
  loop's descriptors ends with an `INTERNAL PANIC` (natively a crash or an
  abort, LB-30, LB-31); an exit never waits for a stream held by a blocked
  reader (LB-29); a fresh `append` handle's cursor is at the end of the
  file, so `truncate` keeps the content (natively it empties the file,
  LB-46), and `EBADMSG` is `inappropriateType`, as `IO.Error` documents
  (LB-47). These IO behaviours, and all of lean2rr's IO, are the
  shared crate lean-runtime's (its `io` module), which lean2rr calls
  through glue over its own values. Limits of Lean's runtime are lifted where the
  result can be computed: `Nat.pow` with an exponent of 2^32 or more
  (`1 ^ e`, `0 ^ e`, and any power that fits, LB-11), `Nat.shiftLeft` and
  `Nat.shiftRight` by 2^32 or more (LB-12, LB-04), `ByteArray.copySlice`
  with an offset or length of 2^64 or more (LB-06); a power too big for
  GMP ends at once with `INTERNAL PANIC: out of memory`, where natively
  GMP kills the program with SIGFPE (LB-05).
- **Lean compiler bugs not reproduced** (plan §10, "Compiler: Lean bugs we
  do not reproduce"): a `match` whose one arm gives a type or a proof and
  whose other arm gives data computes with the data, as the kernel does,
  where native Lean's join point reads `◾` (the boxed 0) in its place and
  gives a wrong value or a crash (`joinTypes` types the parameter `◾`;
  tests `RtJoinErased*`).
- **Lean code only, plus Lean's runtime library** (the owner's decision,
  2026-10-03). The C code of a program or of a package it requires
  (Lake's `extern_lib`) is never compiled, linked or called: an
  `@[extern]` of the program runs the program's own `@[export]` definition
  its C symbol binds to (same type, one compiled signature), else its Lean
  definition (lean2rr's build prints a note listing them); one with
  neither (an `opaque`) is rejected at translation, with the reason
  (translation plan §5.8, "Externs of the program"). An extern of the
  program is never bound to Lean's runtime (the owner's decision,
  2026-10-04): one naming a runtime symbol runs its own definition, or is
  rejected with the name of Lean's declaration to call instead (and the
  module to import, if the program does not). Where the package's C and
  the Lean definition differ, the translation follows the Lean
  definition; where the extern's C symbol is an `@[export]` whose
  binding's tests fail, lean2rr warns. The C FFI work (branch `ffi-c`)
  stays parked.
- **`import Lean` programs** (metaprogramming: the elaborator, the kernel,
  the code generator): the `Lean` library declares 196 more C functions,
  and those implemented in Lean's C++ are not available: expression and
  universe-level internals (`Expr.mkData`, `Expr.equal`, `Level.mkData`),
  `evalConst`, loading shared libraries (`Dynlib`), the LLVM bindings,
  `profileit`, `maxSmallNat`. lean2rr rejects a program that reaches one
  of them, naming each (their Lean bodies are not used in their place);
  one that only uses data structures from `Lean` builds.
- **Build time:** rrc compiles about 80 small functions per second, so a
  program with thousands of constants takes minutes to build (native:
  seconds). Very large literals and monad-transformer towers build, in
  seconds to a few minutes.

## Performance

Measured on this machine (aarch64, 20 cores) in a timing window on
2026-10-04 (the other jobs paused, load 0.9 to 1.25), each program's
lean2rr and native builds run alternately, pinned to the least-loaded fast
core; best of 5; time ratio = lean2rr time / native time (below 1 =
faster than native). Every run's output was checked against native.
`dev` 4fbc6d5 (all 17 optional passes on), Reussir `l2r-local` at
`d79f8b70` (37 local patches), against native Lean 4.34.0
(`python3 tests/oracle.py bench --cmd 'out/{exe} {size}'`).

**Classic corpus** (`tests/classic`, largest size):

| program | native s | lean2rr s | time × | memory × |
|---|---|---|---|---|
| typeclass-generic | 2.08 | 0.84 | 0.40 | 0.59 |
| rbmap | 1.87 | 0.84 | 0.45 | 0.83 |
| liasolver | 2.08 | 0.94 | 0.45 | 0.83 |
| rbtree | 1.85 | 0.85 | 0.46 | 0.83 |
| deriv | 6.46 | 4.16 | 0.64 | 0.77 |
| unionfind | 0.97 | 0.64 | 0.66 | 0.78 |
| mergesort | 1.33 | 0.89 | 0.67 | 0.55 |
| rbtree-ck | 1.33 | 0.92 | 0.69 | 0.83 |
| higher-order | 2.25 | 1.56 | 0.69 | 0.67 |
| strings | 1.57 | 1.17 | 0.75 | 0.80 |
| sieve | 1.38 | 1.14 | 0.83 | 0.31 |
| cfold | 0.72 | 0.63 | 0.88 | 0.75 |
| qsort | 1.12 | 0.99 | 0.88 | 0.64 |
| monadic-interp | 1.81 | 1.66 | 0.92 | 0.66 |
| hashmap | 1.51 | 1.46 | 0.97 | 0.98 |
| bignum | 2.28 | 2.27 | 1.00 | 0.59 |
| binarytrees | 2.71 | 2.76 | 1.02 | 0.62 |
| nqueens | 3.52 | 3.67 | 1.04 | 0.75 |

Geometric mean: 0.71× time, 0.69× memory. At the medium size (0.1 to 1 s
natively) the geometric mean is 0.75× time and 0.67× memory, with deriv at
1.37× (0.52 s against 0.38 s; not yet explained); at the small size the
times are below the tool's resolution, and every program uses less
memory than natively (about 5.5 MB against 7.8 MB at startup).

Against the previous measurement (dev 9f5b642 against native Lean 4.33,
on a loaded machine): native Lean 4.34 is faster on several programs
(mergesort 2.11 s → 1.33 s, binarytrees 3.07 s → 2.71 s), so some ratios
rose while lean2rr's own times stayed about the same; memory fell on
every program, most on bignum (1.34× → 0.59×, one-block big numbers) and
the tree programs.

**Reussir's benchmark suite** (its 18 Lean programs, unchanged; several run
for well under a second, so their ratios are rough):

| program | native s | lean2rr s | time × | memory × |
|---|---|---|---|---|
| rbtree-zipper-lambda | 0.52 | 0.10 | 0.19 | 0.84 |
| rbtree | 0.67 | 0.21 | 0.31 | 0.84 |
| heap | 1.48 | 0.49 | 0.33 | 0.51 |
| nbe-closure | 0.09 | 0.03 | 0.33 | 0.32 |
| nbe-hoas | 0.09 | 0.03 | 0.33 | 0.35 |
| functional-queue | 0.05 | 0.02 | 0.40 | 0.71 |
| hash-map-linear | 1.58 | 0.66 | 0.42 | 0.60 |
| heap-functional | 1.36 | 0.59 | 0.43 | 0.89 |
| qsort | 1.13 | 0.51 | 0.45 | 0.66 |
| ordered-map-linear | 2.63 | 1.36 | 0.52 | 0.44 |
| rbtree-zipper | 0.36 | 0.19 | 0.53 | 0.84 |
| ordered-map-shared | 3.93 | 2.52 | 0.64 | 0.54 |
| life | 4.45 | 2.90 | 0.65 | 0.83 |
| ordered-map-heavily-shared | 4.61 | 3.07 | 0.67 | 0.47 |
| fingertree | 0.05 | 0.04 | 0.80 | 0.71 |
| hash-map-shared | 8.20 | 7.16 | 0.87 | 0.91 |
| derive | 0.32 | 0.28 | 0.88 | 0.80 |
| hash-map-heavily-shared | 116.25 | 124.63 | 1.07 | 0.88 |

Where lean2rr is not faster, the known causes are: freeing through the
pending-work stack that bounded-depth frees need (deriv, monadic-interp;
local patch 13-c made it cheaper), and Reussir having no borrowed
parameters, so code that walks shared data (looking up a hash bucket
shared between map versions) writes reference counts that native Lean
only reads (hash-map-heavily-shared).

## Optimizations

The core translation is correct on its own; every optimization is a
separate pass in `lean2rr/LeanToReussir/Opt/`, registered by one line in
`Opt/Registry.lean`, and **all are on by default** (benchmarks use the
defaults), except `unread-fields`, which the owner wants off by default
(2026-10-08) and `--enable-opt unread-fields` turns on. `lean2rr
--list-opts` lists them; `--disable-opt NAME` (or
`L2R_DISABLE_OPTS=a,b` for `scripts/l2r.py`) turns one off, for testing.
A pass restricts itself only through checks it makes on every program, for
soundness.

| pass | what it does |
|---|---|
| `unread-fields` | off by default: values that are stored in fields no kept code reads (callbacks: Batteries' linters, attributes and environment-extension hooks; data: a derived `ToExpr` instance's `Expr`) left out before Stage 3, with what only they reach: a driver of cedar-spec's authorizer (cedar-spec imports Batteries) no longer reaches the `Lean` package's C++ functions and equals native on three inputs (8,335 of 25,363 declarations kept); lean-regex with its `deriving Lean.ToExpr` instances, unpatched, translates and equals native on 1 MB of Dickens and of Lean source |
| `field-order` | record fields ordered by size, so records have no padding |
| `value-structs` | a structure with one field is represented by the field |
| `compact-arrays` | an `Array` of a scalar is a compact `RVec<u8\|u16\|u32\|u64\|f32\|f64>` (`Bool` and small enumerations as bytes), for each storage kind that a whole-program check finds never meets an array of boxes; the loops of `Array.map` typed at their element types. lean-zip's compression of the Silesia corpus: peak 1.9 GB before, 512 MB after (native 2.17 GB); matrix (`Array UInt64`) fully compact |
| `placeholder-cache` | Lean's placeholder values built once |
| `boxed-consts` | a constant whose boxing allocates (a `Float`, a `UInt64` from 2^63) boxed once, as native Lean's `_boxed_const` |
| `float-lits` | float literals computed at compile time |
| `cheap-consts` | constants made of small literals (one-word `Nat`/`Int` values only) recomputed instead of cached |
| `prelude-repr` | `Nat.repr`/`Int.repr` by the runtime's GMP code |
| `jp-sink`, `jp-small` | join points moved to where they are used; small ones duplicated |
| `state-machines` | loops through join points: entering the loop and every jump inside it allocate nothing |
| `lazy-fields`, `nullary-scrutinee`, `sink-proj` | shapes that let Reussir reuse memory cells |
| `fresh-rebuild` | the error arm of a monadic bind rebuilds its freshly built result, so Reussir reuses the cell on the success path |
| `flatten-structs` | a structure argument of a loop (join point, self-recursive function) and a structure or two-constructor result (`EST.Out`, `Except`, `Option`, `ForInStep`) passed as its fields at their precise types (worker/wrapper; results as a `[value]` tuple with a tag): no record built and no field boxed per step; a whole use rebuilds the value only at a loop's exit or from a call's result, where that adds no allocation (a join point's parameter used whole stays whole). Against the same build with the pass off (cachegrind instructions): Sieve −54 %, MonadicInterp −51 %, Unionfind −51 %, HigherOrder −4 %, Liasolver −8 %, Mergesort −7 %, lean-zip compress −5 %, decompress −11 %. |
| `conv-liveness` | the unboxing, application and conversion helpers generated only for what live code reaches (arms only for the `Box` variants and function values it builds), and functions unreachable from the entry point and the runtime's entries dropped: a program importing `Cslib.Init` went from 990,927 functions (1.44 GB of `.rr`) to 30,418 (26 MB) |
| `merge-fns` | generated functions equal up to their own and local names merged (each copy calls the first): `List.reverseAux` at every type is one function; a function called from one place stays (LLVM inlines it), except startup code; CslInitOnly's `.rr` 32.0 -> 30.7 MB |
| `prelude-liveness` | only the runtime prelude's functions that the program names (directly or through the prelude's kept functions) are in the `.rr`: rrc compiles one rustc run per texture, also for a texture no code calls; a one-line program has 75 textures instead of 484 (rrc with an empty texture cache: 14.3 s → 3.1 s; with a full one 1.8 s → 1.1 s) |

Parts that look like optimizations but are required (each with its reason
in the registry): the startup chain cut into chunks, loop state machines,
Stage 3's type recovery, closed-term chains, `Outline` (long functions cut
into pieces for rrc's sake) and functions kept out of rrc's inliner (build
time).

## Reussir

lean2rr needs Reussir built from source with lean2rr's local patches
(Reussir `943f2195`, a commit of Reussir's `main`, plus the 35 patches of
[`../reussir-bugs/patches/series`](../reussir-bugs/patches/series), in
that order; each patch file is named after its issue, `NN-x-*.patch`, and
explained in depth in the file of that issue, indexed in
[`../reussir-bugs/README.md`](../reussir-bugs/README.md)). Branch
`l2r-base2` of the checkout in `./reussir` (head `b2e4a47e`) has all 35;
since 2026-10-09 13-c also has the fix of Reussir issue 47 (the stack
before the fold is branch `l2r-base2-pre47`, head `71f17ae2`).
They are local: lean2rr's work does not push them, and each is reviewed
adversarially. Five bug fixes are merged upstream (pull requests #651 to
#655: 26-a, 02-a, 09-a, 04-a and 05-a); the base has them, so the series
dropped them on 2026-10-07 (until then the base was `ef922049`).
An independent audit checked whether each problem is really a Reussir
bug. The 40 documented problems are numbered issues (37 is reserved);
their kind says what each is: 20 are bugs (erroneous behaviour), 11 are
costs, 3 are missed optimizations, 5 are missing features and 1 is
intended behaviour. Only the bugs are wrong: the others have correct
output, and their patches are optimizations or features, not fixes. 34
issues have patches (39 patch files; issue 14 is fixed by issue 9's patch
09-a) and 5 are documented only:

- **Real bugs fixed (19 patches):** wrong values after in-place reuse of a
  structure or variant cell (bug 2), `[value]` enum bytes lost (1), a
  layout mismatch that overflowed cells (8), compiler crashes (4, 5, 31),
  use-after-free (9, 14), the parser mixing up subtrees on very large
  files (12, in Reussir's parser library `cstree`), programs that did not
  compile (15, 19), wrong code after an LLVM assumption undid a pointer
  launder (26) and from a uniqueness analysis that proved a shared value
  unique (28), a texture placeholder dropped (21), non-reproducible builds
  (24), MLIR dumps that did not parse back (29), MLIR types whose trailing
  text was silently dropped (33), Reussir's own build (18), and executables
  linked with text relocations (34: lean2rr's driver also passes
  `--relocation-mode pic`).
- **A real bug with a flag workaround (1 patch):** a static cell freed after 2^32
  references (6). Another nullary-constructor encoding avoids it; the patch
  keeps the default encoding for speed.
- **Build-time costs, not bugs, with a small optimization (10 patches):**
  type ids printed exponentially by closure devirtualization (10),
  interprocedural SCCP (11) and Reussir's own quadratic glue lookups
  (11b), reuse across calls in deep matches (16), a straight-line `Nat`
  function (17), the inliner on lean2rr's conversion code (20), wildcard
  arms over wide enums (22), the polymorphic-FFI modules linked one call
  each (23), the call lowering's symbol lookups (30), and rustc run again
  for every FFI texture on every build (35: about 13 s of a small
  program's 16 s; the patch caches the bitcode, and lean2rr's driver gives
  rrc the cache directory). The superlinear ones can make large builds
  infeasible; the output is correct either way.
- **A missed optimization, not a bug (1 patch):** token reuse picking a
  cell that never frees (7). Its optimization patch stays because the use-after-free
  fix (9) builds on it.
- **Missing features, not bugs, implemented locally (8 patches):** freeing
  long or deep structures without recursion, in Lean's order (13, four
  patches; lean2rr's runtime needs them), and the same for a member behind
  `Nullable` (27); a hook at the end of a drain that lean2rr's runtime
  uses for promises released inside a free (40, required since switch
  step 6); opaque handles that may be a tagged number instead of a pointer
  (41), so that `Nat` and `Int` are one word with no allocation for small
  values (lean2rr's prelude needs it); and foreign data in the top 16 bits
  of such a handle (38, for the one-word `Box`).
- **Documented only, not bugs:** Rust allocations on mimalloc's aligned
  path (3, intended), two costs whose removal would be a redesign: the
  inline expansion of copies of `[value]` records shared in a DAG (25) and
  the size of `--emit mlir` dumps (32), and two missed optimizations: no
  inline attribute on texture trampolines (36) and a reuse token taken
  from a release that never frees (39).

Every Reussir problem met so far is documented with a reproducer,
including those lean2rr works around and those the audit classified as
intended behaviour or build costs, in
[`../reussir-bugs/`](../reussir-bugs/README.md), whose status table also
shows which patches are applied. lean2rr keeps its workarounds, so that it
also works with an unpatched Reussir (except for the features it
requires: its runtime needs patch 13-b, its prelude 41-a, and
`scripts/l2r.py` requires 40-a, 38-a and 13-d: `REQUIRED_REUSSIR_PATCHES`).
Two parts of Reussir that its author offered (LLVM coroutine bindings,
dynamic-extent arrays) are not needed: lean2rr's tasks need stackful
contexts, which lean-runtime's scheduler has (corosensei coroutines), and
Lean arrays are growable, which dynamic-extent arrays are not.

## Possible future work

- Borrowed parameters (needs Reussir support) for code that walks shared
  data.
- Real parallelism for tasks (the scheduler is single-threaded by design).
- The C++-implemented parts of the `Lean` library, for metaprogramming
  programs.
- Calling a program's own C code (the parked branch `ffi-c`; not a goal
  for now: lean2rr targets Lean code plus Lean's runtime library).
