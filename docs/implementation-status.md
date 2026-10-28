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
| Runtime test suite (744 programs, `tests/runtime`) | at its last full run (gate51 = dev 0ffaf3de + plan entries for LB-22 and LB-24 to LB-27, 2026-10-28, Reussir l2r-base12, lean-runtime 50840bb), 742 of 744 identical to native Lean 4.34.0 and 2 expected failures (`RtLeanUnsupported`, `RtCastMixedRebox`); the classic corpus 36 of 36 (18 programs at two sizes) with all optional passes on and with all default-on passes off, and 18 of 18 with `unread-fields` on; every check script of tests/runtime passes (21); the raytracer's images equal native's; on dev fd53ae11 the Reussir benchmark suite 18 of 18 and the loader checks 17 of 17. At gate50 (dev 6ba1d54b + panicking externs merged, array literals through instances), 742 of 744 identical and 2 expected failures. At gate49 (dev 3a629b5a + implemented_by in lean2rr's own code, closed terms shared between concrete declarations), 739 of 741 identical and 2 expected failures. At gate48 (dev 0a1e4391 + rule 4 through extern instances, map loops in place through flatten's workers), 734 of 736 identical and 2 expected failures. At gate47 (dev c6ad0332 + leanrt's task glue without its dead answers), 729 of 731 identical and 2 expected failures. At gate46 (dev 17265da7 + the task glue without its dead dispatch chains), 729 of 731 identical and 2 expected failures. At gate45 (dev 97940f1c + names recognized by their declarations), 729 of 731 identical and 2 expected failures. At gate44 (dev 699af824 + the build driver's fixes), 723 of 725 identical and 2 expected failures. At gate43 (dev ffb428f7 + lazy-fields' pushProj rule), 723 of 725 identical and 2 expected failures. At gate42 (dev fd53ae11 + the renumbered scrutinee per alternative), 723 of 725 identical and 2 expected failures. At gate41 (dev 1d71d2a1 + flatten-structs' split of a structure of closures in a program that casts), 722 of 724 identical and 2 expected failures. At gate40 (dev 55ce211d + the resource flow's cleanups), 720 of 722 identical and 2 expected failures. At gate39 (dev 385cbdd3 + the arm-release record by the resource flow), 720 of 722 identical and 2 expected failures. At gate38 (dev d1b3b913 + the borrow emulation's keeps by the resource flow), 720 of 722 identical and 2 expected failures. At gate37 (dev 13532d7f + the release order at the start of a branch), 716 of 718 identical and 2 expected failures. At gate36 (dev 55a46957 + the view binders, unread-fields' task check and the hunts' cleanups), 714 of 716 identical and 2 expected failures. At gate35 (dev ad3cd1d5 + typed arrays past cached constants that hold no array, Flatten's nested matches, and the bug hunts' cleanups), 711 of 713 identical and 2 expected failures. At gate34 (dev af521c12 + Reussir l2r-base12), 708 of 710 identical and 2 expected failures. At gate33 (dev 0c8f1419 + unreached-decls and cleanups, Reussir l2r-base11), 708 of 710 identical and 2 expected failures. At gate32 (dev 69dcbe56 + the loop tail-call fix and the memoized type questions), 707 of 709 identical and 2 expected failures. At gate31 (dev 57ba770c + D8's follow-ups and the wall-time fixes, Reussir l2r-base11), 703 of 705 identical and 2 expected failures. At gate30 (dev 3e03d989 + D8, Reussir l2r-base10), 701 of 703 identical and 2 expected failures. At gate29 (dev 11c498da + Reussir l2r-base10), with both representations, 701 of 703 identical under each and 2 expected failures. At gate28 (dev 0091855a + Phase 2 on Reussir l2r-base9-shared, 21 patches), 699 of 701 identical under each representation and 2 expected failures. At gate27 (dev 419a74d4 + run 14's rcgmp reads, owned boxes, guard mode removed, the index after a proved access; Reussir 00906e38 + 14 patches), 688 of 690 identical under each representation and 2 expected failures. At gate26 (dev 1886d7bf + the default flip to rcgmp), 685 of 687 identical under each representation and 2 expected failures. At the combined gate on int25 (dev 8ee78dc0 + the rcgmp index and size reads, leanrt then the default), 685 of 687 identical under each representation and 2 expected failures. At the combined gate on int24 (dev 2c4083d9 + the inline-anchors guard, Reussir 00906e38 + 13 patches), 683 of 685 identical under each representation and 2 expected failures. At the combined gate on int22 (dev 27ea78da + step D, 2026-10-25), 680 of 682 identical under each representation and 2 expected failures. At the combined gate on int21 (2026-10-25, Reussir upstream 00906e38 + 8 patches), 669 of 671 identical and 2 expected failures. At the combined gate on int20 (2026-10-25, Reussir l2r-base5 on 0378b744), 667 of 670 identical and 3 expected failures. At the combined gate on dev 0810b9ec with Reussir l2r-base5 (2026-10-24), 658 of 660 identical and 2 expected failures, and the same results on Reussir l2r-base3 (13de3101, 2026-10-21). At the combined gate on dev 42e8e15b (2026-10-10, Reussir upstream 943f2195 + 35 patches), 632 of 634 identical and the same 2 expected failures. At the gate of switch step 10 ( branch `lean-runtime-step10` at 0410be6 on dev d39294a, lean-runtime e5e502e, 2026-10-06), 336 of 337 identical to native Lean 4.34.0 and 1 expected failure (`RtLeanUnsupported`); the classic corpus 54 of 54 with all optional passes on and with all off; the Reussir benchmark suite 18 of 18. At the gate of `perf-const-reads` (e7bc212 on dev 9a2ddf6, lean-runtime 83f7127, 2026-10-06), 331 of 332 identical to native Lean 4.34.0 and 1 expected failure (`RtLeanUnsupported`). At the gate of switch step 8 (branch `lean-runtime-step8` at 8e5c5eb on dev d3032e4, lean-runtime e34cd61, 2026-10-05), 326 of 327 identical to native Lean 4.34.0 (`RtNetEffectPoll` counted after one re-run: in the gate's run its native build printed `accepted during the loop: false`, a timing flake of native's that its re-runs did not repeat; lean2rr's output was the expected one), nine of them through expectation files: eight where lean2rr does not reproduce a Lean runtime bug (`RtReadAfterWrite`, `RtStdioStdoutRead`, `RtErrorNoFileName`, `RtProcessNullFd`, `RtProcessNullOpenFails`, `RtStartupFdExhausted`, `RtRefSetDuringModify`, `RtRefSwapDuringModify`; plan §10, "Runtime: Lean bugs we do not reproduce"), and `RtCseFnResult` (its trace prints once natively and twice through lean2rr, which Lean allows: plan §10, "Merging after erasure"); 1 expected failure: `RtLeanUnsupported` (an expected refusal until the runtime has the `Lean` package's C++ functions); five tests (`RtExternRefused`, `RtExternOpaqueRepr`, `RtExternOpaqueRedecl`, `RtExternPrivate`, `RtCastExtern`) check that lean2rr refuses an extern it cannot serve; `RtLiftedLimits` and `RtInternalPanic` compare each side with its own expectation files where lean2rr lifts a limit of Lean's runtime (plan §10, LB-04 to LB-12). lean-runtime's own program cases through lean2rr's builds: of its IO areas (io, process, streams, temp, uvsys, time) 90 of 90 at lean-runtime 9d27ce0 (switch step 5); of its task areas (tasks, sync, refs, taskio, uvloop, net) 163 of 163 at lean-runtime ed1e8af (switch step 6), a subset of 26 of them (references shared with tasks, promises) 26 of 26 at 528fcbb (switch step 6), at 471f458 (switch step 7) a subset of 39 (those 26, the other `sync` cases, `tasks/poll_threshold_mutex`, and the startup and title cases `io/initializing`, `io/startup_*`, `uvsys/process_title`, `uvsys/title_*`) 39 of 39, and at e34cd61 (switch step 8) a subset of 94 (those 39, 31 panic, exit and stream cases such as `panics/replicate_overflow`, `process/output_*oom*`, `tasks/get_in_sync_task*`, `tasks/promise_in_initialize*`, `io/exit_*`, `streams/stream_redirect`, and the 27 `net` cases) 94 of 94 |
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
| `Nat` (natural numbers, unbounded) | `Nat`, one machine word, as natively: Reussir's built-in integer | see below |
| `Int` (unbounded integers) | `Int`, one machine word, as natively: Reussir's built-in integer | small in [-2^61, 2^61) |
| `UInt8/16/32/64`, `USize` | `u8/u16/u32/u64`, `u64` | 64-bit targets only |
| `Int8…Int64`, `ISize` | the same unsigned words, signed operations on the bit pattern | as Lean's C runtime does |
| `Float`, `Float32` | `f64`, `f32` | printing follows Lean's exactly |
| `Char` | `u32` | |
| `Bool` | `bool` | |

**One representation.** `Nat` and `Int` are Reussir's built-in integers
(rcgmp; lean2rr's default since 2026-10-25, its only representation since
2026-10-26): a value in [-2^61, 2^61) is an immediate in the word, any
other a reference-counted GMP integer of Reussir's runtime, one block with
its limbs. Arithmetic on immediates is inline code that LLVM can fold
(Reussir also folds arithmetic on constants), a case split on a `Nat` or
`Int` is a Reussir `match`, and a boxed `Nat` or `Int` keeps Lean's
words (a `Nat` below 2^63 is an immediate; a bigger value is a runtime
cell that holds the integer). Lean's rules (subtraction stops at 0,
division by 0 gives 0, the limits of shifts and exponents) are composed in
the prelude of Reussir's operators, as the shared crate lean-runtime
writes them. Until 2026-10-26, `--int-backend leanrt`
(`L2R_INT_BACKEND=leanrt`), the default until 2026-10-25, selected
lean2rr's own one-word encoding (Lean's `lean_box(n)` words, big numbers
in one block of leanrt's with GMP); both gave the same results at the
combined gates, and timing run 14 measured a per-case geometric mean of
0.990 for rcgmp against leanrt (wall time). Clean-integration D8 removed
it (details:
[nat-int.md](implementation/representations/nat-int.md)).

Compared with native Lean:
- a `Nat` or `Int` field in a record takes 8 bytes, as natively;
- a big number is one allocation (natively two: the object and GMP's
  limbs);
- a `Nat` below 2^63 in the generic `Box` (a field or an array element of
  a type parameter's type, code whose types cannot be made concrete,
  below) is its own word, as natively: boxing it allocates nothing.

### Text, arrays, references

| Lean | Representation | Notes |
|---|---|---|
| `String` | runtime `LStr`: one block like Lean's string object (reference count, byte size, capacity, character count, then the UTF-8 bytes) | copy-on-write: modified in place when unique, like Lean |
| `Array α` | runtime vector of boxes, one word each, for every `α` without a storage kind: one block, header (count, size, capacity) then the elements | in place when unique; a small `Nat` is the word itself, a `Float` a cell, as natively |
| `Array X`, `X` a one-word counted type (a shared record or enum, `Nat`, `Int`, `String`, an array) | runtime vector of the elements themselves (`RVec<T>`) | optimization `typed-arrays`, per pointer kind, under the check of `compact-arrays`, and only when the elements hold nothing whose release the program can observe; otherwise an array of boxes |
| `Array S`, `S` a scalar | runtime vector of the scalars inline: `u8` (`UInt8`, `Bool`, an enumeration of at most 256 constructors), `u16`, `u32` (`UInt32`, `Char`), `u64` (`UInt64`, `USize`), `f32`, `f64` (`Float`) | optimization `compact-arrays`, per storage kind, when the program's array of that kind never reaches generic code (a whole-program check); otherwise an array of boxes |
| `ByteArray`, `FloatArray` | arrays of `u8`, `f64` | `ByteArray.mk`/`data` are the identity with a compact `Array UInt8`; with an array of boxes they copy the elements in one loop, as natively |
| `IO.Ref α` / `ST.Ref` | a shared mutable cell of boxes, or, with optimization `typed-cells`, of `α`'s own type (a shared record or enum, `Nat`, `Int`, `String`, an array, an immediate scalar) | mutations seen through every alias, as in Lean; a typed cell per kind when a whole-program check over the reference primitives allows it |
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
        T_Tree_346::c_leaf => { let nl373 : Nat = 0; nl373 },   // Reussir's literal
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
structure (a long list, a deep tree, nested arrays) never overflows the
stack: Reussir frees records in a loop or with a stack of pending drops
per thread (local patches 23-a to 23-p: memory that does not grow with
the depth, like Lean's to-do list), and the runtime frees its own
objects through the same stack, as Lean does. Resources inside (file
handles) are closed in Lean's order inside a free that starts at a
runtime object, and in field order at the top of a free that user code
starts (plan §10). Memory
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
  with an offset or length of 2^64 or more (LB-06); a power or left shift
  too big for GMP ends at once with `INTERNAL PANIC: out of memory`, where
  natively GMP kills the program with SIGFPE (LB-05; a larger sum or
  product is computed, or ends with an abort where memory runs out). With `mod-pow2`, `x % 2 ^ w`
  and `x % (1 <<< w)` make no power and give their value for every `w`:
  `x` itself above `MAX_BITS`, and no message for a `w` of 2^32 or more,
  where natively (and in lean2rr without the pass, above `MAX_BITS`) the
  power ends the process (LB-11, LB-12).
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
pending-work stack that bounded-depth frees needed (deriv, monadic-interp;
measured on the earlier Reussir base, whose drop glue pushed record
members on that stack), and Reussir having no borrowed
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
| `unread-consts` | a constant that no kept code reads and whose evaluation cannot show (no recursion but Lean's checked library recursion, no function value applied, no extern but pure total ones) is not evaluated at startup and not translated: after `literal-consts`, the 50 distinct `.rr` files of the benchmark set 24.9 → 22.9 MB (−7.9 %), lean-zip's 4.3 → 3.6 MB (−16 %: `bv_decide`'s expression trees), lean-regex −12 %, cedar −6 % |
| `unreached-decls` | a declaration that no code reaches after Stage 2 (from `main`, the error printer, every startup step and the `IO.Error` builders) is not translated: about a fifth of the declarations with code (13,829 of 69,730 for a program that imports `Cslib.Init`, whose translation takes 73 s instead of 84 s; 2,967 of 15,192 for Cedar); nothing more with `unread-fields` on, which already drops them |
| `field-order` | record fields ordered by size, so records have no padding |
| `value-structs` | a structure with one field is represented by the field |
| `typed-arrays` | an `Array` of a one-word counted type (a shared record or enum, `Nat`, `Int`, `String`, an array) whose elements hold nothing with an observable release is a typed `RVec<T>` of the element's own type, for each pointer kind that the check of `compact-arrays` allows; a set or pop of a record releases it by its own drop, out of line. Cachegrind, SVE-free builds: n-body 602 → 493 M instructions (-18.2%), unionfind 6.80 → 5.89 G (-13.3%), the raytracer 16.49 → 15.09 G (-8.5%), hashmap -3.8%, monadic-interp -2.5%, lean-zip compression -1.2%, Cedar +0.6% (the step that frees an array of records) |
| `compact-arrays` | an `Array` of a scalar is a compact `RVec<u8\|u16\|u32\|u64\|f32\|f64>` (`Bool` and small enumerations as bytes), for each storage kind that a whole-program check finds never meets an array of boxes; the loops of `Array.map` typed at their element types. lean-zip's compression of the Silesia corpus: peak 1.9 GB before, 512 MB after (native 2.17 GB); matrix (`Array UInt64`) fully compact |
| `typed-cells` | the cell of a reference (`IO.Ref`, `ST.Ref`) holds the element's own type instead of a box, for a shared record or enum, `Nat`, `Int`, `String`, an array, `Bool`, `UInt8`, `UInt16`, `UInt32`, `Char` and `Float32`, for each such kind that a whole-program check over the reference primitives allows (no operation at another representation, such as one at `lcAny`, can meet it; its values hold nothing with an observable release; no cast) |
| `placeholder-cache` | Lean's placeholder values built once |
| `boxed-consts` | a constant whose boxing allocates (a `Float`, a `UInt64` from 2^63) boxed once, as native Lean's `_boxed_const` |
| `literal-consts` | a constant whose code is one string literal, or one read of such a constant, read from the runtime's literal cache, without a once-cell accessor and `_init`: 50 programs' `.rr` 35.2 MB → 27.8 MB (2284 accessor pairs fewer; L11 −11.9%; lean-zip's two drivers (Survey.Main, ZipBench) −41.5%, as their unread `bv_decide` certificate strings, 3 MB, leave the literal table) |
| `float-lits` | float literals computed at compile time |
| `cheap-consts` | constants made of small literals (for `Nat`/`Int`: any literal, computed values only within rcgmp's immediates) recomputed instead of cached |
| `prelude-repr` | `Nat.repr`/`Int.repr` by the runtime's GMP code |
| `prelude-int-ops` | `Nat.testBit` read in place (rcgmp's `testbiti`) and `Float.ofNat`/`Float.ofInt` (also `Nat.toFloat`/`Int.toFloat`) by `sitofp`. Cachegrind, SVE-free builds: lean-regex's backtracker (Z03b) 19.16 → 18.88 G instructions (−1.5 %); a loop of `toFloat` on small, 2-limb and negative 2-limb values 4.17 G → 80.1 M (−98 %), on small values only 41.5 → 17.5 M (−58 %); `testBit` over each bit of a 9512-bit number 142.6 → 7.8 M (−95 %) |
| `int-match` | a case split on a `Nat` or `Int` (`0`/`n+1`, `ofNat`/`negSucc`, nested splits, chains of literal tests) is a Reussir `match` on the built-in integer. Cachegrind against the pass off: a loop through `n+1` −7.9 %, E01 −3.0 %, X14, X13, L04, L11 unchanged, X04 +1.7 %, L08 +2.2 %, `fib` +6.6 % (rcgmp's selection among immediates costs a few instructions more than one test for two or three arms) |
| `mod-pow2` | `x % 2^w` (every `BitVec.ofNat`) computed as the low `w` bits of `x`, without making `2^w`: lean-regex's backtracker (Z03b) −41 % instructions on dev, −50 % with the runtime's big-number fixes |
| `utf8-size-add` | `p + c.utf8Size` (a `String.Pos.Raw` plus a `Char`: `String.map`'s step) by the prelude's `l2r_nat_add_utf8_size`, which adds 1 for an ASCII character in a branch of its own, so the next position does not wait for `Char.utf8Size`'s selects: strings (L17) 659.8 → 581.0 ms (−11.9 %, median of 7 interleaved runs pinned to one core), 14.31 → 13.95 G instructions (−2.6 %) |
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

lean2rr needs Reussir built from source with lean2rr's local patches.
Its base is upstream Reussir `95d9a1c8` (2026-10-26) plus the 24 patches
of the series: branch `l2r-base12` of the checkout in `./reussir` (head
`c1170ff9`, tree `af82b837`): 10-a, 07-a, step D's 5 patches (issue
20), 21-a (issue 21) and the 16 patches of issue 23 (worklist drops,
their stack shared with lean2rr's runtime, and pending records linked
through their own headers). Upstream `95d9a1c8` has lean2rr's pull
requests #824, #843 and #845, the code of step D's 20-b (the owned
handle `Mpz` at polyffi type arguments), and #844, which moves the
mlir-rcgmp commit that the build fetches to `cc73b218` (quotient-only
division), before the local patch 20-f; so 20-b keeps only tests and
20-f is gone, and rrc and Reussir's runtime are the same as on branch
`l2r-base11` (head `a39e59b0`: upstream `00906e38` plus 25 patches,
with 20-f and the whole 20-b). Branch `l2r-base10` (head `0bea9c7d`)
is `l2r-base11` without 20-f. It has none of
the old drop patches: Reussir frees records with upstream's glue, except
the recursive records that are neither a loop nor non-recursive, which
issue 23's patches free through a stack of pending drops per thread
instead of upstream's coroutines; lean2rr's runtime keeps its pending
releases on that stack (23-k to 23-m). Branch `l2r-base9-shared` (head
`6111586c`) is the same series without 23-n to 23-p, and branch
`l2r-base9` (head `fc9c1d20`) also without 23-k to 23-m. The bases before
Phase 2 had 6 more patches: five for native release order through a
pending stack shared with lean2rr's runtime (02-a to 02-e), and a
drain-end hook (09-a); the runtime's own pending stack replaced them. The last of
those bases was branch `l2r-base8` (head `8e9a6293`, `l2r-stepd` plus
21-a): upstream `00906e38` plus 14 patches, step D's 5 after the 8 of
branch `l2r-base5` (head `c4a5df4b`), then 21-a; branch `l2r-stepd`
(head `e3b96e03`) is its first 13. Phase 2's first base, `l2r-base7`
(head `bfe3d32d`), used upstream's coroutine drops and needed patch
19-a (issue 19); with issue 23's patches 19-a is parked.
Since `0378b744`, Reussir's build needs GMP 6.2 or later, a CMake that
knows `cxx_std_26` for Clang (CMake 4.4.4 works; 3.28 does not) and the
libstdc++ 14 headers, for its built-in rcgmp integers
([building Reussir](../reussir-bugs/README.md#building-reussir)).
Upstream `00906e38` (#804) only moves the commit of mlir-rcgmp that the
build fetches; lean2rr's programs then used no rcgmp integers, and the move to
it changed no issue and no patch. Before it, `l2r-base5` was upstream
`ea240b19` plus the same 8 patches (head `e1680f65`), and until the move
to `ea240b19` (2026-10-25), upstream `0378b744` (2026-10-24) plus 9
patches (head `6bf9be85`). Upstream `ea240b19` is lean2rr's pull request
#758, the change of patch 05-a: it fixes issue 5 (executables linked
with text relocations), whose number is retired, and the move dropped
05-a; lean2rr's driver still passes `--relocation-mode pic`, now rrc's
default for executables (redundant but harmless; kept for older bases).
The base before `0378b744` was branch `l2r-base3` (head `4c490260`):
upstream `7954a367` (2026-10-19) plus the same 9 patches, which applied
to `0378b744` with no conflict; that move fixed no issue. Before that it
was branch `l2r-base2` (head `b2e4a47e`), Reussir `943f2195` plus the 35
patches of the old series; the old patch files are in git history and in
those branches. [`../reussir-bugs/`](../reussir-bugs/README.md) describes
the state at `95d9a1c8`: upstream `7954a367` fixed 30 of the old issues
in full (most of them lean2rr's own fixes, sent as pull requests #651 to
#663 or adapted by Reussir's author from lean2rr's patches), so their
files are gone, and the 16 issues that stayed open got new numbers (1 to
16; `ea240b19` later fixed issue 5). The drain-end hook (9) and the cost
of a one-cell free on Reussir's old stack (11) no longer concern
lean2rr, since the old drop patches went; their numbers are retired, as
is 22 (a local patch for retcon destructors, never published, superseded
by issue 23). The series there,
[`../reussir-bugs/patches/series`](../reussir-bugs/patches/series), has
24 patches on `95d9a1c8`, in that order; each patch file is named after
its issue, `NN-x-*.patch`, and explained in the file of that issue. They
are local: lean2rr's work does not push them, and each is reviewed
adversarially. Only the bugs are wrong: the other kinds have correct
output, and their patches are optimizations or features, not fixes.

- **The interface for `Nat` and `Int` on rcgmp (issue 20, 5 patches),
  for step D (on dev since `1e57ed53`, 2026-10-25):** intrinsics for
  Lean's division modes and the power-of-two remainder, with unsigned
  division of `Nat` immediates; `Nat` and `Int` at polyffi type
  arguments as an owned handle (this patch also fixed a bug: before it,
  a `Vec<Nat>` leaked its elements and a generic texture at `Nat`
  released values it kept, a use after free; its code is upstream since
  #824 and #843, and the patch keeps tests only); retain and release glue
  that inlines into textures; a sharing query for `dbgTraceIfShared`;
  big literals given to MLIR in hexadecimal (a 100k-digit literal: 17 min
  to 0.5 s). rcgmp is lean2rr's default backend since 2026-10-25, so a
  default build needs 20-a and 20-b's `Mpz` (scripts/l2r.py checks for
  them), and since clean-integration D8 (2026-10-26) every build. A sixth
  patch, 20-f, moved the mlir-rcgmp commit that the build fetches to
  `cc73b218` (upstream's quotient-only division: L11 -16% instructions);
  upstream Reussir made the same move in #844, so 20-f left the series.
- **An optimization of code with rcgmp integers (issue 21, 1 patch):**
  inc/dec cancellation also cancels the retain of an integer member
  extracted from a `[value]` record or tuple against the member's release
  in the record's drop, as it does for an rc member (L12 -9.6%
  instructions, L17 -7.8%, Z01c -6.0%).
  Nothing requires it.
- **The memory of deep frees (issue 23, 16 patches; a cost, not a
  bug):** upstream frees the records of a recursive type that is neither
  a loop nor non-recursive with coroutines that keep one frame per level
  of the value being freed (85 to 622 bytes per level; a chain of 10^6
  closures peaked at 652 MB, native Lean at 102 MB). The patches free
  them through a stack of pending drops per thread, as Lean's to-do
  list: no memory per level for a one-sided chain (68 MB there), and
  fewer instructions per freed cell. Three of them (23-k to 23-m) let
  lean2rr's runtime keep its pending releases on that stack (end work
  after the outermost drain, runs of cells, steps), so that one drain
  frees records and runtime objects in Lean's order and no Lean code
  runs inside a drain. Three more (23-n to 23-p) keep a pending record
  of the glue linked through its own header when the release function
  changes, so it costs no memory while it waits (a chain whose levels
  each leave a record of another type pending: 88.7 MB to 45.7 MB,
  native 55.1 MB), and one function's pending records as a run of cells
  (8 bytes each), which costs fewer instructions. `scripts/l2r.py`
  requires them, but for 23-p. One of them
  (23-e) also fixes a leak with TPDE's drop options (issue 24, a bug
  lean2rr does not reach).
- **Missing features, not bugs, implemented locally (2 patches):**
  opaque handles that may be a tagged number instead of a pointer (10),
  so that `Nat` and `Int` are one word with no allocation for small
  values (lean2rr's prelude needs it); and foreign data in the top 16
  bits of such a handle (7, for the one-word `Box`).
- **Documented only:** native Lean's release order (2, a missing
  feature: upstream frees in bounded stack its own way, first field
  first, with no hook for a host; lean2rr's runtime keeps its own
  pending stack, and a free that user code starts at a record goes in
  field order, plan §10); two costs whose removal would be a redesign:
  the inline expansion of copies of `[value]` records shared in a DAG (3)
  and the size of `--emit mlir` dumps (4); three missed optimizations:
  token reuse picking a cell that never frees (1, its patch parked), no
  inline attribute on texture trampolines (6, patches parked) and a
  reuse token taken from a release that never frees (8); five bugs that
  do not reach lean2rr (12 to 14; 16: rrc's 1 GiB driver stack under an
  address-space limit, its fix parked; 19: the drop expansion's code
  exponential in type nesting with upstream's coroutine drops, which
  issue 23's patches replace, its fix parked); and a mimalloc bug that
  leanrt works around (15).

Every Reussir problem met so far is documented with a reproducer, in
[`../reussir-bugs/`](../reussir-bugs/README.md) while it is open (the
fixed ones in git history). lean2rr keeps its workarounds, so that it
also works with a Reussir without the patches that fix or improve them
(except for the patches it requires: its prelude needs 10-a,
`scripts/l2r.py` requires 23-f, 23-k, 23-m and 07-a
(`REQUIRED_REUSSIR_PATCHES`),
and `Nat` and `Int` on Reussir's built-in integers require 20-a and 20-b
(`check_rcgmp`)); the workarounds for the issues fixed
upstream are listed as removable after the move (now) in
[`implementation/reussir-workarounds/`](implementation/reussir-workarounds/README.md).
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
