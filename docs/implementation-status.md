# lean2rr: what is implemented

Status as of 2026-10-02 (branch `dev`). This is a plain-language overview
for someone who knows Rust but not Lean. The full rules are in
[`translation-plan.md`](translation-plan.md); the runtime is described in
[`../runtime/README.md`](../runtime/README.md); the Reussir bugs met on the
way are in [`../reussir-bugs/`](../reussir-bugs/README.md). The implementation's
tricks and special cases, each with its reason, its place in the code and
what would break without it, are cataloged in
[`implementation/`](implementation/README.md).

## In one paragraph

lean2rr compiles Lean 4.33 programs to native executables through
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
| Classic benchmark corpus (18 programs × 3 input sizes, `tests/classic`) | all outputs identical to native |
| Runtime test suite (147 programs, `tests/runtime`) | 147/147 identical to native |
| Reussir's own benchmark suite (18 Lean programs, used unchanged) | 18/18 identical to native |
| The corpus with every optional optimization turned off | 18/18 identical (the core translation is correct on its own) |
| Lean library C functions (externs) of `Init` and `Std` | all 716 of Lean 4.34 available: 705 checked by programs that call each one, the other 11 (internal or private helpers) by direct tests |
| Adversarial testing | 4 rounds (about 1,300 test programs written to break it), every finding fixed or documented |
| Speed | faster than native Lean on 16 of the 18 classic programs and about equal on the other two (monadic-interp 1.01×, deriv ≈1×), faster on 17 of the 18 Reussir-suite programs (the 18th at 1.07×); tables below |

## How a program is compiled

1. **Collect and monomorphize.** Starting from `main`, lean2rr collects
   every function and type the program uses and makes a separate copy for
   each type it is used at (as Rust does with generics): `List Nat` and
   `List String` become two different types with their own code. Lean
   itself does not do this (it represents everything as pointers to boxed
   objects), so lean2rr recovers precise types where Lean erased them.
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
numbers uses GMP too. Lean's semantics are kept exactly: subtraction
stops at 0, division by 0 gives 0, and so on.

Reussir generates the reference counting itself, and normally treats every
handle as a pointer whose count it increments when the value is copied. A
small `Nat` is not a pointer, so lean2rr declares `Nat` and `Int` as
*tagged* opaque handles, a small local Reussir extension (patch 0050):
Reussir counts such a handle only when its low bit is clear, exactly as
Lean's C runtime tests the bit before every count update. Copying or
dropping a small `Nat` is a bit test; it is never allocated.

`Int` works the same way, with Lean's encoding too: a value in the 32-bit
range is stored in the word, any other is a big number.

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
- in the rare places where a `Nat` has to go through the generic `Box`
  (code whose types cannot be made concrete, below), boxing it allocates;
  natively a small `Nat` is never allocated.

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
| `Array α` | runtime vector of `α`'s storage type | in place when unique; enumerations stored as small indices; non-shareable values wrapped in a one-field box (Lean boxes elements too) |
| `ByteArray`, `FloatArray` | `Vec<u8>`, `Vec<f64>` | |
| `IO.Ref α` / `ST.Ref` | a shared mutable cell | mutations seen through every alias, as in Lean |
| `Thunk α`, `Task α` | a shared cell holding a state machine (pending / running / done) | lazy, computed once |
| file handles, processes, sockets, timers | runtime handles | closed when the last reference goes, as in Lean |

### Your own types

Each inductive type at each type instantiation becomes one Reussir type
with the same constructors and fields:

```
inductive Tree α | leaf | node (l : Tree α) (k : α) (r : Tree α)
```

means "a `Tree α` is either `leaf` or `node` with a left subtree, a value
and a right subtree", and at `α = Nat` it becomes roughly

```rust
enum Tree_Nat { leaf, node(Tree_Nat, Nat, Tree_Nat) }   // heap-allocated, reference counted
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
an unsafe inductive holding itself at a larger type, `Nest (α × α)` in
`Nest α`; existential types; values stored in `Dynamic`) uses a uniform
type `Box`: an enum with one variant per concrete type the program ever
boxes.
Converting between a concrete and the uniform representation is generated
code, element by element for arrays and lists.

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

Tasks run on one thread: there is no parallelism. A task runs when its
value is needed, when the running code blocks (sleeping, waiting for a
lock, a promise, a socket), or when `main` returns; contexts switch at
those points and at output, in the order native Lean's scheduler would
have used. Programs get the same output as natively as long as their
output does not depend on timing races. What cannot match: a loop that
polls shared state another task sets, without sleeping or printing, never
sees the change; a blocking system call (reading a pipe, waiting for a
child process) blocks every task.

### Memory

Reference counting and in-place reuse are done by Reussir. Freeing a deep
structure (a long list, a deep tree, nested arrays) uses a stack of
pending work instead of recursion, as Lean does, so it never overflows the
stack; resources inside (file handles) are closed in Lean's order. Memory
use is usually at or below native (Reussir's records and reuse are
tighter), except for generic arrays: an
`Array α` other than `Array Nat`/`Int`, `ByteArray` or `FloatArray` is a
counted box plus a separate element buffer (8 bytes and one allocation more
than Lean's single array object). Strings and `Array Nat`/`Array Int` are
single blocks with Lean's own header sizes (six million three-element
`Array Nat` rows: 328 MB, native 330 MB).

## What is not supported, or differs from native

Translation always succeeds; the differences are behaviours that cannot
match because the information is not in the `.olean`, because there are no
real threads, or because they read raw memory addresses. The full list,
with examples, is §10 of the translation plan.

- **No parallelism** (see "How tasks run"). Output that depends on timing
  races between tasks can come out in another order (natively a race).
- **Pointer identity and raw addresses** are not preserved: `ptrAddrUnsafe`
  answers the address of the value's own cell, or a word computed from a
  scalar value (`UInt64` and `Float` their bits), so `ptrEq`,
  `ptrEqList` and `withPtrAddr` may answer otherwise than natively (a
  value converted between representations is a new object, not `ptrEq` to
  its original), but `ptrEq` answering `true` still means equal values,
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
- **A program's own C code is not supported.** A program that implements
  some of its own `@[extern]` declarations in C (built by Lake) fails at
  the rrc build with an unknown function: lean2rr links no C code of the
  program. The targets for now are programs that use only `Init` and
  `Std`. The work on calling a program's C (branches `ffi-c` and
  `lean-externs`) is parked, not merged; where lean2rr's own layouts and
  Lean's object layouts conflict, lean2rr's win.
- **`import Lean` programs** (metaprogramming: the elaborator, the kernel,
  the code generator): the `Lean` library declares 196 more C functions,
  and those implemented in Lean's C++ are not available: expression and
  universe-level internals (`Expr.mkData`, `Expr.equal`, `Level.mkData`),
  `evalConst`, loading shared libraries (`Dynlib`), the LLVM bindings,
  `profileit`, `maxSmallNat`. A program that reaches one of them does not
  link (rrc reports the unknown function); one that only uses data
  structures from `Lean` builds.
- **Build time:** rrc compiles about 80 small functions per second, so a
  program with thousands of constants takes minutes to build (native:
  seconds). Very large literals and monad-transformer towers build, in
  seconds to a few minutes.

## Performance

Measured on this machine (aarch64, 20 cores, shared with other jobs: load
9 to 16 during these runs), each program's lean2rr and native builds run
alternately, pinned to the least-loaded fast core; best of 5 (classic) or
3 (Reussir suite); time ratio = lean2rr time / native time (below 1 =
faster than native). Every run's output was checked against native.
`dev` 9f5b642, Reussir `l2r-local` at `ef0235b9` (the local patches up to
0015).

**Classic corpus** (`tests/classic`, largest size):

| program | native s | lean2rr s | time × | memory × |
|---|---|---|---|---|
| mergesort | 2.11 | 0.79 | 0.37 | 0.64 |
| rbmap | 1.89 | 0.84 | 0.44 | 1.00 |
| typeclass-generic | 2.15 | 0.95 | 0.44 | 0.91 |
| rbtree | 1.84 | 0.83 | 0.45 | 1.00 |
| liasolver | 2.17 | 1.18 | 0.54 | 1.00 |
| unionfind | 1.18 | 0.71 | 0.60 | 1.03 |
| higher-order | 2.35 | 1.49 | 0.63 | 0.84 |
| rbtree-ck | 1.40 | 0.91 | 0.65 | 0.99 |
| strings | 1.82 | 1.31 | 0.72 | 0.94 |
| cfold | 0.79 | 0.63 | 0.80 | 0.79 |
| sieve | 1.51 | 1.22 | 0.81 | 0.31 |
| hashmap | 1.63 | 1.45 | 0.89 | 1.13 |
| binarytrees | 3.07 | 2.79 | 0.91 | 0.42 |
| qsort | 1.20 | 1.12 | 0.93 | 0.85 |
| nqueens | 3.77 | 3.55 | 0.94 | 0.75 |
| bignum | 2.46 | 2.36 | 0.96 | 1.34 |
| monadic-interp | 1.80 | 1.81 | 1.01 | 0.84 |
| deriv | (3.7–10) | 4.73 | ≈1 (noisy) | 0.80 |

deriv allocates 3.7 GB and its native time varied from 3.7 s to 10 s
between runs on the loaded machine, so its ratio here is not meaningful;
on a quieter machine it measured 1.0–1.1×.

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
local patch 0015 made it cheaper), and Reussir having no borrowed
parameters, so code that walks shared data (looking up a hash bucket
shared between map versions) writes reference counts that native Lean
only reads (hash-map-heavily-shared).

## Optimizations

The core translation is correct on its own; every optimization is a
separate pass in `lean2rr/LeanToReussir/Opt/`, registered by one line in
`Opt/Registry.lean`, and **all are on by default** (benchmarks use the
defaults). `lean2rr --list-opts` lists them; `--disable-opt NAME` (or
`L2R_DISABLE_OPTS=a,b` for `scripts/l2r.py`) turns one off, for testing.
A pass restricts itself only through checks it makes on every program, for
soundness.

| pass | what it does |
|---|---|
| `field-order` | record fields ordered by size, so records have no padding |
| `value-structs` | a structure with one field is represented by the field |
| `nat-arrays` | `Array Nat`/`Array Int` with one word per element |
| `split-map-loops` | an `Array.map` that changes the element representation writes a new array instead of going through `Box` |
| `placeholder-cache` | Lean's placeholder values built once |
| `float-lits` | float literals computed at compile time |
| `cheap-consts` | constants made of small literals (one-word `Nat`/`Int` values only) recomputed instead of cached |
| `prelude-repr` | `Nat.repr`/`Int.repr` by the runtime's GMP code |
| `jp-sink`, `jp-small` | join points moved to where they are used; small ones duplicated |
| `state-machines` | loops through join points: entering the loop and every jump inside it allocate nothing |
| `lazy-fields`, `nullary-scrutinee`, `sink-proj` | shapes that let Reussir reuse memory cells |
| `fresh-rebuild` | the error arm of a monadic bind rebuilds its freshly built result, so Reussir reuses the cell on the success path |

Parts that look like optimizations but are required (each with its reason
in the registry): the startup chain cut into chunks, loop state machines,
Stage 3's type recovery, closed-term chains, `Outline` (long functions cut
into pieces for rrc's sake) and functions kept out of rrc's inliner (build
time).

## Reussir

lean2rr needs Reussir built from source with lean2rr's local patches
(branch `l2r-local` of the checkout in `./reussir`, head `cc8e5aa5`:
Reussir `ef922049` plus 35 patches; the patches are in
[`../reussir-bugs/patches/`](../reussir-bugs/patches/), each explained in
depth in the file of its bug, indexed in
[`../reussir-bugs/README.md`](../reussir-bugs/README.md)).
They are local only, never submitted upstream, and each is reviewed
adversarially.
An independent audit checked whether each problem is really a Reussir
bug. Of the 34 documented problems, 30 are patched in `l2r-local` (33
patches), 1 has a patch not applied yet (bug 34, patch 0065: `rrc --emit
executable` compiled static code into a PIE, so lean2rr's binaries carried
text relocations; lean2rr's driver now passes `--relocation-mode pic`), and
3 are documented only; two more patches add
features lean2rr needs:

- **Real bugs fixed (21 patches):** wrong values after in-place reuse of a
  structure or variant cell (bug 2), `[value]` enum bytes lost (1), a
  layout mismatch that overflowed cells (8), compiler crashes (4, 5, 31),
  use-after-free (9, 14), the parser mixing up subtrees on very large
  files (12, in Reussir's parser library `cstree`), programs that did not
  compile (15, 19), wrong code after an LLVM assumption undid a pointer
  launder (26) and from a uniqueness analysis that proved a shared value
  unique (28), a texture placeholder dropped (21), non-reproducible builds
  (24), MLIR dumps that did not parse back (29), MLIR types whose trailing
  text was silently dropped (33), Reussir's own build (18), and build time
  made quadratic by Reussir's own code (10, 11b, 23).
- **A real bug with a flag workaround:** a static cell freed after 2^32
  references (6). Another nullary-constructor encoding avoids it; the patch
  keeps the default encoding for speed.
- **Build-time costs with a small fix (6 patches):** interprocedural SCCP
  (11), reuse across calls in deep matches (16), a straight-line `Nat`
  function (17), the inliner on lean2rr's conversion code (20), wildcard
  arms over wide enums (22), the call lowering's symbol lookups (30).
- **An optimization, not a bug:** token reuse picking a cell that never
  frees (7). It stays because the use-after-free fix (9) builds on it.
- **A missing feature, implemented locally:** freeing long or deep
  structures without recursion, in Lean's order (13, three patches;
  lean2rr's runtime needs it), and the same for a member behind
  `Nullable` (27).
- **Local additions (no bug):** a hook at the end of a drain that lean2rr's
  runtime uses for promises released inside a free (0040), and opaque
  handles that may be a tagged number instead of a pointer (0050), so that
  `Nat` and `Int` are one word with no allocation for small values
  (lean2rr's prelude needs it).
- **Documented only:** Rust allocations on mimalloc's aligned path
  (3, intended), and two costs whose fix would be a redesign: the inline
  expansion of copies of `[value]` records shared in a DAG (25) and the
  size of `--emit mlir` dumps (32).

Every Reussir problem met so far is documented with a reproducer,
including those lean2rr works around and those the audit classified as
intended behaviour or build costs, in
[`../reussir-bugs/`](../reussir-bugs/README.md), whose status table also
shows which patches are applied. lean2rr keeps its workarounds, so that it
also works with an unpatched Reussir (except that its runtime needs patch
0014).
Two parts of Reussir that its author offered (LLVM coroutine bindings,
dynamic-extent arrays) are not needed: lean2rr's tasks need stackful
contexts, which its runtime has, and Lean arrays are growable, which
dynamic-extent arrays are not.

## Possible future work

- Borrowed parameters (needs Reussir support) for code that walks shared
  data.
- Real parallelism for tasks (the scheduler is single-threaded by design).
- The C++-implemented parts of the `Lean` library, for metaprogramming
  programs.
- Calling a program's own C code (the parked branches `ffi-c` and
  `lean-externs`).
