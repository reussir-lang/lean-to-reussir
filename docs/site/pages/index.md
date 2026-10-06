# lean2rr: architecture and design

<p class="lead">lean2rr compiles Lean 4 programs to native executables through
Reussir. This site explains the design with diagrams and short text. It
describes the repository that it is built from: Lean {{v:lean}}, and Reussir
with lean2rr's local patches (<code>l2r-local</code> at {{v:reussir_head}}).</p>

<div class="note" markdown="1">
**How to read this site.** Each page is a summary. The markdown documents
in the repository are the authority, and each page links to them:

- [translation plan](repo:docs/translation-plan.md): every rule, with its reason;
- [implementation status](repo:docs/implementation-status.md): what works, results, performance;
- [implementation notes](repo:docs/implementation/README.md): every trick and special case;
- [runtime README](repo:runtime/README.md): the runtime's types and functions;
- [Reussir issues](repo:reussir-bugs/README.md): every Reussir problem (a bug, a cost or another kind), with its patch;
- [tests README](repo:tests/README.md): the test sets and the findings they cover.

The [glossary](glossary.html) defines the terms that these pages use.
</div>

## What lean2rr does

A Lean program is first compiled by Lean's own build (`lake build`). That
build writes `.olean` files. These files contain Lean's intermediate code
(LCNF) for every compiled declaration. lean2rr reads this code. It does not
parse Lean source.

lean2rr makes a typed Reussir program from the code. Reussir's compiler
`rrc` then compiles that program with LLVM. Reussir adds the reference
counting and reuses memory cells in place. A small runtime supplies what
Lean's C runtime supplies natively: big numbers, strings, files, processes,
tasks and more. Most of its rules come from the shared crate `lean-runtime`.

{{svg:flow}}

The driver `scripts/l2r.py` runs all the steps:

```
scripts/l2r.py Main.lean -o main
scripts/l2r.py ModuleName -o main --lean-path DIR
```

## The contract

<div class="rule" markdown="1">
**Functional equivalence.** The lean2rr build of a program gives the same
standard output, standard error and exit code as its native build.
</div>

The contract has limits. It applies when the output does not depend on these
things:

- **Pointer identity, raw addresses and sharing.** Only unsafe or
  implementation-level functions can see them (`ptrAddrUnsafe`,
  `isExclusiveUnsafe`, `dbgTraceIfShared`). lean2rr does not copy native
  addresses.
- **Timing races between tasks.** lean2rr runs all tasks on one thread,
  on lean-runtime's scheduler. It picks one schedule that native Lean can
  also produce.
- **The other known differences.** [Known differences](differences.html)
  lists them, grouped. Plan §10 has the full list.

lean2rr also does not copy bugs of Lean's own runtime. A suspected bug
becomes an intended difference only after review confirms it with the C
source, a reason and a native repro.

## Targets

| Topic | Decision |
|---|---|
| Programs | Lean code that uses only `Init` and `Std`: computation, data structures, basic IO (standard streams, files). |
| Layouts | lean2rr's own layouts come first. A Lean-compatible layout stays only where it costs nothing. |
| Network and async | `Std.Async`, sockets, timers and `Std.Internal.UV` work, but they are not targets now. |
| Parallelism | Not now. Tasks run on one thread. Real threads come later, and the design must not block them. |
| C code of the program | Never built, linked or called (see the extern rule below). Support for calling C is parked. |
| Externs of the program | See "The extern rule" below. |
| `import Lean` | Programs that only use data structures from `Lean` build. Lean's C++ externs (`Expr.mkData`, `evalConst`, ...) are not available: lean2rr refuses a program that reaches one, and names each. |
| Mathlib | Not a target. Its initializers reach Lean's C++ externs, so lean2rr refuses such a program. Computational code from such a library, written for `Init` and `Std` only, translates. |

## The extern rule

<div class="rule" markdown="1">
**Lean code only.** The project's rule for an `@[extern]` of the program
or of a package that it uses:

1. It runs Lean code: its `@[implemented_by]` target; else the program's
   own `@[export]` definition that its C symbol names, when the types and
   the compiled signatures agree; else its own Lean definition. Its C code
   (Lake's `extern_lib`) is never built or linked. This route has no data
   conversion: the Lean code works on lean2rr's own representations.
2. An extern with none of these (an `opaque`, an axiom) is refused at
   translation. The message names each such extern and the reason.
3. The only native code is Lean's runtime library: `leanrt` and the shared
   crate `lean-runtime`. An extern of the program is never bound to it,
   also when its C symbol names a runtime function. It runs its own
   definition, or it is refused, and the message names Lean's declaration
   to call instead.
</div>

The externs of Lean's own library (`Init`, `Std`) are not affected: the
runtime implements all of them. lean2rr's build prints a note that lists
the externs of the program that run their Lean definition. Plan §5.8
("Externs of the program") has the full rule.

## The shared runtime crate

lean2rr uses the shared crate `lean-runtime`
(github.com/QueClr/lean-runtime-rs, public). The crate holds Lean's runtime
behaviour, implemented once, in Rust that is safe by default. lean2rr takes
these parts from it:

- the rules: hashes, strings, floats, fixed-width integers, `libm`,
  `Nat`/`Int`, arrays, panics and the text of numbers;
- the IO: files, the standard streams, the file system, processes, the
  system queries, the exit, and the execution of panics and other ends of
  a program;
- the task scheduler, with its wait cores, `Std.Sync`, the event loop and
  the networking;
- the startup: `main`'s thread and native Lean's startup descriptors.

lean2rr keeps only its own representations, its hot paths and the glue
between them and the crate. The switch took nine steps, from 2026-10-04 to
2026-10-05. See [Runtime](runtime.html#the-shared-runtime-crate).

## Status

Counts with a † are taken from the repository when the site is built. The
other results are the last recorded runs.

| Check | Result |
|---|---|
| Runtime test suite | {{v:rt_tests}} programs† ({{v:rt_xfail}} marked `.xfail`†); at the last full run (2026-10-06), 336 of 337 identical to native Lean 4.34.0, some of them through expectation files; the other one is the `.xfail` test |
| Classic corpus | 18 programs × 3 sizes, identical to native, with all optional passes on and with all off |
| Reussir benchmark suite | 18 of 18 programs identical to native |
| Loader checks | {{v:env_cases}} cases†, all as expected |
| Lean's own compile tests | 72 programs of Lean's `tests/compile` and `tests/compile_bench`: all match native (checked with Lean 4.33) |
| Externs of `Init` and `Std` | all 717 of Lean 4.34 available; 706 checked by programs that call each one |
| Speed | against native Lean 4.34.0 (2026-10-04, largest size): faster on 15 of the 18 classic programs, about equal on the other 3; geometric mean 0.71× time and 0.69× memory; less memory on all 18 |
| Reussir | {{v:patches_applied}} local patches applied†, 0065 (position-independent code) and 0066 (texture cache) included |

[Testing](testing.html) explains each test set and the review process.

## Recent changes

Merged from 2026-10-04 to 2026-10-06:

- **The switch to `lean-runtime`**, in nine steps: the rules (steps 1
  and 2), the IO (step 3), the scheduler, `Std.Sync` and the event loop
  (step 4), the last copies of shared functions (step 5), the wait cores
  (step 6), the startup (step 7), the panic and exit executor (step 8),
  and a fix of a scheduler wait that could wait for ever (step 9).
- **Fast paths in the runtime library** (step 10): `Float.toString`,
  `Int` with one small operand, `Int` and string equality, array sets of
  records. Instruction counts against step 9: strings −20.2%, liasolver
  −14.4%, unionfind +5.0%. An array set that frees the last reference to a record
  releases its fields last first, as Lean does (see
  [Runtime](runtime.html#fast-paths-of-the-runtime-library-step-10)).
- **Signal watchers and the record free** (step 11): a one-shot signal
  watcher gets one signal (lean-runtime's fixes-9 to fixes-11). A set, a
  pop or a reference set that frees the last reference to a record puts
  the record on the pending stack as one cell: about 74 instructions per
  freed record, and unionfind +0.8% against step 9.
- **The extern rule** (above).
- **`conv-liveness`**, the 17th optional pass: Stage 4 generates its
  helpers only for live code (see [Optional passes](passes.html)).
- **Library initializers at startup.** The `initialize` declarations of
  `Init` and `Std` (`IO.stdGenRef`) run at their module's place, also when
  the program does not use them, as natively.
- **Array reads without counting traffic.** A read releases its
  container first, takes the element from a view and keeps every read
  function small enough to inline (see
  [Representations](representations.html#strings-and-arrays)). In
  lean-zip's compression loop, the counting stores fell from 77 to 47 and
  the read calls from 281 to 2.
- **Reussir.** Patches 0065 and 0066 are applied. Each
  entry is now a numbered *issue* with a kind: only a *bug* is wrong
  behaviour (see [Reussir](reussir.html#all-entries)).
- **A read of a constant is one load.** Each once-cell's value is also
  kept in a table at a fixed address, so a read is one load and a test, with
  no call (lean-zip fix 4). In lean-zip's codec loops, the once-cell calls
  fell from 17 to 0 and the loads from 170 to 49. A check fails the tests if
  a constant read in a loop becomes a call again.
- **Dependent types: the rule.** Types do not compute, so lean2rr erases
  them, and a value of unknown type is one enum, matched by its variant.
  `◾` items (types, type arguments, proofs) are not stored. An `lcAny`
  value is stored in the enum. The current version converts values between
  a layout for each type argument and the boxed layout. The planned layout
  rule gives each datatype one layout, so no value is converted (see
  [Dependent types](dependent-types.html#layouts-of-generic-types)).
- **Plan §10** lists the Lean runtime bugs that lean2rr does not reproduce
  (see [Known differences](differences.html#lean-bugs-we-do-not-reproduce)),
  the differences of programs that use the `Lean` package, and that
  Mathlib is not supported.
- **Performance** of the classic corpus, measured against native Lean
  4.34.0 (2026-10-04).

The [implementation status](repo:docs/implementation-status.md) lists the
possible future work.

## The pages

<div class="cards" markdown="1">
<div class="card" markdown="1">
#### [Pipeline](pipeline.html)
The stages from `.olean` to executable: what goes in, what comes out, and the key decisions.
</div>
<div class="card" markdown="1">
#### [Representations](representations.html)
How each Lean type is stored, with memory layouts.
</div>
<div class="card" markdown="1">
#### [Dependent types](dependent-types.html)
Types known only at run time: the uniform type `L2RBox`, examples, costs.
</div>
<div class="card" markdown="1">
#### [Runtime](runtime.html)
The runtime layers, memory management, the scheduler, IO, startup, and the shared crate `lean-runtime`.
</div>
<div class="card" markdown="1">
#### [Optional passes](passes.html)
Each optimization, what it does and what guards it. Generated from the registry.
</div>
<div class="card" markdown="1">
#### [Testing](testing.html)
Native builds as the oracle, the test sets, the review rounds.
</div>
<div class="card" markdown="1">
#### [Reussir](reussir.html)
What Reussir is, how lean2rr calls it, the issues met and the local patches.
</div>
<div class="card" markdown="1">
#### [Known differences](differences.html)
Where a lean2rr build can behave differently from the native build.
</div>
<div class="card" markdown="1">
#### [Glossary](glossary.html)
The terms these pages use, one meaning each.
</div>
</div>
