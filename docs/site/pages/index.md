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
- [Reussir bugs](repo:reussir-bugs/README.md): every Reussir problem, with its patch;
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
tasks and more.

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
- **Timing races between tasks.** lean2rr runs all tasks on one thread. It
  picks one schedule that native Lean can also produce.
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
| `import Lean` | Programs that only use data structures from `Lean` build. Lean's C++ externs (`Expr.mkData`, `evalConst`, ...) are not available. |

## The extern rule

<div class="rule" markdown="1">
**Lean code only.** The project's rule for externs:

1. An `@[extern]` of the program or of a package it uses is compiled from
   its Lean definition. Its C code (Lake's `extern_lib`) is never built or
   linked. This route has no data conversion: the Lean definition works on
   lean2rr's own representations.
2. An extern with no Lean definition (`@[extern] opaque`) is refused at
   translation, with a clear message.
3. The only native code is Lean's runtime library: `leanrt` today, moving
   into the shared crate `lean-runtime`. A program extern that re-declares
   one of these runtime functions with a matching signature uses lean2rr's
   runtime version.
</div>

**Current state.** The rule is implemented and in review, not merged yet.
Until it is merged, lean2rr fails such a program at the rrc build with an
unknown function. The externs of Lean's own library (`Init`, `Std`) are not
affected: the runtime implements all of them.

## The shared runtime crate

lean2rr uses the shared crate `lean-runtime`
(github.com/QueClr/lean-runtime-rs, public). The crate holds Lean's runtime
semantics, implemented once, in safe Rust; lean2rr takes the hash, string,
float, fixed-width integer, libm, `Nat`/`Int`, array, panic and number-text
rules from it so far, and keeps only its hot paths and the glue to its own
representations. See [Runtime](runtime.html#the-shared-runtime-crate-plan).

## Status

Counts with a † are taken from the repository when the site is built. The
other results are the last recorded runs.

| Check | Result |
|---|---|
| Runtime test suite | {{v:rt_tests}} programs† ({{v:rt_xfail}} marked `.xfail`†); 231 of 231 identical to native Lean 4.34.0 at the last full regression (2026-10-03) |
| Classic corpus | 18 programs × 3 sizes, identical to native, with all optional passes on and with all off |
| Reussir benchmark suite | 18 of 18 programs identical to native |
| Loader checks | {{v:env_cases}} cases†, all as expected |
| Lean's own compile tests | 72 programs of Lean's `tests/compile` and `tests/compile_bench`: all match native (checked with Lean 4.33) |
| Externs of `Init` and `Std` | all 717 of Lean 4.34 available; 706 checked by programs that call each one |
| Speed | faster than native on 16 of 18 classic programs, about equal on 2 (measured with Lean 4.33; not measured again for 4.34) |
| Reussir | {{v:patches_applied}} local patches applied†; patch 0065 reviewed, not applied yet; patch 0066 (texture cache) reviewed, not applied yet |

[Testing](testing.html) explains each test set and the review process.

## Work in progress

As of 2026-10-04, this work is under way and not in the repository's main
line yet:

- the extern rule (above): implemented, in review;
- fixes found by testing other programs through lean2rr: the release order
  of handles lent to a call, `libm` calls that LLVM must not fold, and the
  overflow message of `Array.replicate`;
- plan §10's list of Lean runtime bugs that lean2rr does not reproduce
  (see [Known differences](differences.html#lean-bugs-we-do-not-reproduce));
- the move of the runtime's IO and scheduler into `lean-runtime`.

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
The runtime layers, memory management, the scheduler, IO, startup, and the shared runtime plan.
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
What Reussir is, how lean2rr calls it, and the local patches.
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
