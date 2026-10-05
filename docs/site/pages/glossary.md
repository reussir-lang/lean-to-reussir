# Glossary

<p class="lead">The terms that these pages use. Each term has one meaning, and
each concept has one term.</p>

## lean2rr and its builds

lean2rr
:   The translator: it reads a compiled Lean program and writes a Reussir program.

native build
:   The executable that Lean's own compiler makes from a program (C code, `leanc`, Lean's C runtime). It is the reference for every test.

lean2rr build
:   The executable that lean2rr, rrc and the runtime make from the same program.

driver
:   `scripts/l2r.py`: it builds the runtime crates (`lean-runtime` and `leanrt`), runs lean2rr, runs rrc, and links the result.

functional equivalence
:   The contract: the lean2rr build gives the same standard output, standard error and exit code as the native build, except for the known differences.

known difference
:   A documented way in which a lean2rr build can behave differently from the native build (plan §10).

## Lean's compiler

LCNF
:   Lean's intermediate code for compiled declarations: `let`, `cases`, join points, `return`. The `.olean` files store it.

base, mono, impure
:   The three phases of Lean's compiler. Base code is typed and polymorphic. Mono code has type variables erased to `lcAny`. Impure code adds boxing and reference counting. lean2rr uses base and mono, never impure.

`lcAny`
:   Lean's "unknown type" in compiled code. Base code has it where the compiler cannot compute a type (`t.denote` for a variable `t`); mono code also has it for erased type variables. lean2rr stores a value of this type as an `L2RBox`.

erased value (`◾`)
:   A type, a proof or another value with no run-time meaning. lean2rr stores it as `L2RUnit`.

arity
:   The number of parameters of a declaration after Lean's optimizations. A call with exactly that many arguments runs the function.

join point
:   Lean's local continuation: code that several branches jump to (`jp`, `jmp`).

closed term
:   A subexpression without free variables that Lean's `extractClosed` makes into a constant `f._closed_N`, evaluated once at first use.

extern
:   A declaration with `@[extern "sym"]`: natively, C code under the symbol `sym` implements it (Lean's runtime, or C code of the program). lean2rr serves the externs of Lean's library with its runtime, and runs Lean code for the externs of the program (see [the extern rule](index.html#the-extern-rule)).

`.olean` file
:   A compiled Lean module, with its LCNF code and its environment data.

## Stages and types

Stage 1 to Stage 4
:   lean2rr's stages: collect and monomorphize; Lean's mono pipeline; check and recover types; lowering to Reussir.

monomorphization
:   Making one copy of a polymorphic declaration per list of type arguments, as `rustc` does with generics.

instance
:   One such copy, with a fresh name (`d._l2r.k`).

uniform instance
:   The instance with every type argument `lcAny`; its values of those types are `L2RBox`es. Polymorphic recursion and the instance bounds lead to it. A call whose type arguments are not statically known (a type unpacked from an existential, a partial application that leaves a type open) goes to an instance at `lcAny`: the uniform instance when no type argument is known.

dictionary
:   The record of functions that a type class instance passes at run time.

static dictionary
:   A dictionary built only from instance constants and types. lean2rr specializes a callee on it.

precise type
:   A type that lean2rr knows exactly, as opposed to `lcAny`.

relevant parameter
:   A type parameter that appears in a data field. Only relevant parameters make different generated types.

dependent type
:   A type that mentions a value (`Array t.denote`, `Vector α n`). A value that occurs only in a proof or an index is erased. When the type changes with a run-time value, the base code has `lcAny` there, and lean2rr stores the value as an `L2RBox`. See [Dependent types](dependent-types.html).

type family
:   A function that gives a type (`Ty.denote`, `fun n => Vector String n`). Stage 2 keeps a constant family or a type constructor. Any other family becomes `lcAny`.

## Representations

representation
:   The Reussir type that stores a value. One Lean type can have several representations (`List Nat` and `List L2RBox`).

shared type
:   A Reussir record or enum stored in a counted heap cell.

`[value]` type
:   A Reussir record or enum stored inline, never allocated.

cell
:   A heap object with a 32-bit reference count in its header.

immediate
:   A constructor without fields of a shared enum: a tagged pointer to a static cell, never allocated.

tagged handle
:   An opaque Reussir handle that may be a number instead of a pointer (local patch 0050). Reussir counts it only when its low bit is 0. `Nat` and `Int` are tagged handles.

`L2RBox`
:   The uniform type: a closed tagged union that lean2rr generates for each program (a shared enum), with one variant per concrete type that the program boxes, plus a unit variant. It stores a value whose type is not statically known. Code that needs the concrete type checks the tag.

storage type
:   The type in which an array stores its elements: the element's own type when it can cross Reussir's FFI boundary, an index for an enumeration, otherwise an `ElemBox`.

`ElemBox`
:   A generated one-field shared struct that wraps a value that cannot cross the FFI boundary.

conversion
:   Generated code that rebuilds a value from one representation into another. The result is a new, unshared value.

placeholder
:   Lean's `box(0)`, a value that is never read. lean2rr gives it the *zero* of the expected type.

function value
:   A Lean closure or partial application. lean2rr stores it as a variant of a generated enum per function type.

## Runtime

runtime
:   Everything a lean2rr build contains besides the program: the prelude, `leanrt`, `lean-runtime` and the shim.

prelude
:   `runtime/prelude.rr`: Reussir source prepended to every program, with one function per Lean extern.

`leanrt`
:   lean2rr's own Rust crate, linked into every lean2rr build: lean2rr's representations, and the glue between them and `lean-runtime`.

shim
:   `L2RShim`: lean2rr's Lean library for the `Std.Internal.UV` externs and a few others, compiled with the program.

glue
:   Code that lean2rr generates for an extern over Lean-defined types.

texture
:   The Rust body of a Reussir `#[ffi(import)]` function. rustc compiles it; LLVM can inline it.

once-cell
:   A runtime slot that holds a constant. The value is computed once and never freed.

deferred task
:   A task that runs only when needed, when the running code blocks, or when `main` returns.

context
:   A stack on which lean-runtime's scheduler runs `main` or a task. Contexts take turns on one thread.

effect point
:   A point (output, exit, `IO.sleep 0`) where the scheduler lets due timers, ready contexts and old queued tasks run first.

`sync` dependent
:   A task created with `sync := true`: it runs on the thread that finishes its source, before anything else.

wait core
:   A wait protocol of lean-runtime's scheduler: the wait for a thunk or a constant that another context computes, the reference rule of a program that creates tasks, and the resolution of a promise put off to the end of a free.

pending stack
:   The per-thread stack of cells to free. Frees use it instead of recursion (local patches 0013 to 0015).

## Reussir

Reussir
:   The compiler framework that lean2rr targets: reference counting and memory reuse for functional programs, over MLIR and LLVM.

rrc
:   Reussir's compiler driver.

token reuse
:   Reussir's way to build a new cell in the memory of a cell that dies (Lean's reset/reuse).

local patch
:   A change to Reussir that lean2rr's builds use, on branch `l2r-local` of `./reussir`. Never pushed upstream.

issue
:   A numbered entry of `reussir-bugs/README.md`: a Reussir problem that lean2rr met. Its kind (bug, cost, missed optimization, missing feature, intended) says what it is. Only a bug is wrong behaviour.

## Testing and review

oracle
:   The native build's output, against which a lean2rr build is compared.

classic corpus
:   The 18 benchmark programs of `tests/classic`, each at three sizes.

runtime test
:   A program `tests/runtime/Rt*.lean` that checks one feature or one finding.

`.xfail`
:   A file that marks a runtime test as known to fail, with the reason.

expectation files
:   `NAME.native.*` and `NAME.l2r.*`: the expected outputs of the two runs of a runtime test that shows an intended difference (plan §10). Each run is compared with its own file.

review round
:   A period in which reviewers try to break lean2rr and write their findings.

finding
:   A defect that a reviewer reports, with an id (`RV9C-02`), a repro, and the expected and actual output.

judge
:   The step that decides whether a finding is real before anyone fixes it.

lean-runtime
:   The shared runtime crate (github.com/QueClr/lean-runtime-rs, the submodule `third_party/lean-runtime`): Lean's runtime behaviour in Rust, safe by default. lean2rr uses its hash, string, float, fixed-width integer, libm, `Nat`/`Int`, array, panic and number-text rules, its IO, its startup, its task scheduler with the wait cores, and its event loop (features `io`, `proc-title`, `startup-fds`, `sched`, `stack-overflow` and `net`), with its own GMP numbers behind the crate's big-number traits.

switch step
:   One of the seven steps (2026-10-04 to 2026-10-05) in which lean2rr's runtime moved to `lean-runtime`.
