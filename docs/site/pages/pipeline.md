# Pipeline

<p class="lead">How a compiled Lean program becomes a Reussir program and then an
executable. Source: <a href="repo:docs/translation-plan.md">translation plan</a>
§1 to §5.</p>

{{svg:pipeline}}

## Why lean2rr starts from Lean's base code

Lean's compiler has three phases:

| Phase | What the code looks like |
|---|---|
| base | typed and polymorphic: type parameters and type arguments are explicit |
| mono | type variables erased to `lcAny`; concrete types such as `List Nat` stay |
| impure | boxing, reference counting and reset/reuse added |

Reussir must do all memory management itself, so lean2rr stops before the
impure phase. The saved mono code of a polymorphic function is not usable:
its type variables are `lcAny`, and the link to the real types is gone. So
lean2rr makes a monomorphic copy of the base code first (Stage 1). Then it
runs Lean's own mono passes on that copy (Stage 2). The result is optimized
mono code that still has exact types.

| Stage | Input | Output | Owner of the code |
|---|---|---|---|
| Loading | `.olean` files | an environment with every module and its extension states | lean2rr (`Env.lean`) |
| 1. Collect and monomorphize | base LCNF of the reachable declarations | one monomorphic copy per type instantiation | lean2rr (`Collect`, `Mono`) |
| 2. Mono pipeline | the monomorphic program | optimized mono LCNF with exact types | Lean's passes, driven by lean2rr (`Pipeline`) |
| 3. Check and recover types | mono LCNF | the same code, fewer `lcAny` | lean2rr (`MonoRetype`) |
| 4. Lowering | checked mono LCNF | Reussir functions and types | lean2rr (`Lower/*`, `Emit/*`) |
| After lowering | Reussir functions | the program text `prog.rr` | lean2rr (`Outline`) |
| rrc | `prog.rr` with the prelude | an executable | Reussir |

`lean2rr --emit STAGE` stops after a stage and prints its output:
`base`, `inst`, `mono`, `externs`, `retyped` or `rr`.

## Loading

- lean2rr imports the program's modules and Lean's library at the
  `private` level. Only this level gives the complete base LCNF of every
  declaration.
- lean2rr loads each extension's imported state. Without this, queries
  such as "is this a class" answer "no", and Lean's passes do less.
- lean2rr never runs the program's `initialize` actions. It loads the
  extension states without Lean's init step.
- lean2rr checks module names. A module named `Init.*`, `Std.*`, `Lean.*`,
  `Lake.*` or `L2RShim.*` must be the real file of Lean's toolchain or of
  lean2rr's shim. lean2rr compares files, not paths. Other modules with these
  names are rejected, because lean2rr trusts such modules.

## Stage 1: collect and monomorphize

**Roots.** The roots are `main`, every zero-parameter declaration of the
program's modules, the `initialize` actions, the `initialize` declarations
of `Init` and `Std` (`IO.stdGenRef`), `IO.Error.toString`, and the
`IO.Error` builders when the program uses fallible IO. Everything these
reach is collected: declarations with code, `@[extern]` declarations and
constructors. A constant that `main` never uses is still a root, because
native Lean evaluates it at startup.

**Instances.** A polymorphic declaration becomes one *instance* per list of
type arguments. Each instance gets a fresh name (`d._l2r.k`), so Lean's
passes in Stage 2 see only lean2rr's copies.

- lean2rr substitutes the type arguments and simplifies the types. This is
  what Lean's own specializer does.
- lean2rr keeps the type parameters as erased parameters. So each instance
  has exactly Lean's arity. Arity decides when work runs (see Stage 4).
- A higher-kinded argument is a type-level function. Substitution and beta
  reduction turn `m (β × σ)` into an ordinary type.

<div class="note" markdown="1">
**Rust analogy.** This is what `rustc` does with generic functions: one
copy per set of type arguments. Lean itself does not do this: natively
every value is a pointer to a boxed object, so one copy serves all types.
</div>

**Static dictionaries.** A type class instance arrives as a *dictionary*: a
record of functions. Lean's `simp` folds a dictionary only when it is
`let`-bound in the same function. So lean2rr also specializes a callee on a
*static dictionary*: one built only from instance constants and types. For
example, `Array.map` passes `Monad Id` to `Array.mapM`. Without the
specialization, `Monad Id` stays a runtime record with polymorphic methods,
which Reussir cannot type. A constant that calls a function or allocates
data is not part of a static dictionary. Natively it is evaluated once, and
the callee only reads it.

**Calls that Lean's `cse` merges across types.** Lean's mono `cse` compares
code after type erasure. So it can merge two calls of one function at two
different types into one call, which runs once. lean2rr's two instances
would be two calls, and a panic in them would print twice. So Stage 1 finds
these calls as `cse` does and gives them one instance and the same
arguments (`Mono.erasedMerges`):

1. The earlier call's instance, when its result can be used at the later
   call's type. An instance at `Nat` reads its inputs as `Nat` values. So
   every function in the result must have the same domain at both types,
   and no `lcAny` may hide the type argument.
2. Otherwise the instance at `lcAny` for each type argument that differs,
   for every call of the group. This is the uniform code that native Lean
   runs. Its closures take boxes, and each use reads them at its own type
   through a wrapper.
3. Otherwise the calls run apart: when a type argument that differs is a
   type former, when an argument of the earlier call cannot be used at the
   type of the argument it replaces, or when the calls are a closed term
   that Lean can share with the same call in other functions (then the
   calls run apart, as before this rule, unless the earlier rule merged
   them too).

A type parameter that shows nowhere in a function's type gets `lcAny` at
every call. All calls of the function then use one instance, as natively.

**When a type is not statically known.** Then a box (`LAny`) takes its
place (see [Representations](representations.html#the-box-lany)):

- a type that depends on a run-time value: Lean's base code already has
  `lcAny` there (see [Dependent types](dependent-types.html));
- a type argument that is not fully known: the instance is made at `lcAny`;
- polymorphic recursion: a request at a type that strictly contains the
  type of an instance on the same path goes to the *uniform instance*
  (every type argument `lcAny`);
- bounds: a type argument deeper than 64 or larger than 256 nodes becomes
  `lcAny`; past 1024 instances of one declaration, every new one is the
  uniform instance;
- existential values and dictionaries stored in data.

**Library code that relies on Lean's uniform objects.** `Array.map` and
`Array.modify` use unsafe code that is correct only because every Lean
value is a pointer. lean2rr translates that code as it is: `NonScalar`
becomes `lcAny`, the casts become boxing and unboxing, and the `box(0)`
placeholder becomes the *zero* of the expected type.

## Stage 2: Lean's mono pipeline

lean2rr runs Lean's own passes in Lean's order. Mutually recursive groups go
bottom-up, callees first. Lean's checker runs after every pass. This stage
has no new translation logic. Its job is to leave the code in the shape that
Stage 4 expects: no local functions, explicit join points, every binder with
its mono type.

{{gen:stage2}}

Main mono passes (Lean's): `simp` (inlining, constant folding, dead code),
`reduceJpArity`, `structProjCases`, `extendJoinPointContext`,
`floatLetIn`, `reduceArity`, `commonJoinPointArgs`, `lambdaLifting`,
`elimDeadBranches`, `cse`, `extractClosed`.

`toMono` also does semantic lowering for lean2rr: `Decidable` becomes
`Bool`, `Nat` constructors become `Nat.add x 1` and tests on 0, single-field
structures become their field (`Char` → `UInt32`, `Fin n` → `Nat`), and
`cases` on builtin types become accessor externs. lean2rr's copy gives the
field of an `Array`, a `ByteArray` or a `FloatArray` its own type
(`List α`, `Array UInt8`, `Array Float`), not `lcAny`.

## Stage 3: check and recover lost types

Mono code can still have `lcAny` where the type is known: types inferred
during the passes go through erased signatures, and the casts of the library
code above are erased. A binder at `lcAny` is a box, and every use at a
precise type unboxes it. Stage 3 gives such a binder its precise type where
the program determines it. Data types have one layout whatever their type
arguments, so Stage 3 types locals; it does not choose layouts.

<div class="rule" markdown="1">
**The rule.** A binder's type comes from what flows *into* it, never from
how it is used. A use at a precise type speaks only for its own branch.
</div>

The sources of a type:

- **definitions**: a `cases` field gets the constructor's field type, when
  the matched value's type is that constructor's inductive; a call gets the
  callee's result type; a join point parameter gets the type that all its
  jumps agree on;
- **result types**: a declaration gets `T` when all its returned values have
  type `T`, or when every call binds its result at `T`;
- **externs at unknown types**: a call of a polymorphic extern at `lcAny`
  (`Array.uget` at `NonScalar`) whose arguments determine the type
  arguments gets the type that the extern returns at them. The call
  `Array.toList ◾ a`, which `toMono` makes for a `match` on an array, goes
  to the extern's instance at the array's element type.

The fixpoint runs over the whole program until nothing changes. What it
does not recover stays `lcAny`, a box.

## Stage 4: lowering to Reussir

### Types

Each Lean type becomes a Reussir type. The rules are on the
[Representations](representations.html) page.

### Declarations and arity

A declaration becomes a Reussir function over its relevant parameters, with
Lean's *arity*: the number of parameters after Lean's optimizations.

- a call with exactly the arity runs the function;
- a call with fewer arguments builds a function value, and nothing runs;
- a call with more arguments runs the function and applies its result to
  the rest.

Stages 1 to 3 keep the erased parameters (types, type arguments, proofs),
so that Lean's passes see Lean's arities. Stage 4 removes them: the Reussir
function has no parameter for them, and a call passes no argument for
them. When the last parameters of a declaration are erased, the function
keeps one unit parameter for that group. So the body runs at the same
point as natively (see
[Dependent types](dependent-types.html#rule-4-examples)).

<div class="note" markdown="1">
**Why arity matters: an example.**

```lean
def mkAdder (n : Nat) : Nat → Nat :=
  let k := dbgTrace s!"prefix {n}" fun _ => n * n
  fun x => x + k
```

- Line 1: `mkAdder` takes a `Nat` and returns a function from `Nat` to `Nat`.
  In Rust terms: `fn mk_adder(n: Nat) -> impl Fn(Nat) -> Nat`.
- Line 2: `k` is `n * n`. `dbgTrace` prints `prefix n` to standard error
  before it computes the value.
- Line 3: the result is the function `x ↦ x + k`.

Lean's optimizer gives `mkAdder` arity 2. So natively `mkAdder 3 x` prints
`prefix 3` at every call. A translation with arity 1 would print it once.
lean2rr keeps Lean's arity, so it prints at every call too.
</div>

### Function values

lean2rr does not use Reussir closures. Each function type gets a generated
enum. A variant `p<m>_f` is a partial application of the target `f` with `m`
captured arguments. A generated function `l2r_ap<j>_T` applies a value: it
calls the target when its last argument arrives, as Lean's `lean_apply_n`
does. This is *defunctionalization*. A known target is a direct call.

### Join points

A join point is Lean's local continuation: code that several branches jump
to. Reussir has no join points, so lean2rr turns each one into structured
code.

{{svg:joinpoints}}

The choice matters for two reasons:

- **Stack use.** Lean runs self tail calls as loops. Under J1 and J2 the tail
  call stays in its own function, and LLVM turns it into a loop. Under J3 the
  loop becomes mutually recursive and can use stack per iteration. J4 makes
  such a loop one function again. With the optional pass `state-machines`,
  the entry point of that function is an integer, and the values of the
  loop go in parameter slots. A jump changes only the slots that it fills.
  On an integer entry point, LLVM threads the loop: a jump goes directly to
  the code that it enters.
- **Memory reuse.** J1 and J2 keep "take the old value apart" and "build the
  new value" in one function. Reussir's token reuse needs that to update in
  place.

### Externs and glue

A call of an extern of Lean's library becomes a call of the prelude
function with the extern's C symbol as its name (`lean_nat_add`). The
prelude function is either inline Reussir code (a fast path) or a call into
the Rust runtime: `leanrt`, or `lean-runtime` for the rules. For
externs over Lean-defined types (`Option`, `List`, `IO.Error`, processes,
references) lean2rr generates *glue*. An extern whose C symbol is an
`@[export]` Lean definition calls that definition directly, so its
semantics are exactly Lean's. lean2rr keeps no list of supported externs:
it checks that the prelude defines each function it calls. When the prelude
lacks one, lean2rr refuses the program at translation and names each such
extern.

An extern of the program runs Lean code (its `@[implemented_by]` target, a
matching `@[export]` of the program, or its own Lean definition), or it is
refused. See [the extern rule](index.html#the-extern-rule).

### Helpers for live code only

At the end of Stage 4, lean2rr generates helper functions: an unboxing
function per target type, an application function per function type,
function-value wrappers, and the casts between inductives. Each helper
matches the type numbers of a box or the variants of a function-value
enum. The optional pass `conv-liveness` generates a helper only when live
code reaches it, and an arm only for a type or a variant that live code
builds. Then it drops the functions that nothing reaches from the
entry point or from the runtime's entries. See
[Optional passes](passes.html#helpers-for-live-code-only-conv-liveness).

### Constants and startup

- Every zero-parameter declaration of the program's modules runs at startup,
  in Lean's initialization order, as natively. lean2rr rebuilds that order
  from the `.olean` record and the source structure.
- The `initialize` declarations of `Init` and `Std` (`IO.stdGenRef`) run
  at their module's place in the same order, also when the program does
  not use them. They open files, and they can fail, so they cannot wait
  until their first use. The other constants of Lean's library are pure,
  and lean2rr evaluates them lazily.
- A constant is a *once-cell* with an accessor. The value is computed once
  and never freed. A read is one load and a test: the runtime keeps each
  cell's value in a table at a fixed address, and a value whose bits are
  all 0 also has a flag (a second load). No read is a call.
- Closed terms (`extractClosed`) are evaluated lazily, once.
- The startup work is cut into functions of at most 128 steps, because one
  long chain overflows rrc's stack.

See [Runtime](runtime.html#startup) for the entry point.

## After lowering

- **Outline.** rrc's analyses grow faster than linearly with nesting depth
  and with straight-line length. So a tail path 32
  matches deep or 256 `let`s long is cut into functions. A recursive function
  keeps its loops: the cut part returns a step value, and the function makes
  the tail call itself. The step value is a `[value]` enum when the layout of
  its variants lets every move keep all bytes. Then a step needs no heap
  cell. Otherwise the step enum is shared.
- **Passes over the generated functions**: `sink-proj`.
- The text: `prog.rr`, with the functions of `prelude.rr` that it uses
  prepended (`prelude-liveness`).

## rrc

Reussir is a research compiler framework for reference-counted functional
programs (github.com/reussir-lang/reussir). Its front end is in Rust, its
back end in MLIR and C++, its runtime in Rust. Reusable memory is explicit
in its IR: a cell that dies becomes a *token*, and a later allocation of
the same size can use the token instead of new memory. Reussir does the
ownership analysis (Perceus-style reference counting), token reuse, drop
glue and LLVM code generation. `rrc` is its compiler driver.

{{svg:rrc}}

What lean2rr uses from Reussir:

| Feature | lean2rr's use |
|---|---|
| shared and `[value]` records and enums | Lean's inductive types ([Representations](representations.html)) |
| opaque `#[ffi]` types | `LStr`, `RVec`, `LCell`, handles: runtime types that do their own counting |
| tagged opaque handles | one-word `Nat` and `Int` |
| textures (`#[ffi(import)]` functions with a Rust body) | the prelude's calls into `leanrt`; inlined when compiled for the same CPU |
| token reuse, `--reuse-across-call` | in-place updates, as Lean's reset/reuse |
| `#[transform_anchor]` | keeps unboxing, wrapper and cast functions out of Reussir's MLIR inliner |

The driver builds the shared crate `lean-runtime` (the pinned submodule,
with cargo) and the runtime crate `leanrt`, each one cached. Then it runs
lean2rr and rrc, and links `leanrt`, `lean-runtime` and GMP. rrc compiles
each *texture* (the Rust body of a prelude function) with rustc, one run
per texture. lean2rr writes only the prelude functions that the program
uses, so a small program has about 75 textures, not about 480. The driver
gives rrc a cache directory, so rrc does not compile an unchanged texture
again.

## Key decisions

| Decision | Reason |
|---|---|
| Read `.olean` files, not source | Every Lean feature arrives as ordinary functions and data. |
| Monomorphize base code, then run Lean's mono passes | Lean's optimizations stay; exact types stay too. |
| Keep the point where a body runs | When work runs is observable (traces, panics). Erased parameters go in Stage 4; a trailing group keeps one unit. |
| Types from definitions only (Stage 3) | A use at a type speaks only for its branch; a guessed type can panic on another path. |
| Function values as generated enums | Applying a shared Reussir closure copies it; enums and a `match` do not allocate. |
| Join points J1/J2 first | Loops stay loops, and Reussir can reuse cells in place. |
| One layout per datatype, a one-word box in generic positions | Typed code never pays for boxing, and no value is converted. |
| Every optimization optional | The core translation is correct alone; each pass can be turned off for a test. |
