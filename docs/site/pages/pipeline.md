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
| After lowering | Reussir functions | the program text `prog.rr` | lean2rr (`ArrayLits`, `Outline`) |
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
these calls as `cse` does and gives the later call the earlier call's
arguments (`Mono.alignErasedMerges`). It refuses when the two result types
differ at a function, a runtime object or something it cannot classify,
because no conversion exists there.

**When a type is not statically known.** Then the uniform type `L2RBox`
takes its place (see [Representations](representations.html#the-uniform-type-l2rbox)):

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
becomes `lcAny`, the casts become conversions, and the `box(0)`
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
`cases` on builtin types become accessor externs.

## Stage 3: check and recover lost types

Mono code can still have `lcAny` where the type is known: types inferred
during the passes go through erased signatures, and the casts of the library
code above are erased. A binder at `lcAny` is a `L2RBox`, and every use at a
precise type converts it. For an array that is a copy of every element.

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
  type `T`;
- **parameters from callers**: an array parameter gets `T` when every call
  site passes `T` (lean2rr then checks the body under that assumption);
- **the `map` loops** of `Array.map`: the result is `Array β` when every
  stored value is a `β`;
- **references**: an `ST.Prim.mkRef` at a precise type gives a typed
  reference, which flows to its binders.

The fixpoint runs over the whole program until nothing changes. Two
optional passes work here: `split-map-loops` (a `map` that changes the
element representation reads one array and writes a new one) and
`uniform-updates` (an update of a container whose element type depends on a
value runs on the uniform container, so it boxes one element, not the whole
array). See [Optional passes](passes.html).

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
  such a loop one function again.
- **Memory reuse.** J1 and J2 keep "take the old value apart" and "build the
  new value" in one function. Reussir's token reuse needs that to update in
  place.

### Externs and glue

An extern call becomes a call of the prelude function with the extern's C
symbol as its name (`lean_nat_add`). The prelude function is either inline
Reussir code (a fast path) or a call into the Rust runtime `leanrt`. For
externs over Lean-defined types (`Option`, `List`, `IO.Error`, processes,
references) lean2rr generates *glue*. An extern whose C symbol is an
`@[export]` Lean definition calls that definition directly, so its
semantics are exactly Lean's. lean2rr keeps no list of supported externs:
when the prelude lacks one, rrc reports an unknown function.

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
  and never freed.
- Closed terms (`extractClosed`) are evaluated lazily, once.
- The startup work is cut into functions of at most 128 steps, because one
  long chain overflows rrc's stack.

See [Runtime](runtime.html#startup) for the entry point.

## After lowering

- **Literal tables.** A run of 32 or more small `Nat` literals pushed onto
  an `Array Nat` becomes one call that reads a generated table.
- **Outline.** rrc's analyses grow faster than linearly with nesting depth
  and with straight-line length (Reussir bugs 16 and 17). So a tail path 32
  matches deep or 256 `let`s long is cut into functions. A recursive function
  keeps its loops: the cut part returns a step value, and the function makes
  the tail call itself.
- **Passes over the generated functions**: `sink-proj`.
- The text: `prog.rr`, with `prelude.rr` prepended.

## rrc

{{svg:rrc}}

The driver builds the runtime crate `leanrt` once (cached by a hash of its
sources), runs lean2rr, then runs rrc, and links `libleanrt.rlib` and GMP.
If rrc crashes, the driver tries once more without `--reuse-across-call`
(a workaround for Reussir bug 4). See [Reussir](reussir.html).

## Key decisions

| Decision | Reason |
|---|---|
| Read `.olean` files, not source | Every Lean feature arrives as ordinary functions and data. |
| Monomorphize base code, then run Lean's mono passes | Lean's optimizations stay; exact types stay too. |
| Keep Lean's arities exactly | When work runs is observable (traces, panics). |
| Types from definitions only (Stage 3) | A use at a type speaks only for its branch; a guessed type can panic on another path. |
| Function values as generated enums | Applying a shared Reussir closure copies it; enums and a `match` do not allocate. |
| Join points J1/J2 first | Loops stay loops, and Reussir can reuse cells in place. |
| Uniform `L2RBox` only where needed | Typed code never pays for boxing. |
| Every optimization optional | The core translation is correct alone; each pass can be turned off for a test. |
