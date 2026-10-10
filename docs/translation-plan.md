# lean2rr translation plan

How a Lean 4.34 program becomes a Reussir program: what each stage receives,
what it does, and what it hands on. The goal is that every rule here is
*right*: the translated program behaves like the Lean program. Each rule
states what it does and why it is correct in plain terms. Reviewers check
the rules against Lean's actual behaviour (its compiler sources, `lean.h`,
and native executables), and tests compare our executables with native
ones.

Code examples are schematic: they use readable names and field syntax.
lean2rr's real output uses mangled names (`l_main___l2r_0_`), generated
type names (`T_Tree_12` with variants `c_leaf`, `c_node`), positional
records with alignment-sorted fields, and the prelude's `lean_*`
functions; `lean2rr --emit mono` and `--emit rr` show it. §5.10 has a real
example. Where behaviour differs from native Lean, §10 lists it.

---

## 1. The flow at a glance

```
Lean source
  │  lake build (stock Lean 4.34)
  ▼
base LCNF, typed, saved in every .olean ── Stage 1: collect + monomorphize (ours)
  ▼
monomorphic base LCNF, closed program ──── Stage 2: Lean's own mono pipeline (Lean's passes)
  ▼
mono LCNF with exact types ─────────────── Stage 3: check, recover the few lost types (ours)
  ▼
checked mono LCNF ──────────────────────── Stage 4: lower to Reussir (ours)
  ▼
prog.rr + runtime ──────────────────────── rrc: Perceus ownership, token reuse, LLVM
  ▼
executable
```

**Why cut Lean's pipeline here.** Lean compiles in three phases:
- **base** is typed and polymorphic;
- **mono** has type variables erased;
- **impure** adds boxing, reference counting and reset/reuse.

Reussir must do all memory management itself, so we stop before impure. Of
the two remaining phases:
- Lean's saved *mono* code cannot be used directly. It is polymorphic code
  with type variables erased to `lcAny`, and the link between them is
  gone.
- But mono erases only type *variables*: `toMonoType` keeps concrete types,
  so `List Nat` stays `List Nat`.

So we monomorphize the *base* code first (Stage 1), then let Lean's own
`toMono` and mono optimizations run on the monomorphic program (Stage 2).
The result is optimized mono code that still carries exact types, which we
confirmed on a hand-monomorphized probe. Stage 2 runs Lean's own passes,
with two of them replaced by lean2rr's copies that keep more types (§3).
Stage 1 adds type specialization and runs Lean's base-phase `simp` on each
instance; Lean's base `specialize` is not run again (§7).

### Code structure and passes

`lean2rr/Main.lean` reads as the pipeline, with an `--emit` checkpoint
after the stages: Stage 1 (`monomorphize`, `--emit inst`), Stage 2
(`runStage2`, `--emit mono` and `externs`; before it and after it,
`retypeErasedData`), Stage 3 (`retypeMono`, from the
declarations the entry point calls, `--emit retyped`), the registry's
passes over mono LCNF, Stage 4 (`lowerProgram`, with the registry's
lowering hooks), `Outline`, the
registry's passes over the generated functions, and the program text
(`--emit rr`). The modules of
`lean2rr/LeanToReussir/`:
- loading: `Env` (importing the program's modules with their extension
  states), `Collect` (reachability; `--emit base`);
- Stage 1: `Mono` (instances), `Passes` (running Lean's passes, for Stage
  1's recompilation and for Stage 2), `Relevance` (relevant type
  parameters, also used by Stage 4);
- the `--stats` dry run: `Stats`, `Specialize`, `Retype`;
- Stage 2: `Pipeline` (the driver), `TypedToMono`,
  `TypedStructProjCases` and `ExtractClosedK` (lean2rr's copies of three
  Lean passes), `MonoTypesKeep`, `CompileRecord` (what the `.olean`
  records of Lean's compilation: its order and its closed terms, also read
  by `Emit/Startup`);
- between the stages: `ErasedData` (a parameter of type `lcErased` that
  receives data gets the type `lcAny`, after Stage 1 and after Stage 2: a
  Lean compiler bug that lean2rr does not reproduce, §10);
- Stage 3: `MonoRetype`;
- Stage 4: `RR` (the `.rr` syntax tree and its text), `LowerBase` (state,
  type translation), then `Lower/*.lean`, each importing the previous one:
  `Ctx` (the code-lowering context), `FnValues`, `LazyForce`, `Conv`,
  `Decls`, `Externs`, `LazyGlue`, `Process`, `Promises`, `Identity`,
  `ExternCall`, `Borrow` (release times of borrowed resources, §5.8),
  `Values`, `JoinPoints`, `StateMachine` (J4), `Hooks`,
  `Code` (`lowerCode`, `lowerDecl`), `Finish`; and `Live` (the
  reachability of the optional pass `conv-liveness`, §5.3, used by
  `Externs` and `Finish`);
- the program: `Emit/Startup` (initializer order, the startup chain),
  `Emit/Entry` (the entry point), `Emit/Program` (`lowerProgram`, which
  splices chains of closed terms before lowering, and the lowered
  program's steps),
  `Outline` (deep and long tail paths and `let` values cut into
  functions, for rrc; run before the optional passes over the generated
  functions);
- `Dump`: typed LCNF dumps for the `--emit` checkpoints;
- `PassConfig`: the configurable parts of the pipeline; `Opt/*.lean`: the
  optional passes, and `Opt/Registry.lean`.

`lean2rr/L2RShim.lean` is a library of its own (built with lean2rr, in its
build directory, which the driver passes as `L2R_SHIM_DIR`): Lean implementations of `Std.Internal.UV`'s externs
and of the few Lean definitions lean2rr replaces (§5.8), which `Env`
imports with the program and Stage 1 calls instead (`Mono.redirectTarget`).

Outside `lean2rr/`: `runtime/` (the prelude `prelude.rr` and the runtime
crate `leanrt`), `scripts/l2r.py` (the driver: lean2rr, then rrc),
`reussir-bugs/` (the Reussir issues met, bugs and costs and the other
kinds, their repros and the local Reussir patches),
`tests/`, `docs/`.

The core translation is the plain one: the rules of this plan without the
optional passes, and correct on its own (the classic corpus at every size
and the runtime suite match native Lean with every optional pass off).
Each optimization is a module of `Opt/` with an `install : PassConfig →
PassConfig` that plugs it into a hook of `PassConfig`, keeping what was
installed before: a representation choice of the type translation (record
field order, `[value]` structs, placeholders kept in once-cells), a pass
over the checked mono declarations
(`monoPasses`), a pass over Stage 2's declarations that leaves some out
before Stage 3 (`prunePasses`), Lean definitions replaced by prelude functions, a lowering
hook (`LowerHooks`: the body before lowering, the J1′ choice, the form of
J4's state machine, constant caching, the binding of a `cases`
alternative's fields), the choice of which helpers Stage 4 generates at
the end (`convLiveness`: only for live code, §5.3), or a pass over the
generated Reussir functions (`rrPasses`). Every hook's default is the
plain translation. A pass keeps
its own state in the code-lowering context's extension slot
(`CodeCtx.ext`), not in the core's.

`Opt/Registry.lean` lists every pass in one place: Stage 2's edits of
Lean's pass lists (two passes replaced; three skipped in their place:
`inferVisibility` and `toImpure`, which are not run, and `extractClosed`,
which runs at the end; each with its reason); the optional passes, one
line each (name, enabled by default, description, `install`), in
installation order (it says what the order means for each kind of
hook); and the parts that look optional but are not, with the reason:
the startup chain's chunks (rrc's stack), J4's state
machines (a loop through an outlined join point would use stack per
iteration), Stage 3's type recovery from call sites (an array left at
`lcAny` would be copied at every crossing), closed-term chains not cached
(an array literal would need memory quadratic in its length), `Outline`
(rrc's build time and memory, and the size of the `.rr` text) and the
functions kept out of rrc's MLIR inliner (rrc's build time and memory on
polymorphic recursion, §5.3).
`lean2rr --list-opts` prints it, and `lean2rr --disable-opt NAME` turns one
optimization off for a run (`--enable-opt NAME` one that is off by
default; `scripts/l2r.py` passes both on, also from `L2R_DISABLE_OPTS=a,b`
and `L2R_ENABLE_OPTS`). To remove an optimization, delete its line; to add
one, write `Opt/Name.lean` with the transformation and its `install`,
import it in the registry and add its line. With all optional passes off,
and with each one off in turn, the classic corpus and the runtime tests
match native Lean.

---

## 2. Stage 1 — collect and monomorphize

### 2.1 Input

Base LCNF is read for every declaration the program can reach, from the
compiled `.olean` files (`getBaseDecl?`). It is A-normal form: `let`,
`cases`, local `fun`, join points (`jp`/`jmp`), and `return`. Type
parameters and type arguments are explicit. Example, `Tree.insert` with
`[Ord α]`:

```
def Tree.insert α inst x t : Tree α :=
  cases t : Tree α
  | Tree.leaf => let r := @Tree.node α t x t; return r
  | Tree.node l k r =>
    let cmp := inst # 0;            -- Ord.compare, projected from the dictionary
    let o := cmp x k;
    cases o : Tree α
    | Ordering.lt => let l' := @Tree.insert α inst l x; let n := @Tree.node α l' k r; return n
    | Ordering.eq => return t
    | Ordering.gt => ...
```

### 2.2 Reachability

The roots are:
- `main`;
- everything that runs at startup (§5.12): every zero-parameter
  declaration of the program's modules, and the `initialize` actions and
  the init functions of `initialize` constants, of the program's modules
  and of the `Init` and `Std` modules that natively are initialized;
- `IO.Error.toString`, which the entry point uses to report an uncaught
  exception (§5.11);
- the `IO.Error` builders, once the program reaches a fallible IO extern
  (§5.8).

Everything referenced from reachable code is collected:
- declarations with code;
- `@[extern]` declarations: those of Lean's library are provided by the
  runtime; any other runs its Lean definition, or the function its C
  symbol binds to (§5.8, "Externs of the program");
- constructors.

Nothing else can occur in a program Lean compiled: Lean refuses to compile
code that uses noncomputable constants. Anything else is a lean2rr bug, and
Stage 4 then fails with "unknown callee". Because every constant of the
program is a root, a constant that `main` never uses is still translated,
and can make the translation or link fail (§10).

### 2.3 Instances

A polymorphic declaration becomes one monomorphic copy, an *instance*, per
distinct list of type arguments it is used with. `main` has none. It calls
`Tree.insert` at `α := Nat`, so the instance `Tree.insert@Nat` is created;
that instance's calls create further instances, and so on. Each instance
gets a **fresh name** that no Lean module uses. This matters in Stage 2: the
fresh names guarantee Lean's passes only ever see our monomorphic copies,
never Lean's saved polymorphic versions.

How an instance is built: substitute each type parameter by its type argument
everywhere and re-simplify the types. This is what Lean's own specializer
does (`Specialize.mkSpecDecl`), with one difference: the type parameters are
*kept*, as erased parameters, so that the instance has exactly Lean's arity
(§5.2). Dropping them would, for example, turn a polymorphic function with
only type parameters into a zero-parameter declaration: a constant
evaluated once at startup, while Lean runs its body at every use. Stages 2
and 3 see these arities; Stage 4 removes the erased parameters, keeping one
unit parameter for a function's trailing erased ones (§5.2, rule 4). Lean represents a
higher-kinded argument as a type-level function, e.g.
`StateT Nat Id ↦ fun α => Nat → α × Nat`. Substitution plus beta reduction
therefore turns `m (β × σ)` into an ordinary type such as
`Nat → (β × Nat) × Nat`.

Sometimes a type argument is not statically known, for example a type taken
out of an existential package. The instance is then built with that argument
set to `lcAny`, Lean's own "unknown type". Values of that type use the
uniform `Box` representation (§5.1). Lean itself treats every value this
way, so this is always correct, only slower. A type argument whose values
are types (`Type`, `Type → Type`) also gives the instance at `lcAny`: at
`Type`, a parameter `x : α` would become a type parameter, which Lean's
passes erase (so `f x + f y` would become `f ◾ + f ◾`, one call after
`cse`), where natively it is a data parameter (`lcAny`, given `box(0)`).

Natively a declaration is one function at every type, and Lean's mono-phase
`cse` compares mono values, with type arguments erased: a call merges into
an earlier call of the same declaration with the same value arguments even
at other type arguments (`gp xs none` used as an `Option String`, then as
an `Option (Nat → Nat)`), and runs once; the merged variable keeps the first
call's type. Instances at the two types would be two calls, and a panic or
trace in them would print twice. So Stage 1 finds these groups of calls in
each instance as `cse` does, on the values `toMono` makes (type arguments
erased, merged variables identified, a trivial structure such as `Subtype`
or `Fin` taken for its field, `Decidable` for `Bool`; one scope per `cases`
alternative, join points in the enclosing scope, a local function's body in
a scope of its own, since Lean's `cse` runs after lambda lifting;
`@[never_extract]` calls apart), and gives the calls of a group one
instance and the same arguments (`Mono.erasedMerges`,
`Mono.alignErasedMerges`). Stage 2's `cse` then merges them as natively,
and a use of the merged value at another type converts it (§5.1: a box, an
unboxing, or a wrapper of a function value).

With one layout per datatype, the two values need no conversion as data.
But an instance at concrete types reads its inputs at those types:
`fst@Nat` unboxes a list element as a `Nat`, and its `Nat → Nat` closure is
not a `String → String`. A value made by the earlier call's instance takes
inputs of the later call's types only through its function values. So:
1. The calls take the earlier call's instance when its result *serves*
   every later call's result type (`Mono.serves`): walked in parallel as
   `toMono` sees them, the two types differ only where no value has both
   types (`none : Option String` and `none : Option (Nat → Nat)`; nothing
   is both a `String` and a function), and every function in them has the
   same domain at both types. Equal types that mention `lcAny` do not
   serve: `lcAny` can hide the type argument (`(b : Bool) → (if b then List
   α else Unit) → Nat` is `Bool → lcAny → Nat` at every `α`). Function
   codomains must convert too (a closure is converted when it is used),
   and the contents of a thunk, a task, a reference or a promise are not
   followed. This keeps the merged variable's type as natively, so Lean's
   closed-term cache, which compares types, shares terms with other
   declarations as natively.
2. Otherwise the calls take the instance at `lcAny` for each type argument
   that differs, the earlier call too (`Mono.uniformArgs`). That is the
   uniform code native Lean runs: its closures take boxes, and each use
   reads them at its own type through wrappers (`mkO n : Option (α → α)` at
   `Nat` and at `String`: one `Box → Box` closure). The earlier call's value
   arguments go into it, and it can return them, so each argument that
   replaces another variable must serve at that variable's type, unless
   both are calls of one group at `lcAny` (the uniform value serves at every
   type of its group). A type argument that differs and is a type former
   prevents this. A closed group (the earlier call is a closed term) takes
   the instance at `lcAny` only where the earlier call's instance does not
   change, or where Stage 1's test before the review of the dependent-type
   work (`lcAny` hides nothing, function types must be equal) aligned it to
   the earlier call's instance too: Lean's closed-term cache shares the
   merged call with the same call at the earlier call's types in other
   functions, and the instance at `lcAny` is a closed term of its own.
3. Otherwise only the calls of 1 are aligned; the others run apart (§10).

A type parameter that shows nowhere in a declaration's LCNF type (`len {α}
(b : Bool) (v : if b then List α else Unit) : Nat` is `Bool → lcAny → Nat`
at every `α`; a phantom parameter) gets `lcAny` at every call, so all calls
share one instance (`Mono.typeParamHidden`): the instances would all have
one type, and natively one closed term serves such a call at every type.

Constructors are not renamed by Stage 1 and merge in Stage 2 as they are;
extern instances and instances (dictionary builders) compute nothing
observable and keep their per-type instances. Lean's closed-term cache
compares types, so closed calls at two types in two declarations stay two
closed terms, natively too; after a merge into the earlier call's instance,
one declaration's call reads the other's closed term as natively
(cross-test XT-6, fixture A482; review XT6-01, XT6-02, XT6-03, XT6-04;
shared cases A833, A1028, D71TesterT23; tests `RtCseAcrossTypes`,
`RtCseFnValues`, `RtCseResidual`, `RtCseFnField`, `RtCseFnTrivial`,
`RtCseFnResult`, `RtCseHiddenAny`, `RtCseUniform`, `RtCseClosed`,
`RtCseApart`).

### 2.4 Type classes

After substitution, a dictionary falls into one of two cases:
- **Dictionaries with monomorphic methods** (`Ord Nat`, `BEq String`,
  `Hashable K`) are plain records of functions. They stay runtime values,
  and `inst # 0` is an ordinary field access.
- **Dictionaries with polymorphic methods** (`Monad m`, `ForIn`, …) contain
  functions whose own types quantify over types. Reussir cannot type such
  a record. We run Lean's base-phase `simp` on the instance. It inlines
  statically known instances and folds `inst # i` projections into direct
  calls, which is exactly the optimization Lean itself applies. The
  resulting direct calls create new instances (§2.3).

`simp` folds only dictionaries that are `let`-bound in the same function. A
dictionary that arrives as a *parameter* (`Array.mapM` receives `Monad Id`
from `Array.map`) would stay a runtime value. So, like Lean's specializer,
lean2rr also specializes callees on **static dictionaries**: a dictionary
built only from instance constants and types (and projections of such). A
constant counts only if it is a dictionary of functions: its evaluation
builds the class's structure (and its parents'), closures, constructors
without fields and small numbers, and nothing else. One that calls a
function (`instance : Inhabited Grid := ⟨mkGrid 300⟩`) or allocates data (a
list or record literal, a `Thunk.mk`, a string or big number literal) does
not count: natively it is evaluated once, at startup, and a callee reads its
fields, while `simp` in a callee specialized on it would copy its body to
the projections, to run at every call: the call again, the literal rebuilt,
a new thunk forced again (round 7 RV7F-02, RV7F-04; test `RtDictConst`).
Only a dictionary's functions gain from the copy: they become direct calls.
The instance key then includes the dictionary. The callee's instance binds that
parameter to the dictionary itself, rebuilt as `let`s at its start, and
`simp` folds its projections into direct calls. The parameter stays, unused,
so the arity is unchanged.

Rebuilding evaluates the dictionary again in the callee, and `simp` can
move part of it into a method's lifted lambda, so it may run once per method
call. Lean's own specializer copies the dictionary's code into the
specialization in the same way, so native code also rebuilds dictionaries,
but not necessarily as often. The difference is visible only when an
instance function traces or panics (for example `dbgTrace` in an instance:
3 traces native, 5 under lean2rr in one test), or costs time when it
computes something (§10). A dictionary is bounded like a type argument
(depth 64), because polymorphic recursion builds ever larger ones.

A dictionary with polymorphic methods is sometimes *not* statically known:
it is stored in a data structure, or passed through code that neither Lean
nor we specialized. Its polymorphic methods are then instantiated at `lcAny`
and work on boxed values (§5.1), just as in Lean's uniform representation.
Statically known dictionaries, the common case, take the fast path above.
`lean2rr --stats` reports how often the slow path occurs.

### 2.5 Local polymorphic functions and externs

- A local `fun` that still takes type parameters is *not* copied per type.
  A local function that takes instance parameters is usually lifted and
  specialized by Lean itself (`main._elam_0._at_.main.spec_N`). Otherwise
  Stage 2's lambda lifting makes one declaration whose type parameters are
  erased, and its values of those types are `Box`es (§5.1). Copying it per
  application type in Stage 1 is a possible optimization.
- An extern with type parameters (`Array.push {α}`) gets a typed instance,
  e.g. `Array.push@Nat : Array Nat → Nat → Array Nat`, which is still an
  extern. Monomorphic externs keep their original names, so Lean's
  constant folding still recognizes them.

### 2.6 When a type is not statically known

Every program Lean compiles is translated (unless it reaches an extern
that neither the runtime implements nor Lean code can replace, §5.8 and
§10). Where a static type is
unavailable, the uniform `Box` representation (§5.1) takes its place:
- **A type argument that is not fully known.** The instance is built at
  `lcAny` (§2.3).
- **Polymorphic recursion.** Nested datatypes, or a function calling itself
  at a growing type such as `α`, `List α`, `List (List α)`, … would need
  infinitely many instances. This is detected when an instance of `d` is
  requested at type arguments that strictly contain those of an instance of
  `d` on the path of instances that led to the request (a type function
  such as `StateT Nat m` counts as growth when it is larger): that request
  goes to the fully uniform instance (every type argument `lcAny`, static
  dictionaries dropped). The path covers growth through other declarations
  of the cycle, a `where` helper (`nestI` → `nestI.helper` → `nestI` at
  `StateT Nat m`) or a mutual partner. It stops at the nearest uniform
  instance of `d`, whose own recursive request at a type built from its
  `lcAny` (`List lcAny`, `lcAny × lcAny`) goes to the uniform instance as
  well: a typed instance there could not hold a value only `unsafeCast` to
  that type (natively any object). Growth through a type function (`m` →
  `OptionT m`) gets one typed instance at `F lcAny`, which adapts the
  dictionary the uniform instance passes, and whose request at
  `F (F lcAny)` goes back to the uniform one. Growth that no path shows is cut by bounds: a type
  argument deeper than 64 or larger than 256 nodes becomes `lcAny`, and
  past 1024 instances of one declaration every further instance is the
  uniform one. So the set of instances stays finite. This is
  necessary: Reussir's own monomorphizer cannot handle polymorphic
  recursion. Only code has instances: a datatype has one type whatever its
  arguments (§5.1), so a caller of a uniform instance passes its values as
  they are, boxing or unboxing only values of the instance's `lcAny` types
  (an array too: `Array α` is one array of boxes, §5.1).
- **Existential values.** A structure with a `Type`-valued field stores its
  payload boxed, and functions over the payload take `Box`.
- **Dynamic polymorphic dictionaries** (§2.4).

### 2.7 Library code that relies on the uniform representation

A few library functions are `implemented_by` unsafe code that is only
correct because every Lean value is an object pointer:
- `Array.mapMUnsafe` (behind `Array.map`/`mapM`) and `mapFinIdxMUnsafe`
  reinterpret an `Array α` as an `Array NonScalar`, replace its elements one
  by one with values of type `β`, and cast the result to `Array β`;
- `Array.modifyMUnsafe` (behind `Array.modify`) stores `unsafeCast ()`, that
  is `box(0)`, into the slot being updated, so that the element stays
  unshared while the update function runs.

These functions are `@[inline]`/`@[specialize]`, so their code is already
inlined into the persisted LCNF of user code. lean2rr translates it as is,
giving it the representation it assumes:
- `NonScalar` and `PNonScalar` (types that stand for "any object") become
  `lcAny`, so values of those types are `Box`es. An array of a type
  without a storage kind has one representation (`RVec<Box>`, §5.1), so
  the casts between `Array α` and `Array NonScalar` change nothing: the
  `map` loop runs on the array in place, reading each `Box`, unboxing it to
  the function's argument type and boxing the result back into the slot,
  as natively. Stage 3 (§4) recovers the precise types around this code.
  With compact arrays (an `Array S` of a scalar `S` is `RVec<k>` of its
  storage kind, optimization `compact-arrays`), Stage 3 gives a `map` loop
  that reads or writes such elements a typed instance: in place when the
  element type does not change, else a loop that reads the source and
  pushes onto a new array of the result's kind
  (`docs/implementation/representations/compact-arrays.md`).
- A `box(0)` placeholder is a value that is never inspected. It arrives as
  a unit-like value used at another type, or as `◾` at a relevant type.
  Stage 4 materializes it as the *zero* of the expected type: `0`, `false`,
  a constructor without fields, else the first constructor whose fields
  have zeros, a function value returning a zero (the nullary `z` variant,
  §5.3), an empty array, a reference or a `done` thunk or task cell
  holding a zero (a `pending` cell that is never forced when the value has
  none: `structure S where h : Nat; t : Thunk S`). For `Nat`, `Bool` and
  enumerations this is exactly what `box(0)` denotes in Lean. The zeros are
  found depth first; a type whose zero is being built is not used for a
  field (which keeps zeros finite), and a constructor whose field turns out
  to have no zero is passed over for the next one: `inductive Term | app (p
  : Term × Term) | var (n : Nat)` gets `var 0` (`app` would need `Term ×
  Term`, whose zero needs `Term`'s), `W | bad (e : Empty) | ok (n : Nat)`
  gets `ok 0` (test `RtZeroFinite`). Only a type without a finite value
  (`Empty`, a type each of whose constructors needs itself) gets
  `unreachable`, which is never evaluated where a value of the type
  exists. A zero that would
  allocate (a string, an array, a record, a reference, a boxed unit) is
  built once and kept in a once-cell, like a constant (§5.12), but not
  walked for tasks as a constant is (natively it is `box(0)`, never marked
  persistent): `modify` stores one per update, and since a placeholder is never
  inspected, a shared value serves as well as a fresh one (optional pass
  `placeholder-cache`; without it each placeholder is built where it is
  used). A placeholder that is put in a box is `box(0)` itself (the word
  1), not its type's zero boxed: `modify` on an `Array Float` stored a
  new `Float` cell per update for it (adversarial finding 2). `box(0)`
  reads back as the type's zero at every type.

This keeps Lean's in-place update tricks, including `modify`'s unshared
element. An alternative, redirecting to the safe reference implementations
and recompiling tainted callers from source, exists behind an option; it is
off, because it loses Lean's inlining and specialization in those callers.

---

## 3. Stage 2 — Lean's mono pipeline (Lean's passes, driven by us)

We run Lean's own passes on the closed monomorphic program, in Lean's order.
Groups of mutually recursive declarations go bottom-up, callees first. Each
declaration is saved to the local extension so later passes can inline it,
and Lean's checker runs after every pass. This stage involves no new
translation logic; its job is to leave the code in the shape Stage 4
expects.

The environment is imported with the extensions' imported state loaded.
Without it every extension keeps its initial state, and queries the passes
depend on, such as "is this a class" for dictionary folding, silently answer
no.

**Two passes are lean2rr's copies.** Lean's `toMono` erases every
type-former argument of an inductive to `lcAny`: `Std.HashMap Nat Nat` is
`DHashMap Nat (fun _ => Nat)`, and mono makes its buckets
`AssocList Nat lcAny`, boxing every value. lean2rr runs copies of `toMono`
and `structProjCases` (the other pass that converts types) whose type
conversion keeps a closed, non-dependent type-former argument: a constant
family `fun _ => T` (its body does not mention the bound variable) or a
type constructor. A family whose body mentions its variable (`fun b => cond
b Nat String`) stays `lcAny`, as its values need not have a single
representation. The rule is syntactic, after eta reduction: `fun n => Fin
n` is the type constructor `Fin`, kept (a field type `Fin k` that applies
it converts to `Nat`). A value index is no obstacle: in Lean's base code
`Fin (n + 1)` is already `Fin lcAny`, so `fun n => Fin (n + 1)` is a
constant family and is kept too (`(n : Nat) × Fin (n + 1)` is stored as a
pair of `Nat`s). Every mono type lean2rr
computes itself uses the same conversion.

**`toMono`: semantic lowering done by Lean.**
- `Decidable` → `Bool`.
- `Nat` constructors and `cases` → `Nat.add x 1`, and `if n == 0 … else
  let m := n - 1`.
- `Int` `cases` → a sign test plus `natAbs`.
- `cases` on builtin runtime types (`Array`, `String`, `ByteArray`,
  `Float`, `Thunk`, `Task`, `UIntN`) → accessor externs. (lean2rr's copy
  binds the field of an `Array`, `ByteArray` or `FloatArray` at its own
  type, not `lcAny`; §4 sends `Array.toList` to the instance at the
  element type.)
- Single-field structures are unwrapped: `Char`→`UInt32`, `Fin n`→`Nat`,
  `Subtype`→its value, `Int8`→`UInt8`, `String.Pos.Raw`→`Nat`.
- `Quot` is unwrapped.
- Type arguments become `◾`.

Because Lean does all of this, the representation types in Stage 4 are
exactly the ones Lean's runtime and `lean.h` externs assume.

**Mono optimizations, one line each:**
- `simp`: inlining, constant folding, dead code;
- `reduceJpArity`: drop unused join-point parameters;
- `structProjCases`: projections become single-arm `cases`;
- `extendJoinPointContext`: join points receive the outer variables they
  use as explicit parameters;
- `floatLetIn`: move `let`s into the branch that uses them;
- `reduceArity`: drop unused parameters (`f._redArg`);
- `commonJoinPointArgs`: drop join-point parameters that get the same
  argument at every jump;
- `lambdaLifting`: every local function becomes a top-level declaration
  `f._lam_N` over its free variables;
- `elimDeadBranches`: remove impossible branches;
- `cse`: common subexpressions;
- `extractClosed`: closed subterms become lazily evaluated constants
  `f._closed_N`. lean2rr runs it last, over all declarations, as Lean ran
  it (`extractLikeLean`, Pipeline.lean). Lean extracts a module's closed
  terms in compilation order with a cache of the terms the module made so
  far: a declaration with a term equal to an earlier one's reads the
  earlier one's, so the earlier one decides how the shared terms evaluate
  (Lean evaluates a constructor's closed fields in reverse order), and the
  later one, making no term of its own, keeps the values the extraction
  left dead (a call there still runs). `set_option compiler.extract_closed
  false` turns extraction off for a declaration or a module. The record
  says what Lean did: each module's IR-only declarations list the closed
  terms `d._closed_N` each declaration made, in the order Lean made them,
  and the IR bodies (in the `.olean`, or in the `.ir` file of a `module`
  file) say which closed terms each declaration reads. So lean2rr extracts
  the declarations that made closed terms first, in Lean's order, with
  one cache per module, then those whose IR reads closed terms, and leaves
  the others as they are (Lean extracted nothing from them: nothing was
  closed, or extraction was off), instances of polymorphic declarations
  included (Lean computes at each call what an instance's known types or
  dictionaries make closed). Only a declaration Lean compiled to no IR
  (lean2rr translates the reference definition of an `@[extern]` or
  `@[implemented_by]` declaration) is extracted as usual. lean2rr's copy of
  the pass (`ExtractClosedK`) checks a callee's attributes and kernel type
  on the declaration of Lean's compilation the instance was made from, so
  `@[never_extract]` functions are not extracted and, as natively, a call
  of a function whose type is not syntactically a function type
  (`def F := Nat → Nat`) is not extracted on its own.

**Output shape.** Top-level declarations only; there are no local functions
left. Closures are partial applications of top-level declarations. Join
points are explicit, mostly closed over their inputs. `cases` appear on
`Bool`, enum-like types, and inductives. Every binder carries its mono type.
Example (a real mono dump, abridged):

```
def loop (a.1 : List (Prod Nat P)) (a.2 : List Float) : List Float :=
  cases a.1
  | List.nil => let r := List.reverse@Float a.2; return r
  | List.cons (head : Prod Nat P) (tail : List (Prod Nat P)) =>
    jp _jp.6 (_y.7 : Float) : List Float :=
      let _x.8 := List.cons ◾ _y.7 a.2;
      let _x.9 := loop tail _x.8;
      return _x.9;
    cases head
    | Prod.mk (fst : Nat) (snd : P) =>
      let _x.13 := Nat.decLt 3 fst;
      cases _x.13
      | Bool.false => let z := Float.ofScientific 0 true 1; goto _jp.6 z
      | Bool.true  => cases snd
                      | P.mk (a : UInt8) (b : Nat) (c : Float) =>
                        let f := UInt8.toFloat a; let s := Float.add c f; goto _jp.6 s
```

---

## 4. Stage 3 — check and recover lost types

Mono can still lose type information in two ways:
- Types inferred *during* the passes go through erased signatures. A
  constructor's mono signature is `List.cons : lcAny → List lcAny → …`, so
  `structProjCases` can type the fields of an exactly typed pair `lcAny`, and
  lambda lifting can give a lifted lambda the result type `lcAny`.
- The library code of §2.7 casts with `unsafeCast`, which LCNF erases. The
  result of `xs.map f` is bound at `Array NonScalar`, i.e. `Array lcAny`.

A binder typed `lcAny` uses the uniform `Box` representation (§5.1), and each
use at a precise type unboxes it. Data types have one representation
whatever their type arguments (§5.1), so `List lcAny` and `List Nat`, or
`Array lcAny` and `Array Nat`, are one type: Stage 3 does not choose
layouts. It types locals, so that `pick Nat`'s `x` is a `Nat` and a field
is read at its own type (§5.5), recovering the exact type wherever the
program determines it. It iterates over the whole program until nothing
changes.

A binder's type is recovered from what flows *into* it, never from how it
is used. A use at a precise type only speaks for its own branch. With a type
that depends on a value, `data : Array t.denote` is used as `Array Nat` only
in the branch where `t = .nat`. An unboxing moved from that use to the
binder would also run, and fail, when `t = .str`. The rules:
- **From definitions.** A `cases` field gets the constructor's field type,
  instantiated at the discriminant's type, when that type is the
  constructor's inductive applied to its parameters. A discriminant of type
  `lcAny` (a value of a type that depends on a value, `d : s.Data`, or an
  existential payload after `cast`) leaves its fields as they are: the
  instantiation needs the parameters (the parameters' own types are not
  the fields', round 7 RV7F-01). A constructor application gets
  the type its argument types determine. Parameters that no field
  determines, such as the error type of `EST.Out.ok`, come from the binder's
  own type. A call, full or partial, gets the type the callee's signature
  gives. A join-point parameter gets the type of its jump arguments when all
  of them are known and agree. No rule gives a binder the type `◾`: mono
  already types types and proofs `◾`, so an `lcAny` binder holds a value
  (test `RtDepFields`).
- **Result types.** A declaration whose result type is unknown gets `T` when
  all its returned values have type `T`. The results of its own self calls
  do not count, and neither do constructors without fields (`none`) of `T`'s
  inductive. It also gets `T` when every call of it binds the result at `T`,
  provided it is used nowhere else, e.g. not as a closure. The callers would
  unbox right away anyway; the unboxing moves to the callee's `return`,
  which for a constant happens once instead of at every read. A self call
  counts as a call here too, except a tail call (`let y := f …; return y`)
  at the declaration's own result type, whose value is the result. Other
  self calls can return a value of another type than the one typed caller
  binds the result at: polymorphic recursion into the uniform instance
  (`FSeq.flatten` at `lcAny` calls itself at `lcAny × lcAny`), which returns
  a value of a different type at every depth (adv2 PrgPoly1, runtime test
  RtPolyRecResult), or a call at a type computed from a value, which the
  binder types `lcAny`, the declaration's own result type (hunt MONO-01,
  runtime test RtSelfCallResult).
- **Externs at unknown types.** A call of a polymorphic extern instantiated
  at `lcAny`, e.g. `Array.uget` and `Array.uset` at `NonScalar`, binds its
  result at the type the extern returns at the type arguments the
  arguments determine. Every argument must then have exactly the expected
  type, or be a `◾` placeholder. The call keeps its callee: an extern does
  not depend on its type arguments, and with one representation per
  datatype only the result binder's type changes. The call
  `Array.toList ◾ a` by the extern's own name, which `toMono` makes after
  Stage 1 for a `match` on an array, goes to the instance at the element
  type: with compact arrays its declared `Array lcAny` would be a crossing
  (hunt HARR2-01). (`Thunk.get ◾ t` and `Task.get ◾ t` stay: at their
  instance a `Float` would be unboxed at the call and boxed again at each
  boxed use.)
- **Placeholders.** A placeholder `let z := ◾` gets the type its uses
  expect when they agree: it has no value to convert.

For `xs.map (· * 2)` the loop of §2.7 runs on the one array type
(`RVec<Box>`), in place: it reads a `Box`, unboxes it to the `Nat` the
function takes, and boxes the result into the same slot, as natively (where
the slot is a `lean_object*`). No loop is split and no array converted. (A
container whose element type depends on a value, a column `data : Array
ty.denote`, is also an `Array lcAny`: updating it at a precise type boxes
one element; before arrays had one representation, it converted the whole
array there and back at every update, review RV9C-02, and needed passes of
its own.)

Each rule is exact. A value's type is taken only from its definition or from
everything that flows into it, so the recovered type is the type the value
has on every path. Where the program does not determine the type, the
binder keeps `lcAny` and uses `Box`, unboxed where it meets a precise type.

Stage 4 relies on structural facts of Stage 2's output:
- join points are not recursive, and jumps are in tail position;
- no local functions remain;
- every `cases` covers all constructors or has a default.
Stage 3 does not check them. Lean's LCNF checker runs after every Stage 2
pass (§3), and Stage 4 copes where a fact fails: a `cases` that misses
constructors gets an `unreachable` arm (§5.5), a local function left over
is lowered as a closure, and a jump to an unknown join point is an internal
error of lean2rr.

---

## 5. Stage 4 — lowering to Reussir

### 5.1 Type translation

Stage 4 sees only mono types:
- applications `C a₁…aₙ` of inductive and builtin types;
- function types `A → B`;
- `◾` (erased), `lcVoid` (the IO world);
- `lcAny`: either a phantom position (ignored), or a data position whose type
  is not statically known (represented by `Box`, below).

**Builtin types.** Native Reussir types wherever they exist:

| Lean (mono) | Reussir | Note |
|---|---|---|
| `UInt8/16/32/64`, `USize` | `u8/u16/u32/u64`, `u64` | `Char` arrives as `UInt32`, `Int8`… as `UInt8`… (unwrapped by Lean); signed operations are externs on the bit pattern, as in `lean.h`. 64-bit targets only. |
| `Float`, `Float32` | `f64`, `f32` | |
| `Bool` | `bool` | |
| `Unit`/`PUnit`, `lcVoid`, `◾` | `L2RUnit` | Reussir's `unit` is result-only, so unit-like values are a one-variant `[value]` enum from the prelude. The IO world is an `L2RUnit` value. |
| `Nat` | `Nat`, a *tagged* opaque handle: one word, `2n+1` for n < 2^63, else a pointer to a counted runtime bignum (GMP) | as natively; see "One-word `Nat` and `Int`" below |
| `Int` | `Int`, the same with small values in the `int32` range (`lean_box((unsigned)(int)i)`) | |
| `String` | `LStr`, an opaque copy-on-write handle to one block like Lean's string object: a 32-byte header (count, byte size, capacity, character count) and the UTF-8 bytes | literals: §5.4 |
| `Array α` | `RVec<Box>`, the runtime's copy-on-write vector: one block, a 24-byte header (count, size, capacity) and the elements | in place when unique. One representation for every `α` without a storage kind: an element goes in by boxing and comes out by unboxing (natively one `lean_object*` per element) |
| `Array S`, `S` a scalar | `RVec<u8>` (`UInt8`, `Bool`, an enumeration of at most 256 constructors), `RVec<u16>`, `RVec<u32>` (`UInt32`, `Char`), `RVec<u64>` (`UInt64`, `USize`), `RVec<f32>`, `RVec<f64>` (`Float`) | optimization `compact-arrays`: per storage kind, when a whole-program check finds that no array of the kind meets an array of boxes; otherwise `RVec<Box>` (`docs/implementation/representations/compact-arrays.md`) |
| `ByteArray`, `FloatArray` | `RVec<u8>`, `RVec<f64>` | `ByteArray.mk`/`data` (and `FloatArray`'s) are the identity with a compact `Array UInt8` (`Array Float`); with an array of `Box`es they convert in one loop at the exact size, as natively they copy |
| `ST.Ref σ α` | one generated shared record `L2RRefN(Cell<Box>)` (N a counter) around Reussir's mutable cell, whatever `α` is | a value is boxed when stored and unboxed when read at a precise type. Mono types a reference `lcAny`: it travels in a `Box`, and an operation unboxes it (one variant) |
| `Thunk α`, `Task α` | `LCell<S>`, a shared mutable runtime cell holding a generated state `S { pending(L2RUnit -> Box), busy, done(Box), … }`, one for thunks and one for tasks, whatever `α` is | memoized thunks, deferred tasks (§5.14) |
| `Option α`, `Except ε α`, `EST.Out ε σ α`, … | generated types (next paragraph) | |

**One-word `Nat` and `Int`.** A `Nat` is one machine word, with Lean's
own encoding: an odd word `lean_box(n) = 2n+1` is the small value `n`
(n < 2^63, `LEAN_MAX_SMALL_NAT`), an even word is a pointer to a
reference-counted big number (n ≥ 2^63, `leanrt::nat`). Every value has
exactly one form, so two small words are equal exactly when their values
are, and every small value is below every big one. An `Int` is the same,
also in Lean's encoding: a value `i` in the `int32` range is
`lean_box((unsigned)(int)i)` (its 32 bits, zero-extended, so a `Nat` below
2^31 and the `Int` of the same value have the same word), any other value
a big number. A big number is lean2rr's own: one block holding the 32-bit
count Reussir counts, 4 reserved bytes, the signed size (GMP's convention:
the limbs in use, negated for a negative `Int`), the capacity, and then
the limbs. Its operations are GMP's: `mpn` functions on the limbs, writing
into an operand's block when it is unique and has room (a carry out of a
result computed in place grows the block; a result that leaves most of a
block unused shrinks it) or into a fresh block, and `mpz` functions on
read-only views for the rare ones (`pow`, `gcd`, parsing, printing). Native Lean's
`lean_mpz_object` is a header and an `mpz_t` whose limbs GMP allocates
separately: one block saves an allocation, a free and a dependent load
per big number, and a two-limb number takes 32 bytes instead of 56. The
small words are exactly Lean's, so C code written against `lean.h` could
receive and return them unchanged; a big number would be converted at
that boundary (calling a program's own C code is not supported for now,
§10).

The difficulty is that Reussir, not lean2rr, inserts the reference
counting: copying a handle increments the count at its address, dropping
it calls the type's drop code. A small `Nat` has no address. Three ways
were weighed (2026-10):

1. *An opaque runtime type with user hooks.* Reussir's opaque `#[ffi]`
   records (`LStr`, `RVec`) already call a Rust drop hook on release, but
   increment the count inline, at the address. A clone hook would need a
   new symbol per type and a call on every copy (or reliance on LLVM
   inlining it).
2. *A small Reussir feature: tagged opaque handles.* The opaque record is
   declared `#[ffi(rust = "::leanrt::nat::LNat", tagged)]`; Reussir then
   increments the count only when the handle's low bit is clear, and calls
   the drop hook only then (the hook is Rust's `Drop` of `LNat`, which
   frees the big number). Real handles point to a 4-byte-aligned count, so
   the low bit is free. Nothing else in Reussir reads through an opaque
   handle (opaque values never donate their cells for reuse, are never
   deferred by the drop glue, and are only passed to Rust code, which knows
   the encoding). The patch (Reussir patch 41-a) carries the flag from the
   attribute to the type (`!reussir.ffi_object<…, tagged = true>`) and adds
   the two guards in the LLVM lowering of `rc.inc`/`rc.dec`.
3. *lean2rr alone.* Reussir's only immediates are field-less constructors,
   encoded as pointers to per-tag dummy cells, not arbitrary numbers. A
   `u64` field would escape Reussir's counting altogether: lean2rr would
   have to insert every increment and decrement of `Nat` values itself,
   including inside the drop code Reussir generates for records, closures
   and enums that hold them, which it cannot reach.

Option 2 was chosen: it is the smallest change (one flag, two guarded
lowerings), keeps Reussir's counting and in-place reuse for everything
else, and gives exactly Lean's representation, with the copy of a small
value costing one bit test and no call. Option 1 is the same mechanism
with a call where the bit test suffices; option 3 is not possible.

`Nat` and `Int` are then ordinary handles to lean2rr: they cross the FFI
boundary, and records, constructors, closures and `Box` hold them as one
word. The
prelude's functions work on the words: `l2r_nat_raw(n)` turns a `Nat`
into its word, which then owns the handle's reference, and each function
does that once per argument, so the small path has no reference counting
at all:

```
fn lean_nat_add(a : Nat, b : Nat) -> Nat {
    let x = l2r_nat_raw(a);                 // 2m+1, or a big number's pointer
    let y = l2r_nat_raw(b);
    let s = x + (y - 1);                    // 2(m+n)+1 when both are small
    if (s & x & 1) == 1 {                   // both small (s odd: same parity)
        if s >= x { l2r_nat_of_raw(s) } else { l2r_nat_add_raw(x, y) }   // no carry: small
    } else { l2r_nat_add_raw(x, y) }        // leanrt::nat, GMP; consumes both words
}
```

The rule for words: a small word owns nothing; a big word must reach
exactly one owner on every path (back into a handle, a `_raw` slow path,
which consumes its words, or `l2r_nat_drop_raw`). The slow paths take
every combination of small and big words and return normalized handles.

A type with computed fields (`Lean.Name`) is represented by its
implementation inductive `T._impl`, whose constructors also store the
computed fields. Lean's runtime does the same, and mono code uses both names
for the same values.

**`◾` (erased)** values have the unit representation. Erased parameters are
removed, except a function's last parameter, which stays one unit parameter
for its trailing erased ones and receives `L2RUnit::u{}` (§5.2, rule 4). An
erased domain of a function type is a unit domain where some function value
of the program runs its body right after it, otherwise a *phantom* domain
with no parameter at run time (§5.3). Erased constructor fields have no
representation. Where `◾` or a unit-like value is used at a *relevant*
type, it is Lean's `box(0)` placeholder (§2.7) and becomes the zero of
that type.

**Other inductives** become one Reussir type each, whatever their type
arguments (rule 1 of the layouts of generic types: types do not compute,
values do), mirroring the Lean declaration: same constructors, same field
order, fields typed by translating their declared types with every
parameter of the inductive `lcAny`. A field of a parameter's type is a
`Box`; `List α` in a field is the one `List` type; `α → β` is the function
type `Box → Box`; a concrete field keeps its type. `Tree Nat` and `Tree α`
are one type, as natively, where a field of unknown type is one
`lean_object*`. The shape follows the constructors:

```
inductive Ordering | lt | eq | gt          ↦  enum [value] Ordering { lt, eq, gt }        -- no fields: unboxed
inductive Tree α | leaf | node (l) (k : α) (r)
                                           ↦  enum Tree { leaf, node(Tree, Box, Tree) }
structure P where a : UInt8; b : Nat; c : Float
                                           ↦  struct P { a : u8, b : Nat, c : f64 }
Prod Nat P                                 ↦  struct Prod { fst : Box, snd : Box }
List (Prod Nat P)                          ↦  enum List { nil, cons(Box, List) }
```

Typed code keeps precise types for its own values: Stage 1 makes an
instance of each function per type argument and Stage 3 types parameters,
results and locals, so `pick Nat`'s `x` is a `Nat`. A value goes into a
field of a parameter's type by boxing and comes out by unboxing, O(1);
`cases` unboxes a field once, at the binder's type (§5.5). A value is never
rebuilt to change its layout: with one type per instantiation, a value
crossing into uniform code was rebuilt node by node, without memory of
the nodes already rebuilt, so a tree whose nodes share their children
took exponential time and memory (`build n` with `.node t t`: 927 MB at
n = 24, native 7.9 MB). A field of a parameter's type is a `Box` also
where the parameter is a proof or a type: it holds `box(0)`, as natively.

- **Shapes.** No relevant fields anywhere (proofs and erased fields do not
  count) means a `[value]` enum (no allocation). One constructor means a
  `struct`. Anything else is an `enum`.
- **Allocation.** Non-enum types are heap-allocated and reference-counted
  (`[shared]`), like Lean's. A structure with a single relevant field
  (`ST.Out`, the result of every `BaseIO` call, once the world is gone) is
  a `[value]` struct instead, as natively Lean represents it by its field,
  unless that field's type is being translated at the same time (no type
  contains itself by value). (Optional pass `value-structs`; without it
  such a structure is a shared record like the others.)
- **Field order.** lean2rr orders each constructor's fields by decreasing
  alignment (ties in declaration order), so records have no padding; the
  layout maps each Lean field to its record position, and constructions,
  patterns and projections go through it. (Reussir's own member packing is
  off: its in-place reuse of a cell for another variant mishandles fields
  that packing moves.) This is the optional pass `field-order`; without it
  the fields stay in declaration order, and Reussir lays the padding out as
  bytes.
- **Recursion.** Recursive, mutual and nested inductives refer to each
  other's types; `inductive Rose | node : List Rose → Rose` gives `Rose`
  and the one `List`, whose head is a `Box`; `inductive Tree | node (v :
  Nat) (cs : Array Tree)` holds the one array type, `RVec<Box>`.
- **Polymorphic recursion in a type.** Since Lean 4.34 an inductive can use
  itself at a larger argument only as an *index*: `unsafe inductive Nest :
  Type → Type 1 | nil {α} : Nest α | cons {α} (x : α) (rest : Nest (α × α)) :
  Nest α`. Lean's mono phase erases indices, and an inductive has one type,
  so `Nest` is one type whose `x` is a `Box`: nothing to cut (test
  `RtNestGrowType`). (Lean 4.33 also accepted a growing *parameter* in an
  `unsafe inductive`; with one type per inductive it would be one type
  too.)

**Function types** become generated shared enums, one per (lowered,
curried) function type, whose variants say what a value is a partial
application of (§5.3). They are not Reussir closures.

**The uniform type `Box`.** When a data position has type `lcAny` (§2.6, §4),
its value is stored as `Box`.
- `Box` is one word, as Lean's `lean_object*` (the prelude's `LAny`,
  `leanrt::any`): an odd word is an immediate (a scalar, an enumeration's
  index, a nullary constructor by index, a small `Nat` or `Int`, unit =
  `box(0)`); an even word owns a counted object, its address in the low
  48 bits and the number of its payload type in the top 16 (leanrt's kinds
  1 to 15, the program's from 16). Payload types are numbered as Stage 4
  boxes values; the program's releases of its payload types
  (`l2r_any_rel_<n>`, installed in leanrt's table by number) and the
  unboxing functions are generated at the end, once every payload
  type is known. With the optional pass `conv-liveness` (on by default,
  §5.3), an unboxing function is generated only once live code calls it,
  with arms only for the payloads that live code builds.
- Converting a precise type `T` to `Box` boxes the value at `T`'s payload
  number (an immediate, or the pointer; a value that is not one counted
  pointer goes into a cell first). Unboxing to a nominal type `T`, an
  array, a thunk or a task, a reference, a string or a word type accepts
  `T`'s own payload only (one type per inductive, one per builtin generic
  type), and `box(0)` as `T`'s zero, in line. Unboxing to a function type
  must accept every payload that can hold a value of the same Lean type,
  because a function type has several Reussir representations (`Nat →
  Nat` and `Box → Box`): it is a generated function that dispatches on the
  payload number and wraps them.
  When the program can cast at all, unboxing also accepts the variants of
  types that an `unsafeCast` can read (below). A program can cast when
  some declaration it reaches outside Lean's library (`Init`, `Std`,
  `Lean`, `Lake`) and lean2rr's shim (`L2RShim`, §5.8) is `unsafe`, is an
  axiom, uses `sorry`, or is an `@[export]` definition that lean2rr calls
  without comparing types (one under a C symbol of Lean's library or one
  that starts with `l2r_`): `unsafeCast` needs `unsafe` code, a `cast`
  between types lean2rr represents differently needs an equality that only
  `sorry` or an axiom proves, and an extern of Lean's library goes to the
  `@[export]` of its symbol unchecked. An axiom that Lean adds for a proof
  by native evaluation (`native_decide`, `bv_decide`: `e = true`, where
  Lean compiled the closed `Bool` term `e`, ran it and saw `true`) is no
  cast when the code that ran is the code of the definitions: no
  `implemented_by` target, extern, `initialize` constant (its value can
  differ between two modules' builds) or `@[csimp]` theorem of the program
  on its way (`nativeEvalStatement?`, `nativeExempt`; a `@[csimp]` theorem,
  or any constant stated `@f = @g`, only when its proof can be false: it
  uses `sorry`, an axiom that is not exempt, or kernel evaluation; and not
  when it comes after the axiom). It is then true of the definitions, so
  it proves nothing that the program could not prove without it. Every
  other axiom counts: `axiom bad : true = false` proves `Array UInt64 =
  Array Float`. So does kernel evaluation (`Lean.reduceBool`,
  `reduceNat`, `ofReduceBool`, `ofReduceNat`) when the walk reaches it, in
  a value or a type: the kernel runs the compiled code of the program's
  constant for it. Lean does not compare the types of
  an extern and the `@[export]` definition that implements it either:
  natively `@[extern "s"] opaque asP2 (p : Pkg) : P2` bound to `@[export
  s] def payload (p : Pkg) : p.α` reads an existential payload as a `P2`;
  but lean2rr binds an extern of the program to an `@[export]` only when
  their types and compiled signatures agree (it refuses that program, test
  `RtCastExtern`, §5.8), and otherwise runs the extern's Lean definition
  or nothing. So an extern of the program is no cast by itself: the walk
  below goes into its `implemented_by` target, the `@[export]` definitions
  of its C symbol and its own definition (test `RtCArrExtern`: compact
  arrays stay on with lean-zip-like externs). `implemented_by` is type-checked, but
  only by its declared type: a program declaration implemented by an
  `unsafe` function, even one of the library's, counts (`@[implemented_by
  TypeName.mk] opaque mkTN` gives two types the same `TypeName`, so
  `Dynamic.get?` reads one as the other). The code Lean (4.33, 4.34) generates for
  a `partial def` (`f._unsafe_rec`) is `partial`, not `unsafe`, so it does
  not make a program cast. Which modules are Lean's library is decided by
  their names; a program module named `Init.*`, `Std.*`, `Lean.*` or
  `Lake.*` that is not the toolchain's is rejected when the program is
  loaded (§10). The declarations
  reached are those the program's code comes from and, transitively, the
  constants their definitions mention (code inlined into others), their
  `implemented_by` targets, their `_unsafe_rec` copies (a `partial def`'s
  code; its value is only an inhabitant), and the `@[export]` definitions
  of an extern's C symbol (`LowerCtx.programCasts`); every `@[csimp]` replacement that is a
  declaration of the program is a root of the walk (also `local` and
  `scoped` ones, which are not in the state after import: every `@f = @g`
  statement of the program's modules counts), since the replaced constant
  may show only in compiled code (a library `@[macro_inline]` `ite`
  becomes `Decidable.casesOn`). Lean's library casts
  only where lean2rr's representations agree: `Array.mapMUnsafe`'s
  `NonScalar` elements are `Box`es, `modify`'s `unsafeCast ()` is a
  placeholder, `attach` adds a `Subtype` (which mono erases), and
  `Dynamic` reads a value at the type its `TypeName` names. Otherwise no
  unboxing function matches another inductive or another word type. In a
  program that casts, an existential payload, an `IO.Ref`'s contents or a
  value in polymorphically recursive code cast to another type converts
  like a typed value: another inductive with the same native layout
  (the value as it is when lean2rr's layouts agree too, otherwise
  converted constructor by constructor through the target's layout), a
  `[value]` struct as its field, `UInt64`/`Float` by their bits, and words:
  a word type (`Nat`, `Int`, `UInt8/16/32`, `Bool`, an enumeration, an
  inductive with a constructor without fields) reads any word, any
  constructor (natively the boxed scalar of its index, or an object whose
  address is read: see the words below) and, if it is only ever a boxed
  scalar, any other heap object. A cast whose conversion needs a function
  value at another representation converts through a wrapper (§5.3), like
  any other conversion, so whether a cast converts depends on the two
  types only. (Such a cast was once kept only when the wrapper existed
  already, to save code on monad transformer towers; whether it converted
  then depended on the order in which helpers were generated: review
  CLR-01, tests `RtCastFnWrapDead`, `RtCastFnWrapLive`,
  `RtCastFnWrapOrder`. The wrappers stay finite: one per pair of function
  types the program has.) One kind of cast is left out: between
  inductives that do not correspond constructor for constructor (another
  number of constructors), which typed code converts: every unboxing
  function would convert from every inductive sharing a constructor shape
  with its own (3 to 5 % more code). Such a cast panics (§10).
  A boxed unit unwraps to the zero of `T`: a unit used at another type is
  Lean's `box(0)` placeholder (§2.7). Any other variant is unreachable.
- Conversions are inserted wherever a value's Reussir type differs from
  the type expected where it is used: call arguments, return values,
  constructor fields, join-point arguments, closure arguments and results.
  This is the typed counterpart of Lean's own `explicitBoxing`, which
  converts between `obj` and unboxed scalars.
- An inductive applied to `lcAny` is the inductive's one type:
  `Free lcAny Nat` ↦ `Free`, whose fields of parameter types are `Box`es.
- A function value is boxed under the variant of its own type. Unboxing it
  to the same type gives the value back; unboxing it to another
  representation of the same Lean type (for example to `Box → Box`, for
  uniform code that applies it) wraps it once in a `w` variant (§5.3),
  which converts the arguments and the result at each application and
  calls the function exactly once. Converting a wrapped value converts the
  value inside from its own representation instead of wrapping again. So a
  function value that goes through uniform code and comes back is not
  wrapped at all (it is the same object), and one read at three
  representations in a loop (`Nat → Nat`, `Nat → Box`, `Box → Box`)
  stays one wrapper deep.
- A reference (`ST.Ref`) has one type, whose cell holds a `Box`; mono
  types every reference `lcAny`, so it travels boxed, and each operation
  unboxes it (one variant) and acts on its one cell: `set` boxes the
  value, `get` gives a `Box` (which the IO result's field holds as it is).
  `ST.Ref.ptrEq` compares the records' addresses.
- A partial application has the type of its target with the supplied
  arguments removed. Lambda lifting can give a lifted lambda the result type
  `lcAny` while its closure is used at `Nat × Int → Int`, or the reverse; the
  value is then converted to the binder's type as above, and the callee
  still runs only when the last argument arrives.
- A value is never rebuilt to change its layout: a datatype, an array, a
  thunk or task and a reference each have one type. The one rebuilt value
  is a cast's (below), between two inductives whose layouts differ: a new
  object, equal to the original and unshared. Natively there is one
  object; only identity (`ptrAddrUnsafe`, `ptrEq`) and sharing
  (`dbgTraceIfShared`) can tell the difference, and neither is preserved
  (§9).
- Through `unsafeCast` (mono erases it), a value can meet code expecting
  another type that Lean represents alike. The conversions follow Lean's
  representation:
  - *Another inductive* whose constructors read the value's fields: the
    same number of constructors, and each field of a target constructor
    at a native layout slot the source constructor has. Lean lays a
    constructor out as its object fields in declaration order, then its
    `usize` fields, then the other scalars by decreasing size (Lean's own
    `getCtorLayout`), so fields correspond by slot, not by declaration
    position: `S₁ {a : UInt8, b : Nat}` read as `S₂ {x : Nat, y : UInt8}`
    is `x = b`, `y = a`. Same-size scalars in the scalar area are
    reinterpreted: a `UInt64` field read as `Float` is its bits. The
    conversion goes constructor by constructor, as Lean's `cases` reads the
    value: by tag (past the target's last constructor, the last one, as
    Lean's `switch`), a constructor without fields of the target is
    selected whatever the source constructor at that tag holds; a source
    constructor without fields, or one with fewer fields, read as a target
    constructor with fields has no value (unreachable). Types that
    correspond constructor for constructor (`isomorphic`) convert wherever
    their representations meet; others whose constructors with fields read
    some of the source's (`Sum3 | a | b (x : Nat) | c (y : String)` read
    as `Option`) only where the program casts (`coerce`), so that
    asking whether two function types convert (§5.3) does not pair every
    inductive with every other.
  - *Words*: `Nat`, `Int`, `UInt8/16/32`, `Char`, `Bool`, enumerations and
    constructors without fields are boxed scalars natively, and convert as
    Lean's `lean_unbox` reads them: truncated to the target's width
    (`unsafeCast (300 : Nat) : UInt8` is 44, `Bool` is the low byte being
    nonzero), an index past an enumeration's last constructor selects the
    last one (Lean's `switch`), a small `Int` is its 32 bits (read as a
    `Nat`, `-5` is `2^32 - 5`), a word read as an `Int` is signed 32 bits.
    `Nat` and `Int` convert by value (natively the same object when big). An
    index selects the nullary constructor at that position (`0` is `[]` or
    `none`), and back. An object read as a word is natively its address
    shifted, different on every run: lean2rr gives a deterministic word
    with the properties every address has (nonzero, a multiple of 4, far
    above any index): `2^44 + 8i` for a constructor with fields of index
    `i` (constructors stay distinct), `2^44` for a string, an array, a
    closure, a thunk or a float cell; a big `Nat` or `Int` reads as the low
    bits of its value. A `USize` (here `u64`, shared with `UInt64`) reads a
    word as it is. These casts happen only where the program performs a
    cast (`castFallback`), never when lean2rr merely asks whether two
    representations convert (function values: every function type over a
    `String` would otherwise convert to the same one over a `Nat`). A word
    read as an object with fields is natively a number used as an address
    (a crash): unreachable.
  - A `[value]` struct is natively its field when Lean erases its
    inductive to the field (`ST.Out σ α`, whose other field is a
    `Void σ`). Lean does not erase an `unsafe` or a recursive inductive
    (`hasTrivialImpureStructure?`): such a `[value]` struct is natively a
    constructor object with one field, and converts constructor by
    constructor, as the inductives above (`unsafeCast (Except.error 5) : U`
    for `unsafe inductive U | mk : Nat → U` is `U.mk 5`).
  When the two Reussir types (two inductives' records; an array has one
  type) have the same layout (the same constructors with fields of the
  same layouts, position by position, coinductively) and the conversion
  would pair exactly those fields, the value is used as it is
  (`l2r_retype`, the same object
  reinterpreted): a user list read as another user list costs nothing and
  keeps its sharing (`structConv` otherwise rebuilds it, converting a
  recursive field by calling itself, so a deep value uses stack). Where no
  conversion exists at all, lean2rr warns and emits a run-time panic for
  that cast: the program is still translated.
- `Box` costs one word, as natively; boxing allocates only a cell for a
  `Float`, a `UInt64` from 2^63 (natively a cell too) or a value that is
  not one counted pointer (a multi-word `[value]` record). It appears in
  every field, array element, reference and thunk of a parameter's type,
  and on the paths of §2.6; a typed local never pays for it.

### 5.2 Declarations, calls, arities

A declaration becomes a Reussir function over its relevant parameters. The
key fact is the *arity*: the number of parameters Lean gave it *after* its
optimizations. Lean eta-expands and lifts lambdas, so arity is not the
number of arrows in the type. Arity decides when work happens:
- a call with exactly `arity` arguments runs the function;
- fewer arguments only build a partial application, and nothing runs;
- more arguments run the function, then apply the result to the rest.

We follow these arities exactly, and never invent our own. The reason is
concrete: the native build of

```lean
def mkAdder (n : Nat) : Nat → Nat := let k := dbgTrace s!"prefix {n}" fun _ => n * n; fun x => x + k
```

has arity 2, and prints `prefix 3` once per call of `mkAdder 3 x`. A
translation that treated `mkAdder` as arity 1 would print it once. Where
work runs is observable.

| Mono LCNF | Reussir |
|---|---|
| `let y := f a b` with `f` of arity 2 | `let y = f(a, b);` |
| `let h := f a` with `f` of arity 2 | `let h = F_B_C::p1_f{a};` (function value, §5.3) |
| `let y := f a b c` with `f` of arity 2 | `let t = f(a, b); let y = t(c);` |
| `let y := g a b` with `g` a function value | `let y = l2r_ap2_…(g, a, b);` (§5.3) |

**Erased parameters (rule 4).** The arity counts erased parameters (`◾`:
types, type arguments, proofs), but the Reussir function takes none of
them, except its last parameter: when that one is erased, the function
takes one `L2RUnit` for its trailing erased parameters. A call drops the
`◾` arguments of removed parameters and passes `()` for the trailing unit.
So the body still runs when Lean's last argument is applied: `f 3` of
`def f (x : Nat) (α : Type)` stays a partial application (`f(x, u)`), and
a function whose parameters are all erased stays a function. Join points
take no erased parameter. The IO world (`lcVoid`) and `Unit` are data.

| Mono LCNF | Reussir |
|---|---|
| `def f (x : Nat) (α : Type) (y : Nat) (β γ : Type)` | `fn f(x : Nat, y : Nat, u : L2RUnit)` |
| `let y := f a ◾ b ◾ ◾` | `let y = f(a, b, L2RUnit::u{});` |
| `let h := f a ◾` | `let h = …::p2_f{a};` (captures `a` only) |

### 5.3 Closures (function values)

After Stage 2, every closure is a partial application of a top-level
declaration; lambda lifting turned local functions into declarations over
their captured variables.

- **Representation.** A Lean function value of lowered, curried type
  `T = A₁ → … → Aₙ → R` is a value of a generated shared enum `L2RFn_…`
  with these variants:
  - `p<j>_<target>(c₁, …)`: a *target* (a declaration, an extern, a
    constructor, a standard-stream primitive) applied to its first `j`
    Lean arguments, capturing those it takes (not the erased ones, §5.2).
    When it captures none, the variant is nullary and costs no allocation;
  - `raw(A₁ -> …)`: a Reussir closure, for values built by glue code;
  - `w<S>(g)`: a value `g` of another representation `S` of the same Lean
    type (§5.1);
  - `z`: the `box(0)` placeholder (§2.7), a function that is never applied.
- **Creating a function value.** A partial application of a target of
  arity `k` to `j < k` arguments builds `p<j>_<target>(args)`: one
  allocation, like native `lean_alloc_closure`.
- **Applying a function value.** `g a₁ … aⱼ` calls a generated
  `l2r_ap<j>_T(g, a₁, …, aⱼ)` (at most the chain length at a time), which
  matches the variant. A target whose remaining arity is exactly `j` is
  called directly, and nothing is allocated. With fewer arguments than it
  needs, a new `p` value capturing them is built. With more, the target is
  called with as many as it takes, and its result is applied to the rest.
  This is exactly `lean_apply_n` (`apply.cpp`).
- **Why this is right.** A target runs exactly when its last argument
  arrives, which is Lean's runtime rule. The variant records the target's
  own arity, so different values of the same Lean type can have different
  arities (`mkAdder` versus a function that returns a closure after doing
  work).
- **Why not Reussir closures.** A Reussir closure is applied by writing the
  argument into its captured payload, so applying a *shared* closure copies
  it first: one allocation per call of any closure held in a data structure
  or used twice. Curried application also allocates an intermediate closure
  per argument. Both are gone here; the dispatch is a `match`, which LLVM
  can inline, and a known target is a direct call. In a prototype, 10⁸ calls
  of shared function values took 0.09 s this way and 0.55 s with Reussir
  closures.
- **Erased parameters.** Lean still passes erased parameters (a proof, a
  type) to closures, and they count toward the arity. A target takes none
  of them except its last parameter (§5.2); a `p<j>` variant counts Lean
  arguments, and captures the ones the target takes. The IO world is data.
- **Erased domains.** A function type keeps an erased domain as a unit
  domain only where some function value of the program runs its body
  right after it (`mkF n b : (α : Type) → β` at `β := List Nat → Nat`
  runs at the type); otherwise the domain is *phantom*: the RR type keeps
  it (Lean positions) but the run-time type has no parameter for it, so
  `{α : Type} → List α → Nat` filled with `List.length` and `fun xs => …`
  is `List_Box → Nat`. The decision is by the type from that domain on:
  the domain stays if it is the type's last domain, if a value completes
  at an erased domain of the same skeleton (erased, data or `lcAny`
  domains), or if a value that completes there can become a value of this
  type along the program's flow (use sites where a function value of one
  type is used at another, and `Box` positions, read from mono LCNF before
  the lowering). Application
  takes Lean arguments along the type (a phantom domain drops its `◾`);
  an application function drops a unit argument at a parameter its
  variant's target does not take; a wrapper knows the phantom domains of
  both types, so uniform code that applies a boxed value to `box(0)` for a
  type argument lines up with the value's own domains.
- **Constructors and externs** are targets like declarations. Constructors
  do no work, so their timing does not matter.
- **Prelude callbacks.** Runtime helpers that take a Reussir closure
  (`dbgTrace`, `timeit`, …) receive `|x| l2r_ap1_…(g, x)`. Glue that
  builds a function value from Reussir code uses the `raw` variant.

The enums and the application functions are generated at the end of
Stage 4, together with the `Box` unboxing functions, until no new variant or
application appears.

- **Only for live code** (optional pass `conv-liveness`, on by default).
  The helpers generated at the end (unboxing functions, application
  functions, conversions of function values) follow a type-based
  reachability, computed while
  they are generated (`Lower/Live`, `Finish.finishLive`). The roots are
  the identifiers of the raw text (the entry point, the startup chain, the
  trampolines the runtime calls) and of the prelude. A function reached is
  looked at: the functions it calls and the identifiers of its atoms are
  reached, and the variants of `Box` and of function-value enums it builds
  are *made*. A helper is generated once it is reached, with an arm for
  each made variant only (and `z`, `raw`, the boxed unit; a match left
  without some variants ends in an `unreachable` wildcard), and again when
  a variant it matches is made, until nothing changes. Then the functions
  not reached are dropped; the enums keep every variant. A removed arm
  matches a variant that no running code builds: no value of it exists,
  so the program computes the same results. The one other difference is at
  translation time: an extern that only a removed arm would call (a
  function value of it that no live code builds) is not reported as
  missing ([liveness.md](implementation/conversions/liveness.md)). Without
  the pass, every helper
  requested anywhere is generated with an arm for every variant
  registered anywhere: in a program that can cast (§5.1), each unboxing
  function then has a cast arm and a conversion for every variant of a
  compatible layout, and a program importing `Cslib.Init` with a
  one-line `main` has 226,219 functions (380 MB of `.rr`; 990,927 in
  1.44 GB before one layout per datatype); with the pass it has 28,300
  (29 MB).

- **Kept out of rrc's MLIR inliner.** The conversions between
  representations (`l2r_fconv_S_T`), the unboxing functions (`l2r_unbox_…`,
  to a nominal type, an array or a function type), the application
  functions of a type with `w<S>` variants, and the application
  functions of the function types of uniform code (types that mention
  `Box`) are marked `#[transform_anchor]`: Reussir keeps a transform anchor a function
  through its MLIR pipeline (its inliner skips it; there are no transform
  scripts), and LLVM, which runs after Reussir's passes, still inlines it
  where that pays. These functions call each other through the wrapper
  variants and through what a `Box` can hold, and polymorphic recursion
  through monad transformers makes hundreds of representations of a few
  Lean types: with these functions inlinable, rrc's build time and memory
  on such programs grew far faster than the programs (superlinearly; an
  8-line `StateT` tower used at `IO` did not build within 30 minutes or
  15 GB; Reussir issue 20, a cost, whose cause was found later). Out of
  line, a conversion, an unboxing, or the application of a wrapped value or of
  a value of uniform type costs a call (until LLVM inlines it); all are rare
  outside uniform code, and typed function values are unaffected.

### 5.4 `let`, `return`, literals

- `let x := v; k` becomes `let x = ⟦v⟧; ⟦k⟧`, and `return x` becomes `x`.
  Lean's passes have already removed dead `let`s. Lowering never drops a
  Lean `let`, never evaluates one twice on the same path, and never
  reorders them, because a `let` can run a function that panics. It does
  add bindings of its own: representation conversions, placeholders, and
  the bodies of duplicated join points (one copy per path).
- Literals:
  - `Nat` literals below 2^63 become `l2r_nat_small(k)` (the word
    `2k+1`); bigger ones are parsed by the runtime from their decimal
    digits, kept in the string literal table (`l2r_nat_of_decimal_lstr`,
    `natLiteral`). One flat call: a nested arithmetic expression per limb
    overflowed rrc's stack for literals of thousands of digits.
  - `UIntN` literals become typed Reussir literals.
  - String literals become `l2r_str_lit(id)`: a runtime function generated
    with the program, which builds the string from a table of Rust byte
    strings holding the literals' UTF-8 bytes. The bytes are written as
    escapes, so every string round-trips exactly.
  - Neither kind passes a Reussir `str` to the runtime: a `str` argument
    goes through a stack slot whose address escapes, and a function with
    such a slot never has its tail calls turned into loops by LLVM.

### 5.5 `cases`

| Mono LCNF | Reussir |
|---|---|
| `cases b : Bool \| false => e₁ \| true => e₂` | `if b { ⟦e₂⟧ } else { ⟦e₁⟧ }` |
| `cases t : Tree Nat \| leaf => e₁ \| node l k r => e₂` | `match t { Tree::leaf => ⟦e₁⟧, Tree::node(l, b, r) => let k = unbox(b); ⟦e₂⟧ }` |
| `cases p : P \| P.mk a b c => e` (single constructor) | `let a = p.0; let b = p.1; let c = p.2; ⟦e⟧`, positions from the alignment-sorted layout (§5.1) |
| alternatives missing a constructor, no default | extra arm `_ => unreachable` (Lean has proved it impossible) |

Erased fields get no binders. A field is bound at its parameter's own
type (from Stage 3): a `Box` field (a field of a parameter's type, §5.1)
read by a parameter of type `Nat` is unboxed once, right after the match,
not at each use; a parameter the code never uses is not converted. Where
the parameter goes back to a `Box` position (a rebuilt constructor's
field), its value is boxed again: passing the field's own box left the
unboxed value's release dead in that branch, and Reussir's token reuse
took it as the new node's donor instead of the matched cell (Reussir
issue 39, reussir-bugs/39-alias-release-donor.md).
Reussir syntax notes: match arms have no trailing comma after the last
arm, and there is no `else if` (use `else { if … }`).

**Cast values.** Mono erases `unsafeCast`, so a `cases` (or a projection)
can meet a value of another type that Lean represents alike. A value of an
inductive whose constructors the matched type's read (§5.1) is matched
through its own constructors, position by position, and each field is
bound from the source field at the same native layout slot, at its own
type (converted only where it is used), so the value is not converted as a
whole:

```
match (unsafeCast x : L2) with | .cons h _ => h | .nil => 0     -- x : L1
    ↦  match x { T_L1::cons(h, _) => h, T_L1::nil => 0 }
```

A word matched as an enumeration or as an inductive with nullary
constructors (and an enumeration matched as another one with a different
number of constructors, or as `Bool`) is converted first (§5.1). A value
in `Box` is unboxed to the inductive's type first, which in a program that
casts accepts values boxed from those other types too. Where no conversion
exists, lean2rr warns and the match panics when it runs.

An arm that returns the matched value (`simp` turns `node l k r` back
into `t`) returns that value itself, as natively: the same object, with its
sharing, so a lookup returning an existing node does not copy it.

The matched value then stays live across the match, and Reussir cannot
reuse its cell for what the other arms build. That is the error arm of
every `ExceptT`/`Option`/`EStateM` bind (`| .error _ => r`), so each bind's
success path would allocate its result and free the matched one. The
optional pass `fresh-rebuild` returns the constructor rebuilt from the
arm's fields instead, an equal value (only identity and sharing, which
are not preserved, §9, can tell them apart), where no copy is likely:
when the matched value is freshly built (bound in the same function to a
constructor application, or to a full call of a declaration all of whose
results are freshly built, which an analysis of the whole program
decides: a bind's result, normally unique, so Reussir reuses its cell and
the rebuilt value is the same cell), and the arm binds every field and
uses the value only by returning it. A parameter, a field, a constant, or the result of a lookup, an
extern or a function value is still returned itself. MonadicInterp: 1.25x
native without the pass, 1.08x with it.

Two shapes help Reussir's token reuse, which gives a cell freed by a match
to a later construction (the optional passes `nullary-scrutinee`,
`lazy-fields` and `sink-proj`; without them the matched value itself is
used and every field is bound at the match):
- In the arm of a constructor without fields, the matched value is that
  constructor (`leaf{}`), which costs nothing to build.
- In an arm where the matched value stays live because it is stored whole
  in a new constructor, returned whole (`simp` turns `t@(node l k r)`
  rebuilt into `t`: a BST insert of a key already present) or passed whole
  to a call (merge's `go l₁ ys (y :: acc)`), the match binds
  only the fields used while the value is live; an inner alternative that
  no longer uses the value matches it again and binds the fields it uses
  there. `balance` keeps the recursive result `x` when no rotation is needed
  and takes it apart otherwise:

  ```
  match x {
      T::node(xs, _, _, _, _) => {        // x stays live: only its size
          if 3 * ss < xs {
              match x {                   // x dies here, this match frees it
                  T::node(_, xk, xv, xl, xr) => ⟦rotations⟧,
                  _ => l2r_unreachable()
              }
          } else { T::node{1 + xs + ss, k, v, x, r} }
      }, …
  ```

  An insert returning the node for an equal key binds only the key, which
  the comparisons need, and matches again in the arms that rebuild:

  ```
  match t {
      T::node(_, k2, _) => {              // t stays live: only its key
          if lean_nat_dec_lt(k, k2) {
              match t { T::node(l, k3, r) => T::node{ins(l, k), k3, r}, … }
          } else { if lean_nat_dec_lt(k2, k) { … } else { t } }
      }, …
  ```

  Reussir projects every bound field at the match. A field of a value that
  stays live then gets an extra reference, released where the field dies,
  and token reuse takes that release for a freed cell, which it never is,
  instead of the cell actually freed: `TreeMap.insert` rebuilt every node
  of the path, and so did a BST insert whose key comparison is a call
  before the branch (`Nat`, `String`, `compare`), even with the local fix
  of Reussir issue 7, a missed optimization (patch 07-a, parked since
  2026-10-07: this pass covers the issue;
  reussir-bugs/07-phantom-reuse-donor.md). A structure
  (one constructor: no match, its fields are projections) that stays live
  the same way projects only the fields used while it is live; an inner
  alternative that no longer uses it projects the others there (the pair
  `(k', t)` of an association list, kept whole when its key does not
  match).
  A merge (`List.mergeSort`'s `mergeTR.go`, the classic `mergesort`'s
  `merge.go`) then reuses the cell it takes apart, as native Lean does.
  Without the rule for calls it allocated a cell at every step and freed
  the matched one, which made the result's memory order a matter of
  allocator state: when the size class has few free cells (the list just
  filled its last page: the length modulo the 2048 32-byte cells of a
  64 KiB page), mimalloc hands back cells freed all over the heap, so the
  sorted list costs a cache miss per cell to walk (S6-02: `List.mergeSort` on
  `List Nat` and every later walk of its result 5-9x native at n = 1e6 or
  2e6, 1.2x at n = 997960; `List UInt64` 3.9x at n = 1000800). When the
  allocator has long runs of free cells, allocating compacts the list
  instead, which a sort of random input gains from: the classic
  `mergesort` runs at about 0.75x native with reuse, 0.4-0.5x when
  allocating.
- The same holds for the fields of a structure, which are projected
  (`let f = s.0`) at the top of the alternative: when the alternative then
  branches and one branch keeps `s` whole while only other branches use
  the field, the projection moves into the branches that use it (a pass
  over the generated code, `Opt/SinkProj`). An association-list update
  `if k == k' then (k', f v) :: more else (k', v) :: go k more` keeps the
  pair whole in the second branch; with `v` projected before the `if`, the
  skipping branch allocated a new cons per element and freed the matched
  one after the recursive call, which was then no longer a tail call.

### 5.6 Join points

A join point is a local continuation: `jp j y := body; k`, where the code
`k` exits through `jmp j arg` (in tail position) or `return`. Lean creates
them for shared code after branches (`if`/`match` followed by more code, `do`
blocks, early `return`). After Stage 2 they have three useful properties:
- they are **never recursive**, since loops in LCNF are recursive
  functions;
- they take the outer variables they use as **explicit parameters**
  (`extendJoinPointContext`);
- unused and constant parameters have been removed (`reduceJpArity`,
  `commonJoinPointArgs`).

Reussir has no join points, so each one becomes ordinary structured code.
Every strategy below is correct for the same reason: on every path that
reaches a jump, `body` runs exactly once, after everything that comes before
the jump. Effects are data flow on the world token, so this keeps their
order too. The strategies are tried in this order: J1, J2, J1', then J3 (or
J4).

**J1, single jump: inline.** When `j` is jumped to from one place, put
`body` there, with `y` bound to the argument.

**J2, all paths join: structured `let`.** When every path through `k` ends
in `jmp j …` (or in unreachable), `k` becomes an expression that produces
`j`'s arguments, followed by `body`. This is the common "diamond" shape. The
mono example of §3 becomes:

```rust
let y7 = match head {                                  // cases head : Prod Nat P
    Prod_Nat_P { fst, snd } =>
        if leanrt::nat_dec_lt(3, fst) {
            let f = leanrt::uint8_to_float(snd.a); leanrt::float_add(snd.c, f)
        } else { leanrt::float_of_scientific(0, true, 1) }
};
let x8 = List_Float::cons{y7, a2};                     // body of _jp.6
loop(tail, x8)
```

A join point with several parameters yields a small generated `[value]`
struct, which is destructured afterwards.

**J1', small join point: duplicate.** A join point that is not J2 is
inlined at each of its jumps, like J1, when it is small: its body has at
most 40 bindings, alternatives and exits (nested join points included), a
copy of it expands to at most 480, and its copies beyond the first add at
most 2000 (jumps minus one, times the expansion), or 4000 for a loop's
continuation: a join point whose own body (not the join points it jumps
to) tail-calls a function of the declaration's call cycle (its strongly
connected component in the program's call graph). The
expansion counts, at each jump, the body of the join point jumped to when
that is inlined there too: a join point nested in the copy (at every jump
to it), another join point jumped to once (J1 inlines it whatever its
size), or another join point whose own body is small, counted the same
way. Outlining the join
point would put a function boundary on the path: a loop through it would
become a state machine or mutually recursive, and Reussir could not reuse a
cell matched before the jump for a construction after it. Duplication is
recursive: small join points inside a duplicated body, and those it jumps
to, are duplicated again. The bounds keep every copy within 480 nodes and
what the copies of one join point add within 2000 (4000), so code grows
linearly.
Each bound closes a blow-up the others allowed:
- the bound on the body alone: Lean leaves sibling join points that are
  jumped to from two others, which sinking cannot nest. A sequence of
  `match`es on a two-constructor state, each alternative setting the next
  state to a constant, gives one join point per alternative, jumping to
  either alternative of the next `match`; each is small, and the first
  ones held 2^n copies of the last (20 `match`es: out of memory;
  tests/runtime/RtJpChain);
- the bound on one copy: after an 800-arm `match` whose arms set such a
  state (with an early return elsewhere), each alternative of the next
  `match` is jumped to from hundreds of arms, and was copied into every
  one (11.7 MB of .rr; rrc ran out of memory; tests/runtime/RtJpWide);
- counting only small join points in a copy: a large join point jumped to
  once, from inside a small duplicated one, is inlined into every copy.
  Sinking (`jp-sink`) puts it inside its jumper, where the bound on the
  body sees it, but without sinking 200 copies of an 80-`let` body were
  made (Lean's dead-branch elimination leaves such join points, for
  instance after a `match` on an `Option` that is always `some`).
The expansion is an upper bound (a J2 or outlined target costs only its
jump). The budgets are generous enough that loops keep their shape: a loop
whose condition is a few `&&`/`||` tests, each a join point jumping two or
three times to the shared continuation, expands to 300-350; a loop's
continuation after a `match` of up to about 100 arms (copies of 30-40
nodes) is still copied into each arm. Outlined, such a continuation makes
the loop a state machine, or, in mutual recursion, a stack frame more per
iteration. The larger budget is only for loop continuations: given to every
join point, it let a 35-line function with a wide `match` setting a state
and a few `match`es on it add 0.5-0.75 MB of .rr (eight such functions: 6.3
MB, a four-minute build at 5.7 GB); and judged through the join points a
copy jumps to, one rare guarded self-call in the last of such a chain of
`match`es gave it to the whole chain (eight functions: 7.3 MB of .rr).
Behaviour does not change. (Optional pass `jp-small`; without it such join
points are outlined, J3.)

**J3, otherwise: outline.** Some paths `return` directly or jump to a
different join point. Then `j` becomes a separate top-level function over
its parameters (and any remaining free variables), and each `jmp j a`
becomes a tail call `j_fn(…, a)`:

```
jp j y := BODY                       fn f_j(fv, y) -> T { BODY }
cases x                         ↦    match x { A => z,
| A => return z                                B => f_j(fv, u),
| B => jmp j u                                 C => f_j(fv, v) }
| C => jmp j v
```

The captured variables `fv` are the free variables of the lowered body,
under the names they have where `j` is declared, and every jump passes
them under those names. An alternative may name a matched variable anew
(a constructor without fields uses a fresh nullary value, a boxed value is
matched after its conversion), but the old name stays in scope there: a
join point outlined inside such an alternative whose body jumps to `j`
captures the old name too, not just the variables the alternative names.

**Sinking first.** Before choosing, every join point is moved down to the
smallest part of its scope that contains all its jumps: past `let`s, into
the single `cases` branch that jumps to it, into the continuation or body of
another join point. Free variables stay in scope (binders are unique), and
no code is duplicated. A join point declared before a `cases` of which only
one branch uses it often satisfies J2 once sunk into that branch.
(Optional pass `jp-sink`.)

**J4, outlined join points that call back: one state machine.** When a
self-recursive declaration has outlined join points whose bodies call the
declaration (a loop whose body is a DAG of join points, e.g. a chain of
`if`s with shared continuations), J3 would make the loop mutually
recursive, and a mutual tail call is a jump only when LLVM can make it a
sibling call, which Reussir's reference counting after the call can
prevent: the loop would use stack per iteration (the classic Sieve and
Strings overflowed a 1 GiB stack that way at their medium size). Instead
the declaration becomes one function over an enum of entry points: one
variant `e` for the declaration's own parameters and one per outlined join
point (its captured variables and parameters). The function matches on the
entry point; the declaration's wrapper enters it at `e` with its
parameters, a self tail call enters at `e` with the new arguments, and a
jump to an outlined join point enters at that join point's variant. All of
these are self tail calls, which LLVM turns into a loop. Every value a
jump needs travels in its variant, so nothing is kept alive by being passed
along. J4 is used only when an outlined join point makes a self tail call,
in its body or in a join point inlined into it (J1, J1'); other calls back
into the declaration are ordinary calls. The enum is a
shared (heap) type: Reussir miscompiles `[value]` enums with fields of
mixed layout (§9), so in this core form every call and every jump
allocates a variant.

The optional pass `state-machines` makes every variant nullary: the
values travel as parameters of the function instead, in *slots*, one per
type and position. A variant puts its `i`-th field of type `T` in the
`i`-th slot of type `T` (a variable it passes on unchanged under a
parameter's name keeps that parameter's slot), so the function has as many
slots of type `T` as the variant with the most fields of type `T`. Each
arm binds its fields from their slots. Example: a loop
`fa (i n : Nat) (s : String)` whose join point `j` uses `i`, `n`, `s` and
a `Nat` parameter `a` becomes

```
fn fa_sm(s1 : Nat, s2 : Nat, s3 : LStr, s4 : Nat, m : fa_mode) -> R {
    match m {
        fa_mode::e  => { let i = s1; let n = s2; let s = s3; … },
        fa_mode::j1 => { let i = s1; let n = s2; let s = s3; let a = s4; … }
    }
}
```

and a jump to `j` is `fa_sm(i, n, s, a, fa_mode::j1{})`, a self call with
`fa_sm(i + 1, n, s, zero, fa_mode::e{})`. A jump passes its own values in
their slots and a placeholder in every other slot, never a live value: a
value passed twice would be kept alive across the jump (an array updated
before the jump would be copied at every iteration). Placeholders are
cheap: a constant (`0`, a constructor without fields), a value built once
and kept in a once-cell (§5.1), and for a string one shared empty string
of the runtime. A type without a finite placeholder (a type without a
finite value, such as `Empty`, §5.1) gets no slot: such a field stays in
its variant, which is then allocated as in the core form. The pass checks
this on every state machine. So a jump costs a jump and the moves of its slots, and no
allocation (test `RtJpSlots`).

**Choice and nesting.** J1 applies first, then J2, then J1' (small), then
J3 (J4 when an outlined body tail-calls the declaration).
- J2 requires every jump to `j` to stay inside the same Reussir function.
  If `j` is also jumped to from inside a join point that was outlined, `j`
  is outlined too.
- Inner join points are lowered before the outer ones that contain them.

**Why the choice matters beyond style.**
- *Stack use.* Loops are recursive functions, and Lean runs self tail calls
  as loops. Under J1 and J2, a self tail call stays inside its own
  function, where LLVM reliably turns it into a loop. Under J3, the tail
  call goes through the outlined function, and the loop becomes mutually
  recursive. Reussir has no guaranteed tail calls, and LLVM makes a
  mutual tail call a sibling call only when all arguments fit in
  registers. A `for` loop in Lean's `forIn'` form overflowed a 1 GiB stack
  that way at 10⁷ iterations until sinking made its join points J2. J3 is
  therefore the last resort. Guaranteed tail calls remain a candidate
  Reussir request.
- *Memory reuse.* J1 and J2 keep "destructure the old value" and "build the
  new one" in one function. That is what Reussir's token reuse needs to
  update in place.

### 5.7 Constructors and projections

- `let x := Tree.node ◾ l k r` at type `Tree Nat` becomes
  `let x = Tree_Nat::node{l, k, r};`. Erased type arguments are dropped.
  The instance is read from the `let`'s type.
- A projection (rare after `structProjCases`) becomes a field access.
- Nullary constructors of `[value]` enums (`Ordering::lt`) and of shared
  enums (`Tree_Nat::leaf`) cost no allocation in Reussir.

### 5.8 Externs and runtime calls

A call of an extern of Lean's library becomes a call of the prelude
function named after the extern's C symbol (or generated glue, below);
the externs of the program follow the rule of "Externs of the program"
below. lean2rr keeps no table of the externs it supports: it checks that
the prelude defines each function it calls, and when it does not, rejects
the program at translation, naming each such extern (§10, "Not
supported"); `lean2rr --emit externs` lists the externs a program calls.
The prelude function is:
- inline Reussir code, for fast paths such as small-`Nat` addition with an
  overflow check;
- or a call into the runtime crate (§6).

| Lean extern | Implementation |
|---|---|
| `Nat.add`, `Nat.decLt`, … | `leanrt` `Nat` operations: small fast path, bignum slow path |
| `UInt32.add`, `UInt8.div`, `Float.add`, … | `+ - *` map to native Reussir arithmetic, since both wrap. Division, remainder, shifts and float→int always go through wrappers with `lean.h` semantics (e.g. `x / 0 = 0`, `x % 0 = x`, shift by `b % bits`, saturating casts), the shared crate lean-runtime's: Reussir lowers them straight to LLVM operations that are undefined at those edge cases. |
| `Array.push@Nat`, `Array.get!@Nat`, … | `Vec` operations; out-of-bounds follows Lean (panic message plus default value) |
| `String.append`, `String.get`, … | `leanrt` string functions; the UTF-8 byte-position rules are the shared crate lean-runtime's (`runtime/README.md`) |
| `IO.getStdout`, `IO.FS.Stream.putStr`, … | runtime IO |

Rules:
- **Same semantics as `lean.h`.** Each implementation matches the C code
  Lean's runtime uses, on the representation types. `Int8` operations
  work on the `u8` bit pattern with signed semantics, exactly as
  `lean_int8_*` do. Division and modulo by zero, shifts, float-to-int
  saturation, `Nat.sub` truncation, and `Int.div` vs `Int.ediv` are all
  taken from `lean.h`.
- **Effects are never optimized away.** IO, `ST.Ref`, panic and trace
  functions are opaque side-effecting calls. The IO world is only
  `L2RUnit`, so nothing else would stop Reussir or LLVM from merging,
  dropping or reordering two identical `println` calls; the probe of §9
  confirmed that effectful FFI calls are kept in order.
- **Lean-defined types in signatures.** Externs that take or return
  Lean-defined types (`IO.FS.Stream`, `IO.Error`, `Option`, `List`,
  `Ordering`) get a small generated wrapper around runtime primitives on
  native types, or pass the generated constructors to a generic runtime
  helper as arguments. That keeps the runtime independent of generated type
  names. `Array.mk` and `Array.toList` are generated loops.
- **Externs implemented in Lean.** Many externs' C symbols are provided
  by an `@[export sym]` Lean definition (`String.Internal.*`,
  `Substring.Raw.Internal.*`, `lean_string_intercalate`, …): Lean's runtime
  calls back into compiled Lean code. lean2rr calls that definition
  directly (`Mono.redirectTarget`) and compiles it like any other, so its
  semantics are exactly Lean's. Lean's other exports are not externs of the
  program: the `IO.Error` builders `lean_mk_io_error_*`, which Lean's C
  runtime calls, are reached through lean2rr's own glue
  (`ensureIOErrorBuilders`, `ioErrorFn`; fallible IO, below).
- **Lean-only target.** The owner's decision (2026-10-03): "let's just
  target lean only code for now, with runtime library as the only
  exception". lean2rr compiles Lean code, and Lean's runtime library is
  the only native code it uses: the C code of a program or of a package it
  requires (Lake's `extern_lib`) is never compiled, linked or called. The
  Lean definition of an `@[extern]` is its specification, so running it
  is not an ad-hoc port of the C code.
- **Externs of Lean's library** (declared in a module of the toolchain's
  library: `Init`, `Std`, `Lean`, `Lake`, and lean2rr's shim `L2RShim`;
  `Mono.isToolchainDecl`, which decides by the module's name: the loader
  has checked that a module so named is the toolchain's own file, §10
  "Module names") are served by the runtime, as above. One the runtime
  lacks is a gap of the runtime: lean2rr rejects the program, naming each
  such extern, and never runs the extern's Lean body in its place (often
  a slow reference definition: `Nat.add`'s is unary recursion).
- **Externs of the program** (any other: of the program's modules or of a
  package it requires) take the first of these routes that applies
  (`Mono.computeExternRoute`):
  1. `@[implemented_by g]`: `g`, as natively.
  2. *A binding to the program's own `@[export]`.* When the extern's C
     symbol is the `@[export]` of another declaration of the program (not
     of Lean's library: the `@[export]`s of Init, such as
     `String.Internal.dropImpl`'s `lean_string_drop`, count as Lean's
     runtime library, REB-14), native Lean's call is
     linked to that definition, and lean2rr calls it too, provided two
     tests pass (`Mono.bindingFailure?`, a rule shared with another Lean
     translator built on the same runtime). *One type*: the extern's type
     is an instance of the definition's: the definition's type with its
     universe parameters instantiated is the extern's, definitionally at
     transparency `all`, borrow marks aside (`{α : Type}` binds to
     `{α : Type u}`). On the definition's *result* type, and only there,
     Lean's two mono identifications apply: a trivial structure is its
     single relevant field and `Decidable p` is `Bool`, so `mk1 : Nat → Nat`
     binds to an `@[export]` returning a `{m : Nat // m > 0}` (its value
     meets the stronger invariant). On a parameter they would be unsound: a
     `Nat` passed where the definition takes a `{n : Nat // n > 0}` could be
     `0` (a `UInt32` for a `Char` could be `0xD800`). *One compiled
     signature*, the condition under which the native call is defined, read
     from Lean's compiled (impure-phase) signatures: the arguments the
     extern's C call passes (not the IO world, not erased ones) are the
     definition's C parameters (erased ones included, so a definition with
     type parameters never binds, and their instantiation is not needed),
     with equal types, the results have one type, and the borrow marks are
     equal, except that an owned argument may meet a parameter the
     definition borrows (natively a leaked reference), never the reverse
     (natively the definition releases a reference the caller still
     holds). The extern becomes a `noinline` declaration calling the
     definition (`Mono.exportForwardDecl`): renamed to the definition in
     Stage 1, its calls on literals would be folded by Stage 2's passes,
     which natively never happens to a C call (`Nat.shiftLeft 1 (2^64)`
     stopped lean2rr, reviews RV8E-11, REB-01). A body the extern has is
     not used, as natively.
  3. *Its Lean definition*, whenever it has one, also when its C symbol is
     that of an extern of Lean's runtime library: an extern of the program
     is never bound to Lean's runtime (the owner's decision of
     2026-10-04, shared with the other translator), so where its
     definition and the runtime's function differ, the definition is what
     runs. It is compiled as Lean compiles a definition without the
     attribute (`Mono.externBodyDecl`: the `_unsafe_rec` copy of a
     recursive or `partial` one, `@[csimp]` replacements, `macro_inline`,
     matchers), `noinline` (RV8E-11). Its callees follow the same rules.
     Lean's compiled callers of a function that a `@[csimp]` theorem
     replaces by an extern call the extern (lean-zip's `UInt64.ctz` →
     `UInt64.ctzFast`), so they get its definition too. `@&` marks need
     nothing (Reussir decides ownership).
  4. Otherwise it is *refused*: lean2rr stops at translation and names
     each such extern the program reaches, with its module, its C symbol
     and why: no Lean definition (an `opaque`, an axiom) or Lean's error
     compiling it, each binding test that failed, and, for a symbol of an
     extern of Lean's library, that declaration to call instead ("call
     `Array.size` instead"), or, for a private one (module system), that a
     program can call it only from a `module` file that imports it with
     `import all M` (`Lean.decodeLossyUTF8` of `Lean.Shell`, REB-10,
     REB-12). When the program does not import a module
     declaring the symbol but the runtime implements it, the message names
     the module of Lean's library that does, to import if that declaration
     is public (read from the toolchain's library source, imported or not;
     REB-03); a helper of
     lean2rr's own prelude (`l2r_nat_repr`, `lean_array_uswap`) gets no
     such hint (REB-07). It says that lean2rr supports Lean code plus
     Lean's runtime library only.

  ```lean
  @[export my_triple] def tripleImpl (n : Nat) : Nat := 3 * n
  -- binds to tripleImpl's @[export] (one type, one compiled signature)
  @[extern "my_triple"] opaque triple : Nat → Nat
  -- borrows what tripleImpl takes owned: the binding fails, the body runs (lean2rr warns)
  @[extern "my_triple"] def tripleB (n : @& Nat) : Nat := 3 * n
  -- the symbol of Array.size: not bound to the runtime, the definition runs
  @[extern "lean_array_get_size"] def sizeNat (a : @& Array Nat) : Nat := a.size
  -- the symbol of Nat.add, no definition: refused ("call Nat.add instead")
  @[extern "lean_nat_add"] opaque myAdd : Nat → Nat → Nat
  -- a symbol of the program: the body runs (natively the program's C)
  @[extern "my_custom_double"] def myDouble (n : Nat) : Nat := n + n
  ```

  The route order and the binding's two tests are shared with another
  Lean translator built on the same runtime. lean2rr's build note marks
  an extern whose definition runs where natively a function of Lean's
  library runs: "(natively Lean's runtime function)" for the symbol of an
  extern of Lean's library, imported or not, "(natively Lean's library
  function)" for an `@[export]` of Lean's library (REB-13). When the route is the
  extern's Lean definition although its C symbol is another declaration's
  `@[export]` whose binding fails, lean2rr warns on its own stderr, naming
  the definition and each failed test (review REB-02, test
  `RtExternStub`). Tests `RtExternBody`, `RtExternBind`, `RtExternRefused`
  and the other `RtExtern*`; plan §10 ("Not supported").
- **Fallible IO** (files and the file system): the runtime primitive
  records its outcome in a last-error slot; `l2r_io_finish` turns it into
  `EST.Out.ok` with the payload (converted: unit, handle, `Metadata`, an
  array of `DirEntry`) or into `EST.Out.error e`, where `e` is built by
  Lean's own exported `lean_mk_io_error_*` builder for the reported kind,
  as Lean's `decode_io_error` does (the builders are instantiated when a
  program uses such an extern). Since Lean 4.34 the kind and the message
  come from libuv's code for the errno (`uv_strerror`'s text, not
  `strerror`'s), and an error of a libuv-based operation stores the
  positive errno. `IO.FS.Handle` is the runtime's `LHandle`.
- **Child processes** (`IO.Process`, over the runtime's `l2r_proc_*`
  primitives, which follow Lean's `process.cpp`). Natively a `Child` object
  carries, after its three stream fields, the pid (`uint32`) and whether
  the child was spawned with `setsid` (`uint8`). The generated record for
  `IO.Process.Child` has the same two hidden fields after its Lean ones:
  `struct Child(Box, Box, Box, u32, bool)` (the streams are `lcAny` in
  mono code: a boxed `LHandle` for a piped stream, a boxed unit otherwise,
  as natively `box(0)`). Lean code never builds a `Child` (its constructor
  is private), so only the glue sets the hidden fields:
  - `spawn args` reads the `SpawnArgs` record and flattens it as the
    primitive takes it: the three `Stdio` indices packed into `modes`, the
    command and arguments, `cwd` as a string and a flag, `env` as three
    parallel arrays (names, values, whether the value is `some`; generated
    loops), `inheritEnv`, `setsid`. On success the `Child` gets
    `l2r_proc_end(k)` for each piped stream, the pid and the flag.
  - `wait`, `tryWait` (`1 << 32 | code`, or 0 while running) and `kill`
    read the hidden fields. They borrow the child natively (`@&`), so the
    glue holds it until the result is built, and its pipes stay open while
    the call runs (a child still writing to a pipe the parent has not read
    does not get `EPIPE`). `pid` is the hidden field; `takeStdin` returns the stdin
    field and a new `Child` with a boxed unit instead, keeping the other
    fields.
  - `IO.Process.output` is Lean code that reads stdout in a dedicated task
    while it reads stderr. lean2rr's tasks are deferred (§5.14), so a child
    writing more than a pipe holds (64 KiB) to stdout before closing stderr
    blocked forever before lean2rr ran on lean-runtime's scheduler (whose
    IO now cooperates: lean-runtime's case `taskio/output_big_stdout`; the
    pattern runs in user code too). The replacement stays because it reads
    both pipes together and writes a large input while it reads them,
    where Lean's code writes all of the input first and can wait for good
    (LB-40). Its declaration is lowered to one runtime primitive instead of its body,
    `l2r_proc_output` (lean-runtime's `io::process::output`), which does
    what Lean's definition does in its order: spawn with stdout and stderr
    piped and stdin null, or piped when `input?` is `some s` (then `s` is
    written and flushed, and the handle closed); both pipes read to end of
    file together; `readToEnd`'s UTF-8 check of stderr (`IO.userError
    "Tried to read from handle containing non UTF-8 data."`); `wait`; the
    same check of stdout. `l2r_proc_output_str` gives the two outputs.
    `IO.Process.run` is Lean code over `output` and needs nothing more.
    Each fallible step's error becomes the `IO.Error` Lean's
    `decode_io_error(errno, nullptr)` builds, as for files.
- **Proofs.** A `Prop`-valued inductive has the unit representation, and a
  parameter of such a type (a proof) is not passed to the runtime.
- **`BaseIO` externs that cannot fail** call the runtime's payload
  primitive `l2r_<symbol without lean_>` when the prelude defines it; its
  result is wrapped as the IO result (`EST.Out.ok` / `ST.Out`). Its
  arguments and, for a non-generic primitive, its result are converted
  between the extern's mono types and the primitive's: a runtime object is
  `lcAny` in mono code (a `Box`) and the runtime's `LHandle` or `LPromise`
  for the primitive.
- **`Std.Sync`** (`BaseMutex`, `Condvar`, `BaseRecursiveMutex`,
  `BaseSharedMutex`, whose externs Lean implements over `std::mutex` & co.
  in `mutex.cpp`) are runtime handles holding lean-runtime's objects
  (`sched::sync`), and their externs payload primitives over
  `leanrt::sync`. The rules are lean-runtime's: a thread that must wait
  blocks its context (§5.14, *Blocking*); a lock's owner is a thread: a
  context, and on it the innermost running task's thread (a task needed by
  another runs on a worker thread natively). As with glibc, locking a
  `BaseMutex` the same thread holds waits forever, `tryLock` then fails,
  and a released mutex goes to the thread that waited longest; the shared
  mutex follows libc++'s (a writer that has entered keeps new readers out). Everything
  else (`Mutex`, `Barrier`, channels, `Notify`, `Broadcast`, cancellation
  tokens) is Lean code over these and promises.
- **`Std.Internal.UV`** (timers, TCP and UDP sockets, name resolution,
  signals, the system queries of `Std.Internal.UV.System`, and `Std.Net`'s
  address conversions and interfaces, natively C over libuv that builds
  Lean values) is implemented in Lean by lean2rr's shim library
  `L2RShim` (`lean2rr/L2RShim.lean`): each definition is exported under an
  extern's C symbol, so it is the extern's implementation (above), and
  lean2rr imports the shim with the program (`LeanToReussir.Env`, from
  `L2R_SHIM_DIR`, which the driver sets to lean2rr's build directory, last
  on the search path; lean2rr stops if that directory has no shim) and
  treats it as a toolchain module (no startup work). When the modules of
  `Std` that the shim imports declare a name the program declares too
  (`Std.Data.ByteSlice`'s `ByteSlice`; natively no clash, the program does
  not import them), lean2rr loads only the shim's part over `Init`
  (`L2RShim.Core`: `ShareCommon` and the replaced definitions below), with
  a note; the shim's `Std` externs are then missing. The shim builds Lean's
  values over primitives of the runtime (`leanrt::net`, `leanrt::sys`) on
  plain values (numbers, strings, byte arrays, handles, promises), whose
  rules are lean-runtime's: its event loop's timers and signal watchers
  (`sched::uv`), sockets, name resolution and interfaces (`net`), address
  texts (`semantics::net`) and system queries (`io::uvsys`), §5.14; errors
  are lean-runtime's `IoError`s, built in Lean by their `IO.Error`
  builder, code, file name and details (`L2RShim.ioErrorOf`; the system
  queries' libuv codes are decoded by lean-runtime as
  `lean_decode_uv_error` does).
  The shim also replaces Lean definitions whose native behaviour depends
  on Lean's borrow inference: a definition exported as
  `l2r_override_<mangled name>` is called instead of the definition of
  that name (`Mono.redirectTarget`). `IO.Promise.isResolved` is one:
  natively it borrows the promise (`result?` does), so the caller releases
  it after the question, and a last reference resolves the promise with
  `none` only then; compiled as written, the release would come inside
  `result?`, before the question (`isResolved` on a promise's last use
  would answer `true`). The replacement asks the runtime, then releases
  the promise.
- **Constructors with an implementation.** Constructors of builtin types
  that Lean implements in its runtime (`Int.ofNat` is `lean_nat_to_int`,
  `Int.negSucc`, `ByteArray.mk`, …) are calls, as in Lean's IR.
- **Element storage.** A polymorphic extern instance knows its type
  arguments. A value whose *declared* type is a type parameter `α` (the
  element of `Array.push`, or a trivial structure over `α` such as
  `[Inhabited α]`, which mono represents by its field) is passed and
  returned in `α`'s storage type: a `Box` for an extern over arrays of `α`
  (an array holds `Box`es), boxed and unboxed at the call; for any other,
  `α`'s own type, wrapped or unwrapped if that is an `ElemBox`. Other
  parameters, like an index, are passed as they are.
  Instance keys hold base-phase types, so type arguments go through
  `toMonoType` first.
- **Generic prelude functions over values.** Storage types exist only
  because values cross into Rust. A prelude function that is plain Reussir
  code (not an FFI import) and whose signature applies no generic type
  (no `RVec<T>`, `LRef<T>`) never does that, so it is instantiated at the
  value types themselves and receives its arguments as they are:
  `dbgSleep 1 fun _ => n + 1` at `Nat` is
  `lean_dbg_sleep<Nat>(ms, f : L2RUnit -> Nat)`, not
  `lean_dbg_sleep<ElemBox>` with a closure returning a `Nat`. This covers
  `dbgTrace`, `dbgTraceIfShared`, `dbgSleep`, `dbgStackTrace`, `panic`
  and `sorry`; lean2rr finds these functions by reading the prelude.
- **Borrowing.** Reussir passes every argument owned and releases a value
  at its last use. Natively a parameter that Lean borrows (its
  `inferBorrow`, and `@&` annotations) is released by the caller after the
  call returns. Only resources can tell: natively a file handle written by
  a helper that borrows it is still open (its data still buffered) when the
  helper reads the file again; a child whose stdin pipe a helper borrows
  does not see end of file while the helper waits for it; a promise whose
  `result?` task a helper asks about is not resolved yet (the last
  reference to an unresolved promise resolves the task with `none`). So
  for a program that creates resources (it calls `IO.FS.Handle.mk`,
  `createTempFile`, `IO.Process.spawn` or `IO.Promise.new`), lean2rr runs
  Lean's own borrow inference on its mono
  declarations (Lower/Borrow: copies go through `toImpure` and the impure
  passes up to `inferBorrow`, as Lean compiles its own declarations; extern
  instances get their extern's `@&`; the instances of an exported
  declaration, `@[export]` or `main`, are marked exported, so their
  parameters stay owned, as Lean's `isExport` keeps the declaration's) and
  emulates Lean's reference counting
  where a value may hold a resource, decided on the mono type of the
  parameter it is passed to (a handle, which mono types `lcAny`, so any
  `lcAny`; an inductive or array with such a field at its type arguments,
  so not a `List Nat`, although its one Reussir type holds `Box`es):
  - a direct call keeps an argument passed to a borrowed parameter until
    the call returns (`l2r_release_after`, an effectful FFI call after the
    call, as Lean's `dec`), when the caller owns it; an argument the caller
    itself borrows (a borrowed parameter, a field or array element of one,
    an `a[i]!` whose array and `Inhabited` instance are both such values,
    the value of a constant, a constructor applied to no variable such as
    `none`, a join point parameter to which every jump passes such a value
    or `◾`) is left alone, as natively, so a loop's tail calls stay tail
    calls;
  - a function value of such a declaration calls a `_boxed` variant that
    releases its borrowed arguments after the call, as Lean's `_boxed`
    functions do for closures;
  - the kept arguments are released last first, in the reverse order of
    their first occurrences among the arguments, as Lean's `explicitRc`
    prepends each `dec` after the call: `put3 a b c` with three dead
    handles closes `c`, then `b`, then `a`.
  A failure of the inference is a translation error: the emulation is all
  or nothing.
  Other values keep Reussir's release times: the same results without the
  extra reference counting. The process glue keeps a `Child` alive across
  `wait`, `tryWait` and `kill`, which borrow it by annotation.

### 5.9 Panics and unreachable code

- `panic!` prints what native prints (`PANIC at …: msg`) to stderr, then
  **returns the default value and continues**, as native does.
- Reaching `unreachable` stops the program as Lean's
  `lean_internal_panic_unreachable` does: it prints `INTERNAL PANIC:
  unreachable code has been reached` and exits with status 1.
- lean2rr also inserts impossibilities of its own: the other-variant arm
  of a `Box` unwrap, a cast with no conversion (§5.1). They currently print
  the same message, so a lean2rr bug looks like Lean's own unreachable
  (§10).

### 5.10 IO and the world token

In mono, an IO function takes the world as an extra `lcVoid` parameter and
returns `EST.Out ε σ α`, with constructors `ok a` and `error e`. The world
becomes an `L2RUnit` parameter. `EST.Out` becomes an ordinary
two-constructor enum; its phantom `σ` is ignored. A `BaseIO`/`ST` result,
whose error case is impossible, is the one-field structure `ST.Out`. Effects
happen inside runtime calls in program order.

Real output (`--emit mono`, then `--emit rr`) for
`def main : IO Unit := do let s := "hi"; IO.println s`. The literal became a
closed term (§5.12), read through a once-cell:

```
def main._l2r.0._closed_0 : String :=
  let s : String := "hi"; return s
def main._l2r.0 (a.404 : lcVoid) : EST.Out IO.Error lcAny PUnit :=
  let s : String := main._l2r.0._closed_0
  let _x.405 : EST.Out IO.Error lcAny PUnit := IO.println._at_.main.spec_0._l2r.0 s a.404
  return _x.405
```

```rust
fn l_main___l2r_0____closed__0_init() -> LStr {
    let x504 : LStr = l2r_str_lit(21);
    x504
}
fn l_main___l2r_0____closed__0() -> LStr {
    let r : u64 = if l2r_once_ready(28) { 0 } else {
        if l2r_once_claim(28) { 0 } else { l2r_once_put<LStr>(28, l_main___l2r_0____closed__0_init()) }
    };
    l2r_once_get<LStr>(28)
}
fn l_main___l2r_0_(a505 : L2RUnit) -> T_EST_Out_348 {
    let x506 : LStr = l_main___l2r_0____closed__0();
    let x507 : T_EST_Out_348 = l_IO_println___at___00main_spec__0___l2r_0_(x506, a505);
    x507
}
```

### 5.11 Program entry

A generated Reussir `#[main]` does what Lean's generated `main` does
(`EmitC`: `initialize_Main`, then `lean_io_mark_end_initialization` and
`lean_init_task_manager`, then `lean_run_main`, then
`lean_finalize_task_manager`):
0. before any of it (lean-runtime's ELF constructor, so before Rust's
   runtime starts), the runtime opens the descriptors that native Lean's runtime has open
   when the program starts: libuv's event loop opens an epoll descriptor,
   two io_uring rings (when the kernel has them), its two signal pipes and
   an eventfd, close-on-exec, at the lowest free numbers (3 to 10 when the
   standard descriptors are open; a standard descriptor closed at startup is
   taken by the first of them, as natively, so using it fails as natively).
   `/proc/self/fd`, the numbers of the descriptors the program opens and the
   point where opening fails with `EMFILE` are native's;
1. it runs the startup work of §5.12 on the process's main thread (8 MiB
   stack), with `IO.initializing` answering `true`. An error there prints
   `uncaught exception: <message>` and exits with status 1 before `main`;
2. it clears `IO.initializing` and starts the task manager: IO tasks are
   deferred from now on (§5.14). It then starts a thread with a 1 GiB
   stack, as Lean's runtime does for `main` (deep non-tail recursion is
   common in Lean programs); `main` starts there with the process's
   standard streams, as a new thread does natively, whatever the
   initializers redirected. With `LEAN_MAIN_USE_THREAD=0`, as natively,
   there is no new thread: `main` runs on the process's main thread after
   the initializers and keeps the standard streams they left (an
   `IO.setStdout` in an `initialize` still applies in `main`);
3. on that thread it calls the translated `main`, passing the argument list
   (without the program name) if `main` takes one, and the world;
4. it runs the IO tasks still pending, whatever `main` returned, as
   `lean_finalize_task_manager` does before the result is looked at;
5. on `error e`, it prints `uncaught exception: <message>` to stderr and
   exits with status 1;
6. otherwise it exits with the returned `UInt32` (0 for `IO Unit`).

`leanrt::rt::run_main2` implements the two threads (`main`'s is
lean-runtime's `io::startup::run_main` since switch step 7; it has no name
of its own, as native's `lthread`); Lean's stack
overflow report is lean-runtime's (`sched::install_stack_overflow_handler`,
on both threads): a stack overflow in either thread or in a task (on a
context of lean-runtime's scheduler, §5.14) prints `Stack overflow
detected. Aborting.` and aborts (status 134, stdout not flushed), as Lean's
handler does in every thread. Each thread has an alternate signal stack;
a fault in the guard page below the thread's stack, or below the running
context's, is an overflow, and any other fault takes the action before
the handler (Rust's, or the default). leanrt's own handler, gone with step
4, also took a fault below the stack while the stack pointer was below it
(a frame without stack probes can skip the guard page); lean-runtime's, as
Lean's, does not (`RtStackOverflow` still passes).

The runtime flushes stdout at exit. These behaviours were observed on native
executables.

### 5.12 Constants (CAFs) and closed terms

Native Lean behaves as follows (observed; `EmitC.emitInitFn`):
- every zero-parameter declaration of a module's compiled code is
  **evaluated at program start**, in the module initializer, *even if
  unused*. This includes declarations the compiler generates, such as a
  specialization `gen._at_.main.spec_0` with every parameter fixed;
- `extractClosed` constants are evaluated **lazily, once**, on first use;
- all of these values live for the whole run;
- simple ground values (literals, constructors of literals) are static
  data and cost nothing.

A constant whose code only builds unboxed values from small literals and
constructors (`Int.ofNat 0`, an enumeration value) is recomputed at every
use instead of cached. Every `Nat` or `Int` it builds must be small (a
`Nat` below 2^63, an `Int` in `int32`; `def K : Int := 3000000000` is a
big number, which is cached: recomputed it would be allocated at every
use, RV8N-01). It cannot panic, trace or allocate, so this is
unobservable, and it is cheaper than a once-cell read (optional pass
`cheap-consts`). A constant boxed where boxing allocates (a `Float`, a
`UInt64` from 2^63) is boxed once, its box kept in a once-cell, as Lean's
`_boxed_const_N` (optional pass `boxed-consts`): the default of `a[i]!`
on an `Array Float` is `instInhabitedFloat`, and boxing it at every read
was a new cell per read. A closed term referenced exactly once, by another constant
(the steps of an array literal, `_closed_k := push _closed_(k-1) e_k`), is
evaluated where it is used instead of cached: it still runs once, and the
intermediate values are not kept (caching every step of a 10000-element
literal kept 1 GB of intermediate arrays). When its code and its user's are
straight-line (`let`s, then `return`), it is spliced into the user before
lowering (`spliceChainConsts`): an `n`-element literal (`#[…]`, `[…]`, a
`ByteArray`) becomes one straight-line body instead of `n` functions
calling each other (rrc compiles about 80 functions per second: a
100000-element `Array Nat` took ten minutes to build), each element's
literal placed right before its push. Long bodies are cut by `Outline`
(§10, "Build time"). (While an `Array Nat` was a one-word `LNatArr`, a run
of small `Nat` literals became a table the runtime pushed; an array of
`Box`es has none, and the 100000-element `Array Nat` literal's build time
is to be measured again.)
Only a chain where nothing but literals (and closed terms of literals) is
computed before a step reads the previous one is spliced: otherwise every
element would be computed before the whole rest of the chain and live
across it (an `Array Float` literal whose elements are shared constants),
where the chain evaluated step by step holds one element at a time; such a
literal stays a chain of functions.

A float literal arrives as a call of a Lean function on literal arguments,
`Float.ofScientific 15 true 301` for `1.5e-300` (or `Float.ofNat n`,
`Float32.…`), which is not cheap: the slow path (a mantissa of `2^53` or
more, an exponent above 22) goes through `Float.Model` with bignum
arithmetic. lean2rr evaluates such calls itself, with the same Lean
functions (lean2rr is compiled from the same `Init` code, so the bits are
Lean's, subnormals and rounding included), and replaces them by
`Float.ofBits` of the bit pattern, a cheap constant as above. Calls with
an exponent above 2000 or a mantissa of more than 4096 bits are left to run
(cached as usual when they are a constant), as are all of them without the
optional pass `float-lits`.

The initializer follows Lean's compilation order: native Lean initializes a
module's declarations in the order in which it compiled them
(`EmitC.emitInitFn`). The `.olean` records part of that order. Its
`extraConstNames` are the module's IR declarations that are not kernel
constants (closed terms `c._closed_N`, `_boxed` wrappers, lifted lambdas
`_lam_N`, specializations), newest first, and Lean adds a command's IR when
it compiles the command. So each declaration that compiled to at least one
of them gets its place in the compilation order (`compileOrder`): every
specialization (whose order among themselves depends on how Lean's
specializer recursed), every `initialize` action, and nearly every constant
whose value calls a function (Lean extracts the call as a closed term).
Not recorded are constants whose calls Lean leaves in place: a callee whose
type is not syntactically a function (`def F := Nat → Nat`), a value equal
to a closed term an earlier declaration made (Lean's closed-term cache), or
a module compiled with `set_option compiler.extract_closed false`. A
hygienic name keeps its
macro scopes at the end: `zz._closed_0._@.M._hyg.3` is a closed term of
`zz._@.M._hyg.3`. A specialization's name is the exception: Lean appends
`_at_.g.spec_N` after them (`helper._@.M._hyg.3._at_.runIt.spec_1`).
lean2rr rebuilds a name from its components one at a time, not with
`Name.append`, which reads a part ending in `_hyg` as a hygienic name and
panics (round 6 RV6L-04, round 9 RV9S-01).

lean2rr orders the startup items by the program's structure (below), then
puts the items that the record places in the recorded order, in the places
the structural order gave them. The others keep their places, except that a
constant goes after the constants it reads: evaluating it evaluates them
(their accessors compute them on demand), and natively they come before it
(a constant reads only constants declared before it, or its own helpers).

The structure: compilation follows the source, command by command. A `def`
or `instance` command is compiled after it is elaborated, together with its
`where`/`let rec` helpers: the elaborator lists the helpers (those of later
`mutual` members first, outer ones before nested ones, a member's `where`
helpers before the `let rec`s of its body, since a `where` clause is a
`let rec` around the body, otherwise in source order), then the command's
own declarations, and compiles the strongly connected components of their
reference graph one at a time, callees first (Tarjan's order over that
list). A declaration generated while compiling a component, such as a
specialization `f._at_.g.spec_N` made while compiling `g`, comes right
before the component's members; an auxiliary declaration made during
elaboration (`c.unsafe_1`, `instInhabitedP.default`) comes before the whole
command. For example

    def p : Nat := t "p" (h1 + h2)
    where
      h1 : Nat := t "p.h1" 1
      h2 : Nat := t "p.h2" (h3 + 1)
      h3 : Nat := t "p.h3" 3

initializes `p.h1`, `p.h3`, `p.h2`, then the specializations made in `p`,
then `p`. lean2rr rebuilds this order from declaration ranges (a helper's
range lies inside its parent's; the `where` helpers are the last direct
helpers: the last one ends where its parent ends, and each other one starts
on the line of the next one, after `;`, or at the column of the next one on
an earlier line, or is shifted by a doc comment or an attribute, which the
ranges leave out), from the kernel's `all` (a recursive mutual block), from
the compilation record and from uses (a `mutual` block whose members do not
call each other is recorded as separate definitions, but a later member's
code compiled before an earlier member's shows that they share a block,
with every command in between, and so does a declaration that uses a later
one, which only a `mutual` block allows), and from the references in the
declarations' kernel values (for a `partial` definition, its
`_unsafe_rec`). The function of an `initialize` declaration belongs to its
constant: a specialization made inside the action comes right before the
action.

Positions are compared as (line, column). Declarations with the same range
need more. Every declaration of one macro expansion has the macro call's
range, and the instances of one `deriving instance … for A, B` command
share one range too. A range equal to another one is therefore not
"inside" it: `mk foo foo.bar` makes two commands, not `foo` and its helper.
Such commands are ordered by the position of their names (a macro that
takes the names from its arguments keeps their positions; a hygienic name
made by the macro has the call's position, so it comes first), then by the
order in which the module added its instances (the instance extension keeps
it), then hygienic names by their macro scopes (which grow as a command
expands its macros; the names of one quotation share them), and last by
name, with the numbers in names compared by value: the auxiliary constants
`c._unsafe_1`, `c._unsafe_4`, …, `c._unsafe_10` of a declaration with
several `unsafe` parts start in that order. The compilation record then
orders those it records, as the macro wrote them. For the others macro
scopes are only a guess: a macro that defines a name and then expands the
rest makes increasing scopes in elaboration order, one that expands the
rest first makes them in the reverse order.

What no rule recovers is the order of unrecorded constants where the
structure does not fix it: the members of a `mutual` block that do not use
each other, the made-up names of one quotation, the names a recursive
macro makes in the reverse of their scopes (§10). The `.olean` of a
non-recursive `mutual` block of such constants and that of the same text
without `mutual` differ only in fresh-name counters left in later
declarations' code (one name fewer used before them); the declarations'
own records (names, ranges, kernel values, LCNF, IR, extension entries)
are equal. For the made-up names of one quotation, only the macro's own
definition (its code) holds the order.

Our translation runs, before `main`, the startup work of Lean's module
initializers, for each module that natively is initialized, in Lean's
module order (below; the toolchain's modules included):
- for a program module, for each of its declarations that natively runs,
  in the order above:
  - an `initialize` action (`initialize do …`) is run;
  - for `initialize c : T ← act`, `act` is run and its result stored as
    `c`, which the program reads from a once-cell;
  - any other zero-parameter declaration of the module's base-phase code
    (the persisted base LCNF, so generated declarations are included),
    instances included, is evaluated;
- for a module of `Init` or `Std`, its `initialize` declarations, in
  source order, used or not;
- for any other toolchain module (the `Lean` package's), nothing.
In a program that uses the `Lean` package (a module of it is among the
modules initialized), the initializer of `main`'s module natively calls
`lean_initialize()` first (`emitInitFn`), so before anything else all of
`Init`, then all of `Std`, then all of `Lean` are initialized
(`initialize_Init`, `initialize_Std`, `initialize_Lean`), whatever the
program imports: lean2rr runs the `initialize` declarations of `Init` and
`Std` first (loading the modules `Init` and `Std` when the program's
imports do not reach them), then the `Lean` package's `initialize`
constants that the program uses (§10), then the rest of the walk.
An error from an initializer is reported like an uncaught exception of
`main` (the message, exit code 1), and later initializers do not run
(natively, in a program that uses the `Lean` package, an error in
`lean_initialize()` aborts instead; §10).

The other toolchain constants are evaluated lazily, once, on first use:
native Lean evaluates all of them at startup, but they are pure, so the
time of their evaluation does not show. An initializer is an action, and
its effects show whether or not the program uses its constant. Lean
4.34.0's `Init` and `Std` have one, `IO.stdGenRef` (`Init/Data/Random.lean`:
`IO.getRandomBytes 8` seeds `IO.rand`'s generator), which every program
that imports `Init` runs, as does a program that uses the `Lean` package
(`lean_initialize()`); a `prelude` program runs it only when its imports
reach `Init.Data.Random`, at that module's place. It opens and reads
`/dev/urandom`, and when no descriptor is left (`ulimit -n 11`, libuv's 8
descriptors taking 3 to 10) the program stops before the initializers
after it with

    uncaught exception: resource exhausted (error code: 24, too many open files)
      file: /dev/urandom

and exit code 1. lean2rr ran it only when the program used `IO.rand`, so a
program that did not ran `main` there (test `RtStartupInitUrandom`). It
then ran it before every program initializer, where natively a `prelude`
program's module that its imports list before `Init.Data.Random` is
initialized first (review RSG-01, test `RtStartupInitOrder`), and not at
all in a `prelude` program that imports a module of the `Lean` package
but not `Init.Data.Random` (RSG-02, test `RtStartupInitLeanPkg`). `IO.rand`
reads the generator from its once-cell and never seeds it again (test
`RtStartupInitRand`). Running these initializers costs a few functions per
program (the initializer, `IO.mkRef`, `mkStdGen`, `ByteArray.toUInt64LE!`
and its panic message). The search covered every constant of `Init` and
`Std` with an `[init]` or `[builtin_init]` attribute; `Std`'s other modules
add no system call at startup (`strace` of a native `import Std` program).
Closed terms are lazy, once.

Which modules and declarations run, and in which order, follows `EmitC`
(`emitMainFn`, `emitInitFn`, `emitLegacyInitFn`; `startupModules`,
`startupItems`). Native `main` calls the initializer of `main`'s module,
which first calls those of the module's imports, in import order, each
module once: the modules are initialized in a depth-first post-order walk
of the import graph from `main`'s module (a module that `main`'s module
does not import, directly or not, is not initialized). Under the module
system a `module` has two initializers, one per phase: the *runtime* one
calls the runtime initializers of the module's non-`meta` imports, then
initializes the declarations not marked `meta`; the *compile-time* one
initializes those marked `meta` (`meta def`, `meta initialize`), which only
the compiler's own evaluation needs. So:
- when `main`'s module is a `module`, only runtime initializers run: the
  walk follows only non-`meta` imports (a module reached only through a
  `meta import` is not initialized at all), and `meta` declarations are
  skipped. For example

      module
      meta import Gen          -- Gen is not initialized (unless also imported
                               --   without `meta`, directly or not)
      import Util              -- Util's runtime initializer runs first
      meta initialize do …     -- skipped: it runs only when the compiler
                               --   imports this module
      meta def table : Nat := …   -- skipped
      initialize do …          -- runs
      public def main : IO Unit := …

- when `main`'s module is not a `module`, every import is followed, and an
  imported `module` is initialized as for an importer outside the module
  system: its imports (`meta` ones included), then its declarations not
  marked `meta`, then its `meta` ones (each group in the order above).

A declaration counts as `meta` when the one native Lean initializes is
marked so (`isMarkedMeta`): for `meta initialize c : T ← act`, the constant
`c`; for `meta initialize do …`, its function. Declarations the compiler
generates, such as a specialization made while compiling a `meta def`, are
not marked and run with the runtime phase, as natively.

lean2rr itself never runs the program's initializers: it loads the imported
extension states without Lean's init step, which would execute the
program's `initialize` actions inside the compiler.

The startup steps are emitted as functions of at most 128 steps each,
called in order (with a further level of grouping when there are more than
128 of those): one chain of nested matches, one per initializer, would be
as deep as the program has initializers, and rrc's recursive lowering
overflows its stack on a few thousand. An error in a step exits from inside
it, so later steps do not run.

The storage is a runtime once-cell per constant (the prelude's
`l2r_once_ready`/`claim`/`put`/`get` over `leanrt::once`), holding a value
that is never freed. Each slot's word and set flag are also kept in static
tables at fixed addresses (`leanrt::once::FAST`, `FLAGS`), so that a read
of a set constant is one load from a constant address and a test
(`l2r_once_ready`), then the reference's increment (`l2r_once_get`, whose
load LLVM merges with the first): a load fewer than a native closed
term's `lean_obj_once` (its state, then its value), a test more than a
native named constant (a global's load). A value whose bits are all 0
(its word is 0) costs a second load, of its flag; no read calls out.
When the slot is not set, `l2r_once_claim` decides who computes the
value: the caller computes it (`l2r_once_put` stores it), and another
context of the scheduler (§5.14) that needs it meanwhile (the computation
blocked) waits until it is set, as natively a thread waits for the one
computing a closed term (`lean_obj_once_cold` holds a lock); needed again
by the context computing it, it waits forever, as natively. A value that
is not a pointer-sized boundary type is wrapped in an `ElemBox` struct.
The tables' words and flags are plain loads and stores: Lean code runs
on one thread at a time (the initializers', then `main`'s); with Lean
code on several threads, the store would have to release and the load
acquire. The same slots back the runtime's mutable cells
(`l2r_cell_swap`). Reussir has no global variables; they would not be
cheaper than the table.

### 5.13 Names

Generated names are valid Reussir identifiers and never clash with runtime
or std names:
- an instance of declaration `d` is named `d._l2r.k`, with a counter `k`
  per declaration, and mangled with Lean's own scheme (`Name.mangle` with
  prefix `l_`): `l_main___l2r_0_`;
- a generated type is `T_<hint>_<counter>`, with variants `c_<constructor>`;
- helpers use `l2r_` prefixes (`l2r_conv_…`, `l2r_unbox_…`, `l2r_vconv_…`).
Uniqueness comes from the counters, not from an encoding of the type
arguments.

### 5.14 Thunks and tasks

Both are a runtime cell `LCell<S>`: one allocation holding a count and one
value, updated in place and seen through every alias. The value is a
generated state, one type for thunks and one for tasks, whatever `α` is
(the value is boxed):

```
enum L2RThunk_N { pending(L2RUnit -> Box), busy, done(Box) }
enum L2RTask_N  { pending(L2RUnit -> Box), busy, done(Box),
                  bind(L2RUnit -> LCell<L2RTask_N>) }
```

The state is a shared Reussir enum, so every `α` fits, closures and value
types included; a closure cannot be stored in a runtime cell directly.
`bind` is a bind task that has not started (below). `Thunk.mk f` wraps `f`
(`Unit → α`) as a function value returning a `Box` (§5.3), `Thunk.get`
unboxes the value it gives.
toMono leaves only a few externs to translate: `cases` on a thunk or task
becomes `Thunk.get`/`Task.get`, and `Thunk.fn` a closure calling
`Thunk.get`.

**Thunks** follow `lean_mk_thunk` and `lean_thunk_get_core`:

| Lean | Reussir |
|---|---|
| `Thunk.mk f` | `l2r_lcell_new(S::pending{f})` |
| `Thunk.pure a` | `l2r_lcell_new(S::done{a})` |
| `Thunk.get t` | `l2r_thunk_get_S(t)`: `done(v)` gives `v`; `pending(f)`: swap in `busy`, `v = f(())`, store `done(v)`, give `v` |

- The closure runs at most once, on the first `get`, and is released after
  it has run, as Lean's thunk drops its closure before calling it.
- `busy` means the thunk is needed by its own computation. Lean then spins
  forever waiting for the value; the translation waits forever too.
- Cost: `Thunk.mk` allocates one object more than Lean (the `pending` state
  around the closure). The first `get` replaces it by the `done` state,
  which Reussir can build in the cell it frees.

**Tasks.** Native Lean runs tasks on a thread pool. A worker may start a task
at any time after it is created and must have finished it when its value is
needed. The translation is single-threaded and runs its tasks on the shared
crate lean-runtime's task scheduler (`lean_runtime::sched`; its
`docs/sched.md` has the model and every rule), which picks one such
schedule: Lean's task manager on one thread, with *contexts* that block and
resume. lean2rr's part is the task objects and the glue (`leanrt::task`,
`leanrt::sched`; implementation notes `docs/implementation/tasks/`).

- Every task created after `main` has started is *deferred*: its cell is
  `pending(|w| …)`, and it is given to lean-runtime (`spawn`; for a task
  that depends on another, `depend`, Lean's `add_dep`), whose job for it
  runs the generated code through the program's dispatcher. For IO tasks
  (`BaseIO.asTask`, `mapTask`, `bindTask`) the computation is `act(w).val`
  (for `mapTask f t`, `f t.get`); for `bindTask t f` the cell is
  `bind(|w| (f t.get w).val)`, whose computation yields the task the new
  one continues as. Pure tasks (`Task.spawn`, `Task.map`, `Task.bind`) are
  deferred the same way (`keep_alive` false); `Task.pure a` is `done(a)`,
  a finished task, which lean-runtime never sees. During module
  initialization Lean has no task manager and `lean_task_spawn_core` runs
  the computation at once; so does the translation (those tasks share the
  initializer's streams), and so with `LEAN_NUM_THREADS=0`.
- A task runs, as lean-runtime decides (its "The model"), when it is
  needed (`Task.get`, `IO.wait`: on the stack of whoever needs it once it
  is the task a free worker would start), when the running code blocks and
  a worker is free, at an effect point once a worker would have started it
  (5 ms), when the program polls for it (`IO.getTaskState`: two sleeps or
  1000 questions), or when `main` returns (`finish`, which runs what is
  left in the order Lean's task manager would start it, also a pool task
  enqueued after `main`, which native Lean never runs: LB-13). Pure tasks
  no IO task waits for are only marked started where a worker would start
  them, and run when needed, polled, at exit, or when nothing else can go
  on (lean-runtime's pure-task rule).
- *Dropped tasks.* The program's last reference to an unfinished task is
  its cell's last (the scheduler's job holds no count): its drop calls
  lean-runtime's `release` (Lean's `deactivate_task`). A pure task that has
  not started is deleted and never runs; dropping its state releases its
  source, so a chain of dropped pure tasks goes, as natively. Any other
  task runs to completion (the glue keeps its cell), and its finish wakes
  nobody, as natively.
- *Priorities.* 0 to 8 are the task manager's queues; every priority
  above 8 is a dedicated task, as `Task.Priority`'s documentation says.
  lean2rr passes the whole priority, one of 2^64 or more as `u64::MAX`
  (`l2r_nat_sat`). Natively Lean passes `lean_unbox(prio)` as an
  `unsigned`: 2^32-1 is `LEAN_SYNC_PRIO`, a task that runs at once on the
  enqueuing thread, and 2^32 to 2^32+8 are pool priorities (LB-39, §10).
- *Dependents.* When a task finishes (its job returns, or a promise is
  resolved), lean-runtime walks its dependents from the newest
  (`handle_finished`): a `sync := true` one runs
  there and then, on the finishing context, the others are queued; the
  waiters of finished tasks wake at the end of the walk. A bind task that
  has run `f` finishes at once if the task `f` returned has finished, and
  otherwise waits for it (`task_bind_fn1`). `mapTask`/`bindTask`/
  `Task.map`/`Task.bind` with `sync := true` of a finished task apply `f`
  at once in the calling thread, as `lean_task_map_core` does.
- `IO.cancel`, `IO.checkCanceled` (true at shutdown, for a task that could
  have started before only once time has passed in it), `IO.getTID`
  inside tasks (`main`'s id plus lean-runtime's thread number), `IO.waitAny`
  (its notification rule, what runs on the waiter's stack) and `Task.get`
  in a `sync := true` task (Lean's panic, then the wait) are lean-runtime's.
- *Closed terms.* Lean evaluates a closed term once, at its first use, and
  then marks it persistent (`lean_mark_persistent`), which waits for every
  task it reaches and makes every object it reaches persistent: never
  freed, and not looked into by a later mark. The module initializer does
  the same for each constant it evaluates and for each `[init]`
  declaration's result, and `Runtime.markPersistent` for its argument. A
  constant whose type may hold tasks waits for its tasks right after it is
  evaluated (`l2r_persist_T`; a program constant at startup, an `[init]`
  result after its initializer, a closed term at its first use), whether
  they are in fields, arrays, the values of tasks, the values captured by
  function values (partial applications), thunks (their computation, or
  their value: the thunk is not forced), references (their value),
  promises (their task) or boxed values. The walk works as Lean's does: a
  loop over a list of the values still to look at (no recursion), in
  Lean's order (it pushes an object's fields in order and pops the last
  one first). It marks each cell it visits persistent (its count goes up
  by 2^30: never freed, never unique; `leanrt::persist`) and does not look
  into a cell that is persistent already, marked by this walk or an
  earlier one. A box is looked into where the walk meets it: a payload
  whose type can hold a task is pushed, any other is marked without being
  looked into (a persistent cell keeps all it holds), an immediate is
  nothing; so a list's or an array's boxed numbers make no work. So a later walk does not read again a reference, a thunk, a
  task or a promise that an earlier walk (or the startup) reached: a
  closed term that reaches an initializer's reference does not wait for a
  promise `main` stored in it. Natively waiting only blocks, and the
  workers run the term's tasks in queue order; lean-runtime's `wait`
  keeps that order too (the awaited task runs only once a free worker
  would start it), so the walk waits for each task as it reaches it, in
  one pass. What it reads out of a reference or a thunk is read when it
  gets there, so a task that replaces the task a reference next to it
  holds has run by then, as natively. A placeholder's never-forced task
  cell (`pending` with the function value `z`, §5.1) is not a task
  (natively `box(0)`, which the walk skips; test `RtZeroWalkRef`). The
  walks are generated at the end of lowering, and do nothing for types
  that cannot hold a task; a program that creates no task has none.
  `Runtime.markPersistent` also marks its argument persistent whatever its
  type, so a marked file handle is never closed.
- A thunk or task is never converted: it has one type whatever its value
  type, so typed and uniform code share the one cell (a task's address is
  its identity for the runtime).
- *Promises* (`IO.Promise α`, `lcAny` in mono code) are a runtime object
  (`LPromise`) holding the cell of their task (the one task type, whose
  value, an `Option α`, is boxed); lean-runtime's promise is that task. `Promise.resolve` stores `some v` (only the first
  resolution counts) and lean-runtime walks the task's dependents on the
  resolving thread (`resolve_core`). `Promise.result?` gives the task as it
  is (one task type), and `Promise.result!` maps `Option.getOrBlock!` over
  it (lean-runtime's `option_get_or_block`: Lean's forced panic message,
  then the context waits forever). Dropping the last reference to an
  unresolved promise resolves it with `none` (`deactivate_promise`).
  `IO.Promise.new` during initialization is Lean's internal panic.
- *The event loop* is lean-runtime's (its scheduler's: epoll, timers,
  watches, a loop context of its own for the callbacks, as libuv's loop
  thread natively): `Std.Internal.UV`'s timers and signal watchers
  (`sched::uv`), sockets and name resolution (`net`). An operation that
  completes later (a timer firing, data received, a connection accepted)
  gets, from the shim, a promise `r` of `Unit` and a `sync` continuation on
  `r` that resolves the program's promise; lean-runtime's completion stores
  the outcome and drops its reference to `r`, so the continuation runs on
  the loop context, as libuv's callback natively runs on libuv's thread.
  `Std.Async` (`Async`, `sleep`, `Interval`, `Selector`, TCP and UDP
  clients and servers) is Lean code over these.
- *Standard streams.* Natively each thread has its own current standard
  streams (`IO.setStdout` & co. replace the current thread's, which start as
  the process's), and a task runs on a worker thread. So each context has
  its own stream cells (lean-runtime's `Glue::switched`), a task run as on
  a worker thread starts with the process's streams, and when it ends the
  streams of whoever ran it are back (`l2r_std_enter_if`/`l2r_std_leave_if`
  set the stream cells aside and restore them; lean-runtime's
  `Glue::task_begin` says which tasks). That is a dedicated task's; a pool
  task runs with its emulated worker's stream cells instead (lean-runtime's
  `running_worker`), which the worker keeps from one task to the next, as a
  native worker thread keeps its streams, and which are dropped at the task
  manager's finalization (as the workers' thread finalizers drop theirs). A
  task that runs on the current thread (a `sync` dependent) shares that
  thread's streams. `main`, on its own thread, starts
  with the process's streams whatever the initializers installed (§5.11).
  A task's `sync` dependents run with whatever streams the task left
  installed, as natively on its thread (a dedicated task ends inside its
  stream context, lean-runtime's `end_running_task`).

*Blocking.* A thread that blocks natively (a mutex another thread holds, a
condition variable, `IO.wait` of a task another worker runs or of an
unresolved promise, a channel, a socket, `IO.sleep`, a read of an empty
pipe) lets the others go on. lean-runtime's contexts do that on one
thread: `main`'s (its thread's stack) and one per task it starts, each a
corosensei coroutine on a stack of a native worker's size (1 GiB, or
`LEAN_STACK_SIZE_KB`, touched only as used, with a guard page that
reports Lean's stack overflow); when the running context blocks, its hub
runs a context that can go on, a queued task on a new context if one of
the task manager's workers is free (`LEAN_NUM_THREADS`, or the online
processors), or waits in its event loop. Effect points (output, a flush, a
process spawn, `IO.Process.exit`) and polling points (task-state
questions, `IO.checkCanceled`, the program's clock reads) let what
natively would have run by then go first. lean-runtime's IO cooperates
(a read of an empty pipe, a write to a full one, `flock`, `Child.wait`
let the others run). lean2rr's glue: the one `unsafe` step of a switch
(`Glue::suspend`), the per-context streams, and the keys under which its
own objects wait in lean-runtime's wait cores (a thunk being forced on
another context, under its address: `l2r_thunk_wait_busy`, woken by
`l2r_thunk_done`; a constant another context computes, under
`(slot << 1) | 1`: `once::claim`).

No context is suspended inside a free (the free's pending work is the
thread's, Reussir's `reussir_rt::drop`, and the other contexts would push
their frees onto it): the drop of a stream handle runs in lean-runtime's
no-suspend scope (a dropped stream's flush hands what would wait to a
writer thread), and nothing else a free reaches waits. This decides when the `sync`
dependents of a promise dropped unresolved run (natively at once, on the
dropping thread, wherever that happens):
- a promise whose last reference is released by itself (not inside a
  free) is resolved with `none`, and its dependents run at once, as
  natively;
- a promise held by a container being freed (an array, a list, a
  structure, a map, an `Option`, ...) is resolved with `none` as soon as
  the free is over, its cell's store and the walk of its dependents
  together, in the order the free reached the promises (natively during
  the free, when it reaches the promise), before the code that released
  the container goes on (lean-runtime's deferred resolutions, `defer` and
  `run_deferred`). A free inside such a dependent is a free of its own:
  its promises' dependents run when it ends, before the dependent goes
  on, as natively (test `RtPromiseNestedFreeOrder`). The runtime sees the
  end of every free through local Reussir patch 40-a
  (`__reussir_drop_drained`, which every drain that released something
  calls when it ends), which lean2rr requires (`scripts/l2r.py` stops
  with an error without it).

A reference's `set` stores the new value before it releases the old one,
as `lean_st_ref_set` does (Reussir's `cell::set` releases first): code that
the release runs sees the new value. It releases the old value as
`lean_dec` does (`leanrt::drop::release`, through the prelude's
`l2r_release_value_then`, which then releases the reference: a set that is
the reference's last use frees the old value before the new one, test
`RtRefSetLastUse`): a shared value is only decremented, and the last
reference to a record is freed inside a free the runtime starts, so what
it holds goes in Lean's order (its last field first) and the dependents
of the promises it drops run when that free ends, before the next
statement. The same holds for the old state of
a task or thunk cell (`l2r_lcell_set`, which first lets the writers of the
streams the context handed off end: a publication, lean-runtime's
`before_publish`).

*References.* lean2rr decides at translation time whether a program
creates tasks: whether one of the externs it reaches (its own code and the
code of Lean's library it calls, after the shim's replacements) makes a
task or a promise (`Task.spawn`, `Task.map`, `Task.bind`, `IO.asTask`,
`IO.mapTask`, `IO.bindTask`, `IO.Promise.new`; polymorphic, so each one
the program reaches is an instance of it). Every context other than
`main`'s comes from those: a task, a promise's dependents (run where it is
resolved), the event loop's completions (they resolve the promises the
shim's Lean code makes); a `Std.Sync` object or a timer alone makes none.
So a program without them has one context,
`main`'s, and its reference operations are plain cell operations (its code
is the same as before). In a program that creates tasks each reference
operation first has a point (`leanrt::refs`, lean-runtime's keyed
reference rule, `sched::ref_keyed`):
- a read (`get`, `take`, `swap`) is a polling point: every 1000th read on
  the thread polls (lean-runtime's `ref_read`), so a loop that polls a
  reference another task sets ends (`while !(← flag.get) do pure ()`);
- a write (`set`, `take`, `swap`) is a publication (`before_publish`);
- `ST.Ref.modify` is `take`, then `set`; `take` records the reference as
  taken by the running frame (the context, the number of tasks running on
  it, and the innermost one), and until the closing store (a `set` or
  `swap` in that frame: modify's own), every other `get`, `take`, `set` and
  `swap` of that reference waits, then sees modify's value: Lean 4.35's
  rule (LB-01 and LB-18 not reproduced, §10). The taker's own `get` and
  `take` wait too (natively the reference is multi-threaded where safe code
  reaches it inside modify's pure function, through the `sync` dependent
  of a promise the function drops, and its `get` spins forever: review
  RS4-01, test `RtRefOwnGetDuringModify`), and so does a store from such a
  dependent (natively 4.34 stores into the empty slot, LB-01). A `modify`
  whose function waits for a task that uses the same reference deadlocks,
  as in 4.35.

The cost, in programs that create tasks only: a load and a branch per
read and per write while no reference is taken, a recorded `take` per
`modify` (to measure in an owner-approved timing session).

lean-runtime's scheduler itself starts at the first task, promise,
`Std.Sync` object, timer, signal watcher or socket after `main` started
(its lazy start, `sched::start_lazy`, which `leanrt::task::start` calls at
`main`'s start; lean-runtime's entry points call `ensure_started`), with
the number of workers and the stack size `main`'s start read as natively:
a program that makes none pays nothing for it.

Why tasks are deferred rather than run at creation: a task may wait for
`main`. `IO.asTask (do while !(← flag.get) do IO.sleep 1; …)` followed by
`flag.set true; IO.wait t` finishes natively; run at creation, the task
would spin forever. Running at creation also prints the task's output
before `main`'s next line, which natively comes first when the task starts
with a sleep, and computes pure tasks the program then drops.

What a single thread cannot do (lean-runtime's "The limits of one thread",
and lean2rr's own):
- contexts do not run in parallel: one that computes without blocking, an
  effect point or a polling point delays the others (in a program that
  creates tasks every 1000th `ST.Ref` read is a polling point, so a loop
  polling a reference that another task sets ends: "References" below);
- `IO.waitAny` does not pick the fastest of several unfinished tasks;
- tasks nobody waits for stay queued, with what they hold, until `main`
  returns or a worker is free;
- a few blocking calls still block the whole thread (`open` of a FIFO,
  lean-runtime's list).

Tasks that wait for each other in a cycle wait forever, as natively.

---

## 6. Runtime (`leanrt`)

The rules of Lean's runtime that do not depend on how values are
represented come from the shared crate lean-runtime (the submodule
`third_party/lean-runtime`, shared with another Lean translator): hashes, string positions
and comparisons, float formatting, bits, `frExp`, `scaleB` and conversions,
the fixed-width integer rules, libm, the `Nat` and `Int` rules (zero
divisors, truncation, rounding, shift and exponent limits, the size of a
big result), the array edge rules (out-of-bounds indices, allocation
sizes, `copySlice`'s ranges), the panics' texts and endings, the decimal
text of numbers, and the OS-level IO (lean-runtime's `io`: glibc's `FILE`
model behind handles and the standard streams, `IO.Error`'s decoding, the
file system, temporary files, the environment, the clocks, child
processes, `Std.Internal.UV.System`, the startup descriptors,
`IO.initializing` and the exit sequence), the task scheduler (lean-runtime's
`sched`: Lean's task manager on one thread, promises, `Std.Sync`, the event
loop with `Std.Internal.UV`'s timers and signals, Lean's stack-overflow
report) and the networking (`net`: sockets, name resolution, interfaces;
`runtime/README.md`, "The shared crate lean-runtime"). `leanrt` and the prelude hold lean2rr's representations and
hot paths (the inline small-`Nat`/`Int` arithmetic, the one-block big
numbers with GMP's kernels behind lean-runtime's `BigNat`/`BigInt`
traits, the one-block arrays' reads, writes and pushes) and convert
lean2rr's values to lean-runtime's views and back. The runtime provides
what Reussir lacks:
- `Nat`/`Int`: a small value, or a GMP bignum (`leanrt::big`);
- Lean's `String` operations over UTF-8 bytes (one block with the character count, §5.1);
- `Array`/`ByteArray`/`FloatArray` operations over the copy-on-write one-block vector;
- `Float` and `Float32` math: lean-runtime's `semantics::libm`, glibc's
  results, with the operands LLVM would fold or rewrite hidden from it:
  natively every call runs glibc's function at run time, and LLVM's folded
  or rewritten values (`f32` functions in double precision, `exp2` through
  `pow`, `pow(x, 0.5)` as `sqrt`, …) differ from glibc's in the last bit on
  some inputs;
- IO: the glue of lean-runtime's `io` (handles in `LHandle` boxes, the
  last-error slot from which the generated code builds `IO.Error`s, the
  current standard streams as lean2rr's own cells), argv;
- the mutable cells of thunks and tasks, their entries naming
  lean-runtime's tasks, the jobs that run them through the program's
  dispatcher, promises, and the glue of lean-runtime's scheduler and event
  loop (§5.14);
- panic, trace;
- once-cells for constants.

Everything runs on one thread: tasks are deferred until needed
(lean-runtime's scheduler, §5.14), which gives one of the schedules native
Lean can produce. Real
threads, using Reussir's atomic reference counting, come later. Each
runtime function consumes the arguments it owns, and never mutates in
place unless it has checked for uniqueness (the cells of refs, thunks and
tasks are mutable by design).

---

## 7. Optimization: what is already done, and what is left

**Already optimized, reused from Lean:**
- inlining;
- specialization of higher-order and instance arguments at the original
  call sites, plus our type specialization;
- simp, cse, let-floating;
- join-point cleanup;
- arity reduction;
- dead-branch elimination;
- lambda lifting;
- closed-term extraction.

**Left to Reussir by design:** all memory management.
- Perceus ownership.
- Token reuse, which replaces Lean's reset/reuse. Mono code comes *before*
  reset/reuse, so Reussir sees the plain destructure-then-rebuild pattern it
  optimizes.
- Drop specialization, inc/dec cancellation, TRMC, closure
  devirtualization, LLVM.

**Gained from typing:**
- no boxing;
- unboxed scalars in fields, closures and arrays (`Vec<u32>`, where Lean
  boxes array elements), enumerations in arrays as indices;
- unboxed enum-like types;
- per-type drop code;
- exact allocation sizes.

**Room kept open.** Each of these can change later without changing when
work runs or what the program computes:
- `[value]` for small non-recursive structs;
- borrowed parameters, if Reussir adds them;
- globals for constants (done without them: a constant's read is one
  load from a runtime table at a fixed address, §5.12);
- re-running Lean's `specialize` after monomorphization.

The lowering keeps Reussir's job easy:
- it prefers J1/J2 over J3;
- it emits structured control flow;
- it adds no closures, reference counting or reuse of its own.

lean2rr's own optimizations are optional passes, listed with the required
parts in `lean2rr/LeanToReussir/Opt/Registry.lean` (§1, "Code structure
and passes").

---

## 8. Checking that the rules are right

Reviewers go through each section and ask one question: does following this
rule make the translated program behave like the Lean program? They answer
with evidence: Lean's compiler sources, `lean.h`, or a small native
experiment.

Points that deserve particular attention:
- Stage 1 substitution versus Lean's specializer;
- dictionary folding;
- the Stage 2 driver really running Lean's passes as Lean does;
- that Stage 3 never guesses a type;
- arity and closure timing (§5.2–5.3);
- the join-point strategies and their nesting condition (§5.6);
- extern semantics against `lean.h` (§5.8);
- startup behaviour (§5.12);
- that nothing lets Reussir or LLVM drop or reorder effects.

Tests run each program natively and through lean2rr, and compare:
- stdout and exit code exactly;
- stderr with panic backtraces removed, since those contain random
  addresses.

They match except for the known divergences of §10.

---

## 9. Open items

Probe results (Reussir at the pinned commit):
- **FFI types.** Integers, floats, `bool`, `char`, `str`, opaque runtime
  types and shared records cross the FFI boundary; `unit` only as a result.
  `[value]` records, closures and `unit` parameters do not, hence
  `L2RUnit`, the `ElemBox` element wrapper and the runtime's generic
  helpers taking constructors as arguments.
- **Runtime crate.** The runtime is an external Rust crate (`leanrt`) linked
  into every program; its statics are shared by all FFI textures (each
  texture is otherwise its own crate).
- **Inlining.** Textures are inlined into Reussir code only when compiled
  for the same target CPU and features as Reussir's own code, and only
  under LLVM's size threshold, so hot runtime functions keep a small fast
  path and an out-of-line slow path.
- **Tail calls.** Self tail calls become loops, unless the function has a
  stack slot whose address escapes (a `str` argument, a float or 4+
  argument FFI call through the packed-argument path). Mutual tail calls
  become sibling calls only when all arguments fit in registers.
- **Effects.** Effectful FFI calls are never merged, dropped or reordered,
  at every optimization level.
- **Stacks.** The main thread has 8 MiB; the program body runs on a 1 GiB
  thread (§5.11).
- **Known Reussir bug.** A `[value]` enum is lowered to LLVM as its tag
  plus one representative arm's struct, and moved as that aggregate, so
  bytes of another arm that fall on the representative's padding or on a
  `bool` field are lost (`enum [value] M { A(u8), B(bool) }` reads `A(42)`
  back as 0). lean2rr only emits `[value]` enums that are unaffected:
  enumerations without fields. Everything else with several arms is a shared enum (J4
  entry points, §5.6); multi-field value records are `[value]` structs,
  whose padding is explicit.
- **Candidate Reussir requests.** Guaranteed tail calls; `[value]` types
  across the FFI (for array elements without a wrapper); borrowed
  FFI parameters (an array `get` currently takes ownership and releases);
  a no-inline attribute (lean2rr uses `#[transform_anchor]`, whose
  `no_inline` is a side effect, reussir-bugs/20-statet-tower.md); tagged
  opaque handles (one-word `Nat`/`Int`, §5.1: local patch 41-a,
  reussir-bugs/41-tagged-ffi-objects.md); bounded-depth frees (local patches
  13-a to 13-c).

Answered (Lean):
- Startup order: `EmitC.emitInitFn` runs the module's compiled
  declarations in compilation order, skipping closed terms and simple ground
  declarations (§5.12).
- `lean_apply_n` (`apply.cpp`) calls the code directly at exact arity,
  builds a partial application with fewer arguments, and with more calls and
  then applies the rest: one-argument-at-a-time semantics (§5.3).
- Identity is not preserved. Native Lean answers `ptrAddrUnsafe` with an
  object's address, or a boxed scalar's word (`lean_box(n) = 2n+1`).
  lean2rr does not emulate it: a translated program must give the same
  results as natively when they do not depend on pointer identity, raw
  addresses or sharing, which only unsafe or implementation-level APIs
  observe (`ptrAddrUnsafe` and what is built on it, `isExclusiveUnsafe`,
  `dbgTraceIfShared`, `ShareCommon`). `ptrAddrUnsafe x` (`addrOf`) takes
  `x` in its own representation (it is not converted for the call) and
  answers:
  - a heap value (a record, a function value, a `Box`, a string, an
    array, a reference, a thunk or task, a runtime handle):
    the address of its cell, whatever its count (`l2r_ptr_addr_rec`,
    `l2r_ptr_addr_obj`); a nullary constructor of a shared enum: its
    immediate;
  - a `Nat` or `Int`: its own word, which is native Lean's (§5.1): the
    boxed scalar `2n+1` when small (a `Nat` below 2^63, an `Int` in the
    `int32` range), else the pointer to its big number object;
  - `UInt8/16/32`, `Char`, `Bool`, an enumeration: the boxed scalar's
    word `2n+1`;
    `Unit` and erased values in typed code: `1` (in uniform code an erased
    value is a `Box`, the boxed unit, which answers its `Box` cell);
  - `UInt64`, `Float`, `Float32`: their bits;
  - a `[value]` struct: its field's;
  - a value of a type `addrOf` does not know: a number answered only once
    (`l2r_addr_fresh`: even, in [2^62, 2^63), so never a word or a
    pointer).

  `ptrEq` compares these words (it inlines to `ptrAddrUnsafe`),
  `ptrEqList` applies `ptrEq` element by element (it is recursive and not
  inlined; `ptrEq` is), and `withPtrAddr` passes one on; none of them can
  crash. For two values alive at the same time, equal words mean the same
  cell or equal values, so `ptrEq` answering `true` still means equal
  values, which the code using it as a shortcut for equality needs
  (`Array.mapMono`, `List.mapMono`, `withPtrEq`, `ShareCommon`'s tables:
  "not equal" is safe there). Every caller in `Init` and `Std`
  (`Array.mapMonoM`, `List.mapMonoM`, `ptrEqList`, `withPtrEqUnsafe`,
  `withPtrAddrUnsafe`, `ShareCommon`) compares live variables. The
  condition fails for a temporary, whose cell a later temporary can get
  once it has died: `ptrAddrUnsafe` applied as a function value to a value
  of another representation (it sees the converted value), the parameter
  of a function that is not inlined given a converted argument
  (`addrL (convert p)`), and a polymorphic function value such as
  `{β} → β → USize`, which boxes its argument at each call. Answers
  differ from native where a value has another representation or another
  cell here: a value cast to another inductive whose layout differs
  (§5.1) is a new object, so it is not `ptrEq` to its original, nor are two
  conversions of one value; two boxings of one value are two `Box` cells; a
  function value wrapped for another representation (§5.3) is a cell of
  its own; an arm rebuilt by `fresh-rebuild` (§5.5) is a new
  cell; equal `UInt64`s, `Float`s and small numbers are `ptrEq` (natively
  each boxing of a `UInt64` or `Float` is a new cell), also through a
  generic function (`ptrEq` on `α` applied to two `Float`s: lean2rr
  instantiates the function at `Float` and compares the bits; natively it
  receives two new boxes and answers `false`; adversarial finding 4); a
  constant boxed twice is one cell (`boxed-consts`), as natively
  (`_boxed_const_N`) within one module only: native Lean caches its boxed
  constants per module (`cacheAuxDecl`), lean2rr one cell per constant for
  the whole program, so the boxings of one constant in two modules are two
  cells natively and one here; and in the body of a constant (which runs
  once) lean2rr boxes a constant in line, a new cell each time, where
  natively it is the module's cell. So code that stops
  only when `ptrEq` says a step returned its argument (a fixpoint over
  values that cross representations) can take more steps than natively.
  `ST.Ref.ptrEq` (`IO.Ref.ptrEq`) stays real identity: a reference is never
  converted (§5.1), and it compares the addresses of the references'
  records (`l2r_ptr_addr_rec`), whatever representation each side is seen
  at. Sharing is not emulated either: `isExclusiveUnsafe` answers `false`,
  `shareCommon` shares nothing, and `dbgTraceIfShared` reads the cell's
  count, which conversions and lean2rr's own copies can make differ from
  native.

---

## 10. Known divergences and unsupported features

Where a translated program can behave differently from its native build.
Each item says what differs and when.

**Unsupported programs**
- *Module names*: a program module named `Init.*`, `Std.*`, `Lean.*`,
  `Lake.*` or `L2RShim.*` (natively allowed when the program does not
  import the toolchain's module of that name) is rejected, as is a
  directory `L2RShim` on the search path: lean2rr takes such modules for
  Lean's library or its own shim (constants evaluated lazily, only
  `initialize` declarations run at startup, `unsafe` code trusted, §5.1,
  §5.12). A module of those names is the library's when its files
  (`.olean`, and the `.olean.server` and `.olean.private` parts) are the same files as
  those of the module of that name in the library of the toolchain
  lean2rr is built with (or in the shim directory), reached by any path: a
  symbolic link, hard links or a copy are accepted. lean2rr reads that toolchain's
  library (last on the search path, after `LEAN_PATH`), whatever
  toolchain the working directory's `lean-toolchain` names.

**Evaluation and effects**
- *Dictionary rebuilding* (§2.4): lean2rr specializes a callee on every
  static dictionary, also where Lean's specializer does not (an `Inhabited`
  instance, the class being `weak_specialize`; a `@[nospecialize]`
  function; an instance argument that a recursive call changes). Instance
  code, and pure computations that take the dictionary, can then run more
  or fewer times than natively: the code that builds the dictionary is
  copied into the callee and runs there, and a call that passes the
  dictionary on (`traced "A"` with `traced [Inhabited α]`, a `panic!` in a
  generic `firstOr [Inhabited α]`) can become a closed term of the
  instance, run once, where natively it runs at each call. Lean allows
  this: it treats `dbgTrace` and `panic` as pure, and its specializer makes
  the same closed terms where it specializes (natively, `@[specialize α]`
  on the two generic helpers of round 7's FClosed2, an annotation that only
  affects performance, turns its 4 panics into 2, as under lean2rr). As a
  cost, a dictionary built by an instance function applied to static
  arguments (`instance [Inhabited α] : Inhabited (Wrap α) := ⟨expensive
  default⟩`), natively a value the caller computes once, can be recomputed
  at each call of the callee. A constant that is more than a dictionary of
  functions (one that calls a function or allocates data: a literal, a
  record, a thunk) is not part of a static dictionary, so it is evaluated
  once, as natively (test `RtDictConst`). Visible through traces or panics
  in instance code or in such calls, or as extra time.
- *Tasks* run on one thread, on lean-runtime's scheduler (§5.14), which
  picks one of native's schedules; its documented differences hold
  (lean-runtime's `docs/sched.md`, "Schedules that depend on the machine's
  speed", "The limits of one thread", "Known differences from native",
  LSCHED-01). Contexts never run in parallel and switch only when one
  blocks or at an effect or polling point, to what natively would have run
  by then (in a program that creates tasks every 1000th `ST.Ref` read is a
  polling point, §5.14 "References"), a context that computes without
  these delays the others, and `IO.waitAny` does not pick
  the fastest task. lean-runtime's pure-task rule defers pure tasks a
  worker would start (they run when needed, polled, at exit or when nothing
  else can go on). `IO.getTID` inside a task is main's thread id plus the
  number lean-runtime gives the OS thread the code natively runs on (a
  pool task its emulated worker's, a dedicated task a new one), as
  distinct from main's as a worker's.
- *Startup order of unrecorded constants* (§5.12): a constant that Lean
  compiled to no IR-only declaration although its value calls a function
  (a callee whose type is not syntactically a function, such as
  `def F := Nat → Nat`; a value whose closed term an earlier declaration
  made; a module with `set_option compiler.extract_closed false`) is
  placed by the program's structure alone. It starts in another order than
  natively when it is a member of a `mutual` block whose members do not use
  each other (natively the helpers of all members first), one of the
  made-up names of one macro quotation (here by name), or a name made by a
  recursive macro that expands the rest before its own definition (here
  in the order of the macro scopes). The `.olean` does not record these
  orders. Visible only when such constants trace or panic.
- *Compiler options of the program's modules* (`compiler.small`,
  `maxRecInline`, …) are not recorded in the `.olean`, so lean2rr runs
  Lean's passes with the defaults (`compiler.extract_closed` shows in the
  record of closed terms and is followed, §3). The recursion limit
  (`maxRecDepth`, which large literals need raised) is effectively
  unlimited in lean2rr, bounded by its stack (1 GiB, as for Lean's own
  compiler, set by `scripts/l2r.py` through `LEAN_STACK_SIZE_KB`): a
  60000-element list literal needs more than 64 MiB, and a 100000-element
  array literal translates. Only lean2rr's main thread, which runs
  everything, has that stack; it gives the other threads Lean's runtime
  starts (task workers) 64 MiB, so that lean2rr fits an address-space limit
  (`ulimit -v 16000000`) on such inputs.
- *Merging after erasure* (§2.3): Lean's mono `cse` merges calls of one
  declaration at different type arguments whose value arguments agree after
  erasure, and runs them once; lean2rr does too, with the earlier call's
  instance or with the instance at `lcAny`, except in these shapes, where a
  trace or panic in the calls prints another number of times (test
  `RtCseApart` records both outputs in expectation files):
  - the calls cannot share an instance: the earlier call's result does not
    serve the later one, and the instance at `lcAny` is not possible,
    because a type argument that differs is a type former, or an argument
    of the earlier call does not serve at the type of the argument it
    replaces (the earlier call's `⟨tagger n⟩ : Fn`, a `Nat → Nat`, for the
    later call's `String → String`), or the group is closed and the base
    test refused it (`mkO 3 : Option (α → α)` in `one` at `Nat` and in
    `both` at `Nat` and `String`: natively `both` shares `one`'s closed
    term, one trace; lean2rr runs `both`'s calls apart, two traces, as
    before): both calls run;
  - a closed call that takes the instance at `lcAny` because the base test
    aligned it, and whose result type hides the type argument in a field
    (`Foo α` with a field `(b : Bool) → if b then List α else Unit`): it is
    not the closed term of the same call at the earlier call's types in
    another function, which natively and on the base it is: it runs once
    more;
  - a call that Lean's `cse` finds in the scope of the other only after
    its later passes moved the code (a call inside a local function merged
    with one outside it, where Lean inlined the local function first; a
    call in a join point merged with one in a branch that jumps to it,
    where Lean inlined the join point into that branch): both run.
- *Running out of memory*: lean2rr ends every failed allocation, including
  a big number's limbs (one block allocated by leanrt since the one-block
  layout; only `pow`, `gcd` and decimal conversion go through GMP's own
  allocator), with `INTERNAL PANIC: out of memory` and exit status 1 after
  flushing standard output. Natively the end depends on the site: a Lean
  object gives the same `INTERNAL PANIC: out of memory`, exit 1; GMP's
  limbs give `GNU MP: Cannot allocate memory (size=N)` and an abort (status
  134, buffered standard output lost); `IO.FS.Stream.getLine` gives a C++
  `bad_alloc` (134). Since the two builds use different amounts of memory,
  they also run out at different points.
- *Build time*: rrc compiles about 80 small functions per second; a program
  with thousands of constants (each an initializer and an accessor, plus its
  closed terms) takes minutes to build where native takes seconds.
  Polymorphic recursion through type functions (monad transformer towers)
  makes hundreds of representations of a few function types, with
  conversions between them, and several rrc costs grow superlinearly on
  such code. The driver turns closure devirtualization off
  (`--no-closure-wpd`: it prints each closure's result type, every named
  type expanded, at every vtable and indirect call site; no classic
  benchmark changes by more than 1%, since lean2rr dispatches function
  values itself; Reussir issue 10, a cost), and lean2rr keeps the
  conversions, unboxings and the applications of wrapped and uniform
  function values out of rrc's MLIR inliner (§5.3; issue 20, a cost). The
  towers of the adversarial rounds then build in 15 s to 2.5 minutes and at
  most 3 GB, the whole build (a single `StateT` tower used at `IO`: 21 s,
  0.4 GB, where it did not build in 30 minutes; five towers in one program:
  70 s, 1.5 GB, where they took 15 minutes and 7.5 GB). rrc's costs also
  grow faster than linearly in the depth of nested matches (reuse across
  calls; every IO bind nests one) and in the length of straight-line code on
  `Nat` (Reussir issues 16 and 17, costs). So after lowering, a function with a
  tail path 32 matches or `if`s deep, or 256 `let`s long (a long `main`, a
  3000-arm literal match, a long `do` block), or with a `let` whose value is
  that deep or long, is cut (`Outline`): once a tail path is 8 levels deep or
  64 `let`s long, its rest becomes a function of the variables it uses,
  called in tail position; a value that deep or long comes from a function
  of the variables it uses. A recursive function keeps its loops: a rest
  that holds a tail call of the function's cycle returns what to do, a
  value of a generated enum `L2RStep_k` (`done(v)`, or one variant per
  function of the cycle, with its arguments), and the function matches it
  and makes the tail call itself; a cycle of tail calls through the parts
  would not always be a sibling call and would use stack per iteration.
  Such a loop allocates a step per iteration, only in functions this long.
  Ordinary functions are below the bounds; the classic corpus only has
  some `main`s cut. rrc also copies a wildcard arm into every constructor
  it covers and expands, in each copy, the release of every value the arm
  holds as an in-line match over its variants; a two-scrutinee match on an
  inductive with N constructors (a derived `BEq`, `DecidableEq` or `Ord`)
  became N^3 code (40 constructors: a 9-minute build). So such an arm
  releases the values of wide enums (8 or more constructors) that it holds
  and does not use through one out-of-line call (`l2r_sink`, kept out of
  rrc's inliner): the same release at the same point (40 constructors: 27
  s). A 2000-line `main` builds in about two minutes and
  2 GB, a recursive IO function of 2000 statements in about 70 s and
  1.5 GB, a recursive function with a 3000-arm match in 80 s. rrc
  compiles each generic runtime function instantiated at a type with its
  own rustc run (§5.1). `Outline`
  itself takes lean2rr time quadratic in the length of a tail path: each
  cut computes the free variables of the whole rest of the path
  (`partParams`). A function made of 1600 matches in a row, each holding
  the next, took 20 s (when duplicated join points made it that long,
  §5.6 J1'); computing the free variables bottom-up once, during the walk,
  would make it linear.
- *Casts that natively read an address* (§5.1): an object read as a word
  (`unsafeCast` of a constructor with fields, a string, an array, a closure
  to `Nat`, `UInt8`, an enumeration, ...) natively gives its address
  shifted, different on every run; lean2rr gives a deterministic word
  with the properties every address has (nonzero, a multiple of 4, far
  above any constructor index: `2^44 + 8i` for constructor `i`, `2^44`
  otherwise), and a big `Nat` or `Int` the low bits of its value, so only
  results that depend on the address itself differ. A `Nat` from 2^31 to
  2^63 cast to `Int` is natively not a valid small `Int` (results then
  depend on the operation); lean2rr keeps its value. Casts with no native
  value panic (`INTERNAL PANIC: unreachable code has been reached`, exit
  1), where native Lean crashes or reads garbage: a word read as a
  constructor with fields or as a string (a number used as an address), a
  constructor read as another inductive's constructor that has fields its
  source does not have, a `UInt64` cell read as `Nat`; and, through a
  `Box` only, a cast between inductives whose constructors do not all
  correspond (another number of constructors), which typed code converts
  (§5.1). Also out of reach: a cast that reads part of a scalar
  cell (a `Float` or `UInt64` read as `Float32`) or a record of scalars read
  as a `UInt64` (natively its data; here an address stand-in) or the
  reverse panic or differ, and a value cast to `Bool` or an enumeration
  outside its range (a byte 7 read as `Bool`) is normalized (`7 != 0`, the
  last constructor) where natively the byte survives a cast back. A cast
  between `Float` and `UInt64` copies the bits, NaN payloads included; the
  sign of a NaN an operation produces is unspecified, so a NaN computed by
  constant folding (`-(0.0 / 0.0)` in the source) can have the other sign
  than natively, visible only through such a cast (`Float.toBits`
  canonicalizes NaN). A cast between `Float32` and `UInt32` copies the bits
  too; natively it crashes (a boxed `UInt32` is a tagged scalar, a boxed
  `Float32` a cell).
- *Pointer identity and sharing* (§9) are not preserved: `ptrAddrUnsafe`
  answers the address of a value's cell in its own representation, or a
  word computed from a scalar's value, so `ptrEq`, `ptrEqList` and
  `withPtrAddr` can answer otherwise than natively wherever a value has
  another representation or another cell here (a value cast to another
  inductive whose layout differs and its original, two conversions or two
  boxings of one value, a wrapped function value, an arm rebuilt by
  `fresh-rebuild`), and equal `UInt64`s, `Float`s
  and small numbers are `ptrEq`, also through a generic function, which
  lean2rr instantiates at the type (two `Float`s: natively two new boxes,
  `false`). `ptrEq` answering `true` still means
  equal values, and `ST.Ref.ptrEq` is exact. `dbgTraceIfShared` reports
  lean2rr's counts (below, Runtime).
- *Order of releases in one free*: when a value holding several resources
  is freed at once (handles closed, and so flushed; promises resolved, or
  for a resolved promise its task's value released), native Lean releases
  them last pushed first: an array's last element
  first (after a first pass that decrements every element in index order,
  so an element held twice is freed at its last index:
  `RtArrayDupFreeOrder`), a nested array's elements before the elements
  before it, a record's last field first. Here the runtime's containers (`leanrt::drop`)
  and Reussir's drop glue for records (local patch 13-b) push what they
  free on one stack of pending work per thread, so the order is Lean's
  inside every free that starts at a container (an array, a reference, a
  thunk or task cell), through any records (tests `RtDropOrder`,
  `RtDropOrderRec`; with Reussir patch 13-d, which scripts/l2r.py
  requires, also a record field before a container field below the first
  record: `RtNestedArrayFreeOrder`), and mostly below the first cell of a
  free that starts at a record. An element of an array, a reference or a
  thunk or task value is a box (rule 1): the last release of a boxed
  record runs inside a free of leanrt's worklist, so a record replaced in
  an array (`Array.set!`) is freed in Lean's order too. That first cell is the difference. When user
  code drops a record by itself (a list, tree or structure of handles), Reussir's
  inline release in the user's function releases its fields in field
  order, each completely before the next. Natively the order depends on
  where the value is dropped: where Lean's code knows the constructor
  (`lean_dec_ref_known`, e.g. a structure it has just built), the fields
  go in field order too, each completely; elsewhere (`lean_dec`) they go
  last first. lean2rr's code does not drop values where Lean's does: where
  Lean borrows a parameter and drops the value in the caller, lean2rr's
  function takes the value and releases it as it destructures it. So a
  value dropped by itself can come out in the other order. A value of a
  parameter's type (a `List α` element, a field of type `α`) is a box
  (rule 1), which Reussir does not push as it pushes a record: it calls
  the box's drop, which releases the payload at once, inside a free of its
  own, when no free runs (`any::release_last`). Reussir's release of the
  first cell also releases the members of a record member it frees (the
  second cell) before it drains the stack of pending work; from the third
  cell on, members are pushed. So the boxes of the first two cells come
  out in field order and the rest last first: a `List IO.FS.Handle`
  `L0 … L7` dropped by itself closes `L0 L1 L7 L6 … L2` (natively
  `L0 L7 … L1` where Lean knows the constructor, `L7 … L0` elsewhere),
  and `{inner := ⟨a, b⟩, arr := #[c, d], opt := some e}` over handles
  closes `a b d c e` (natively `e d c b a`) (test `RtDepDropOrderBoxed`,
  with expectation files; while a box was the record enum `L2RBox`, the
  list closed `L0 L7 … L1` and the structure `b a d c e`). A tree of
  handles closes its left subtree before its handle and its right
  subtree. No fixed
  order of the fields in Reussir's releases matches both cases. Reversing
  it was tried: that fixes these cases but breaks the field-order ones and
  the order inside containers. One case below the first cell also differs:
  a record that the first cell holds is released through its drop function
  while no free runs, and that function frees a container field (an array,
  a reference, a thunk) as soon as it reaches it, before the record fields.
  So a structure `{a : Array Handle, l : List Handle}` as the field of a
  monomorphic list type dropped by itself closes `A1 A0 L1 L0` (natively
  `L1 L0 A1 A0`). In a `List` the structure is a box's payload, released
  inside a free of the runtime, so it closes `L1 L0 A1 A0` as natively
  (with `L2RBox`, `A1 A0 L1 L0`). An array set or
  pop that removes the last reference to a record frees it inside a free
  the runtime starts, so its fields go last first, as `lean_dec` frees them
  in `lean_array_uset` and `lean_array_pop` (switch step 10, review
  RS10-01; tests `RtArraySetFreeOrder`, `RtArrayPopFreeOrder`); before,
  the record's own release freed them in field order. With an array of
  boxes (rule 1) that record is a box's payload, freed the same way
  (`any::release_last`, one pending cell).
- *Release time of borrowed parameters* (§5.8): emulated for values that
  may hold a resource, with Lean's inference run on lean2rr's monomorphic
  instances: where Lean infers a polymorphic declaration or one of its own
  specializations differently from lean2rr's instance of it, the release
  time follows the instance. A resource captured in a closure or a thunk
  is not looked into (released at its last use). In a program that
  creates resources, a value of uniform type (`Box`) passed owned to a
  borrowed parameter is kept until the call returns: one more increment
  and release per such call.
- *Order of panics in pure code*: when several pure computations panic
  (`get!` on a short array, an `assert!`), their messages can come out in
  another order than natively, because Lean's closed-term extraction may
  group them differently in lean2rr's instances. stdout and results are the
  same.
- *Stack depth* in general: frame sizes differ from native. lean2rr adds
  no recursion of its own, except in the conversion of a value cast to
  another inductive whose layout differs (§5.1, recursive through
  recursive fields; values of one inductive are never converted): the
  `Array.mk`, `String.mk` and `String.ofList` list folds are tail-recursive
  loops, and the walk of a closed term for its tasks (§5.14) is a loop over
  a work list, so folding a list of 10⁷ elements, or walking
  a closed term 300000 cells deep through its first field, works at an 8 MB
  stack (`LEAN_STACK_SIZE_KB=8192`) as natively (test `RtPersistWalk`).
  The walk's work list and set of visited cells are heap memory while it
  runs (natively a stack of pointers): a few tens of bytes per cell of a value
  walked while a task is unfinished. Dropping a deep value:
  Lean frees iteratively, through a stack of objects to free. The
  runtime's containers (arrays, references, thunk and task cells:
  `leanrt::drop`) do the same: a container freed while another is being
  freed is pushed on a stack of pending work instead, which the outermost
  free empties; so a value deep through containers, with records in
  between (a tree whose children are in arrays, a record → array → record
  chain, a chain of thunks or tasks), is freed at a bounded depth.
  Records are freed by Reussir's drop glue, which with the local patches
  releases the last record member being freed in a loop (13-a) and pushes
  the other record members being freed on the same stack (13-b), so a
  value deep through records too is freed at a bounded depth: a list, a
  snoc list, a binary tree deep along its left child whose right children
  are fresh nodes, a rose tree in uniform code (test `RtDropGlue`, 10⁶
  levels at an 8 MB stack). The depth at which
  `Stack overflow detected. Aborting.` (exit 134) happens is not native's,
  in either direction (the report itself is, in every thread: §5.11).
  Tasks run on lean-runtime's contexts, each with a stack of Lean's size
  (1 GiB, or `LEAN_STACK_SIZE_KB`), as native task workers have.
- *Stream redirection* (`IO.setStdout`, `setStderr`, `setStdin`,
  `IO.FS.withIsolatedStreams`) is translated: the current streams live in
  cell slots, and panics, `dbgTrace` and `timeit` write through the current
  stderr stream (`l2r_stderr_put`), as natively, and per thread as
  natively: a task, and `main` after the initializers, start with the
  process's streams (§5.14). One order differs: at a thread's end its
  streams are dropped in a fixed order (stdin, stdout, stderr), where
  natively the thread's finalizers run in the reverse order of each
  stream's first use on that thread; it shows only when the drop of one
  stream runs code that uses another of the thread's streams (a promise
  whose `sync` dependent prints), or when two drops have effects whose
  order shows (two handles of one file) (hunt HST-03).

**Cost** (time and memory, not results)
- *No borrowed parameters* (§5.8, §7): a parameter Lean borrows is owned
  here, so a traversal that keeps the nodes it visits (an `Expr.replace`
  over a DAG that replaces nothing) increments and releases the fields of
  every node it keeps, and every `ptrEq` operand: 1.5x native on such a
  traversal (adv4 RP4-09).
- *Casts between layouts that differ* (§5.1): a value cast to another
  inductive whose layout differs (a field holding an `Int` where the
  source's holds a `Nat`) is rebuilt, O(size), at each such cast, where
  natively the cast is free. (A value of one datatype, array, thunk, task
  or reference is never converted: one type each.)
- *Boxes*: a box is one word (`LAny`, as Lean's `lean_object*`): a small
  `Nat`, a `Bool` or an enumeration is a scalar in the slot, as natively;
  a `Float` and a `UInt64` from 2^63 are cells, as natively; a `[value]`
  value that is not a struct of one field is wrapped in an `ElemBox` cell.
  Once-cell values and polymorphic extern
  arguments (other than arrays' elements) whose type cannot cross the FFI
  boundary (`[value]` tuples, closures) are wrapped in an `ElemBox` cell,
  one allocation each. `ByteArray` and `FloatArray` are unboxed, as
  natively; `Array UInt64` and `Array Float` hold boxes.
- *Reads take their container owned* (Reussir has no borrowed FFI
  parameters, §9): every array or string read is an increment by the caller
  and a release in the inlined runtime function. LLVM cancels the pair when
  the increment's store reaches the release with no store or call on any
  path in between (Reussir's `rc.inc` lets it assume the old count was at
  least 1). So a read gives its reference up first, before its bounds
  check, for a view of the array, and its failing branch releases nothing;
  the prelude takes an index as its word and ends the impossible big-index
  paths instead of rejoining them; lean2rr passes a read's index in a
  `let`, so that Reussir increments the index before the container; and
  each read texture is small enough for LLVM to inline at a call site it
  judges cold (Reussir issue 36; docs/implementation/ownership.md, "Reads
  give their reference up first, for a view"; with the one-word `Box`,
  `l2r_view_take<LAny>` is not, and stays a call there: the patch that
  inlined it, 36-a, is parked). Index loops and insertion
  sort on `Array UInt64` ran at 1.2x native or better before these
  changes; with them (perf-array-reads, measured in the LLVM IR), no
  array read of lean-zip stays a call (279 did), and its LZ77 loop has 47
  count stores on its hot paths, at most 7 on one iteration (77 and 15
  before). A loop body whose slow path (a big number's arithmetic, a
  call) rejoins the fast path keeps a count store per iteration: LLVM
  reloads the count after the call. It does not cancel either when a
  structure field projected at the top of a loop body is released by the
  iteration's last read, as in Lean's `String.Slice` loops (`String.any`,
  `contains`, `toNat?`): 1.7x native (Pf4MinStrAny; 1.1x with the projection
  moved by hand to its first use); insertion sort on `Array Nat` keeps
  the count's stores and reloads it for the swap's uniqueness check: 2.1x.
- *Arrays and strings are one block each*, with headers of Lean's sizes
  (24 bytes for an array, `Array Nat`/`Array Int` included, 32 for a
  string). Until perf-rvec a generic array (`RVec`) was two allocations, a
  32-byte counted box and the element buffer: three million three-element
  `Array UInt64` rows took 186 MB, now 163 MB (native 303 MB, which boxes
  each `UInt64`), with one allocation per array instead of two. The cost
  of the single block: an array asked for with a payload of exactly
  16 MiB (a hash table's 2^21 buckets) is, with its header, past
  mimalloc's large-object limit and becomes a huge segment, which mimalloc
  purges only 100 ms after it is freed: `Std.HashMap` with 0.8M to 2M keys
  peaks up to 24% higher than with the buffer apart (hashmap 1M: 60 MB,
  51 MB before, native 64 MB; Lean's array has the same header). Six
  million three-element `Array Nat` rows take native memory
  (Pf4SmallArrs 0: 328 MB, native 330 MB), five million short live
  strings 270 MB (Pf4ManyStrs; native 352 MB). `String.toUTF8` and
  `String.fromUTF8` copy the bytes, as natively.
- *Dropping a large array of records*: the runtime decrements shared
  elements inline (as `lean_del` does natively) and frees the array
  without the stack of pending work when no element is freed; an element
  whose last reference it holds goes through Reussir's out-of-line
  `<record>_ffi_release` (`leanrt::drop`, `ReleaseElems`). The Reussir
  suite's `hash-map-heavily-shared`, which frees an old version of its
  bucket array after each update while a parked version is live, went from
  1.79x native to 1.05x with this.
- *Constants read in a loop* (a top-level `Array` or `String` table)
  test their once-cell's word on every read: one load and a test, where
  a native named constant is one load and a native closed term
  (`lean_obj_once`) two loads and a test (§5.12). The reference's
  increment stays when the read is not right before a read from the
  table (a use in between). A constant whose bits are all 0 (a computed
  `UInt64`, `Float` or `UInt8` 0, `false`) costs a second load, of its
  set flag.

**Runtime** (details in `runtime/README.md`, "Known divergences")
- Sharing is not observable: `isExclusiveUnsafe` answers `false`;
  `dbgTraceIfShared` reads lean2rr's own counts (a converted value is a
  new, unshared object, §5.1; `leanrt::is_shared`, which also reads a big
  `Nat`'s or `Int`'s count, review HL-01). It does not report a task
  that one reference holds, where natively a task that `Task.spawn` made
  is multi-threaded (its count is negative) and reported as shared;
  `shareCommon` shares nothing, and
  `ShareCommon.Object.eq` compares addresses (§9: at most the same cell;
  natively also two objects with the same fields; `L2RShim`), so an
  object converted at each call (a value cast to `ShareCommon.Object`) is
  not even equal to itself, and its hash can change.
- `IO.getNumHeartbeats` is 0; `dbgStackTrace` prints nothing; a panic's
  backtrace line is `(stack trace unavailable)`.
- Only what a walk reaches is persistent (§5.14: the cells of the types
  that can hold a task and the payloads of the boxes the walk meets, in a
  program that creates tasks) and `Runtime.markPersistent`'s argument; a
  persistent cell never releases what it holds. Anything else is released
  at its last reference once the program takes it out or stores over it:
  in a program without tasks, everything a constant's value holds (an
  initializer's `IO.Ref`'s value included); in a program with tasks, the
  value a reference or a thunk gets after the walk (natively not
  persistent either). So in a program without tasks a file handle that an
  initializer stores in an `IO.Ref` closes when the program sets the
  reference to `none`, as Lean's documentation says of a handle's last
  reference (`Init/System/IO.lean`): its buffered bytes are written then,
  and a `flock` it took is released. Natively the initializers mark their
  values persistent, so that handle stays open until the exit (glibc
  writes its buffer then). Example: an initializer writes "from-init" to a
  new handle and stores it in an `IO.Ref (Option IO.FS.Handle)`; `main`
  sets the reference to `none` and reads the file: native reads "",
  lean2rr "from-init" (in a program with tasks "", as natively: the walk
  after the initializer marks the `some` cell, or the handle when the
  reference holds it directly; tests `RtPersistInitHandle`,
  `RtPersistInitHandleDirect`); at the exit the file holds "from-init" in
  both (hunt HSG-02; docs/implementation/startup/constants.md). A marked
  cell with 2^30 references or more (8 GiB of pointers to it) has a count
  of 2^31, which leanrt takes for a nullary variant's dummy box; an
  unmarked one at 2^31 references.
- An internal panic (`INTERNAL PANIC: ...`, the end of the program) in a
  program that has made a task, a promise, a timer or a watch writes its
  line straight to descriptor 2, without waiting for stderr's lock
  (lean-runtime's `io::panic`, its docs/panic.md row 10; switch step 8;
  the test is process-wide, so on every thread): it does not wait for a
  write to stderr in progress by another context (a task or `main`
  suspended in the middle of it, on a full pipe), and, from the thread
  that drains `IO.Process.output`'s stdout after a failure (its
  out-of-memory end), for any write to stderr in progress, `main`'s
  blocked write included. The line then lands inside that write, where
  natively it comes after it (the writing thread holds C's `FILE` lock).
  The bytes are the same, and the exit then writes the rest of the other
  write. Without tasks the line waits for a write in progress, as
  natively. The lock is skipped because the cooperative lock allocates
  and may switch contexts, which the out-of-memory end must not, and a
  plain lock off the scheduler's thread could wait for good for a context
  suspended in the middle of its write, which only that thread resumes
  (review RS8-01: a hang ranks above the place of a line in an error
  path).
- Child processes (§5.8): code that reads one of a child's pipes in a task
  while it reads the other (as `IO.Process.output` does natively, stdout
  in the task; its glue here reads both together) deadlocks if the child
  writes more than a pipe holds to the task's pipe before closing the
  other one, since the task runs only when its value is needed. Natively `Child.pid` leaks the child, so its pipes stay open
  forever (a child waiting for end of file on stdin then hangs); here they
  are closed as usual. Natively the `Child` from `takeStdin` loses the
  `setsid` flag (LB-14, below); here it keeps it. `output` is
  lean-runtime's: its errors come in Lean's order (stderr's read or UTF-8
  error as soon as stderr is at end of file, stdout's after `wait`), and
  after a stderr failure stdout is read to its end on a thread until
  `main` returns, as Lean's task reads it. A child is started with
  `posix_spawn`, with what Lean's forked child does before `execvp`
  reproduced by lean-runtime (`io::process` lists what remains
  different).

**Runtime: Lean bugs we do not reproduce** (each judged a bug in Lean
4.34.0's runtime, listed in lean-runtime's
[docs/lean-bugs.md](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md); both translators and
lean-runtime do the right thing instead; where a runtime test shows the
difference, it pins native's output and lean2rr's in expectation files,
`NAME.native.*` and `NAME.l2r.*`. The IO ones are lean-runtime's `io`
module's behaviour, which lean2rr calls. The lean-runtime cases:
`refs/lost_update` (LB-01), `io/read_after_write` (LB-02),
`io/error_without_file_name` and `io/temp_file_error` (LB-03),
`process/take_stdin_setsid` (LB-14), `process/null_fd_leak` (LB-15),
`temp/temp_long_dir`, `temp_long_file`, `temp_long_dir_4095` (LB-16),
`process/null_open_fails` (LB-17), `process/exit_while_reading`,
`process/output_oom_both_pipes`, `process/output_drain_exit_exit` and
`_panic` (LB-29), `io/startup_fd_exhausted` (LB-30, LB-31); the task
manager's, since lean2rr runs on lean-runtime's scheduler (switch step 4):
`tasks/late_*` (LB-13: a pool task enqueued after `main` runs),
`uvloop/signal_failed_next` (LB-19), `uvloop/*_in_sync_dependent` (LB-20,
and LB-33, LB-34: a `stop` or `cancel` whose release runs a `sync`
dependent that subscribes again), the `net` cases of LB-21 to LB-28,
`tasks/dropped_promise_waiter_*` (LB-32), `tasks/big_priority_dedicated`
(LB-39); and the `float/scaleb*` rows (LB-36), `process/output_large_input`
and `taskio/output_input_while_ticking` (LB-40), `io/getline_after_error`
(LB-41), `process/failed_child_pending_stdout` (LB-42),
`io/random_overflow_fd` (LB-43), `process/spawn_late_pipe_fails` (LB-44),
`uvsys/uv_system` and `uvsys/rt_system` (LB-45), `io/append_starts_at_end`
(LB-46))
- *LB-01, a concurrent `IO.Ref.set` can be lost*
  ([LB-01](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-01-a-concurrent-iorefset-can-be-lost);
  fixed upstream in Lean 4.35): natively `lean_st_ref_get` takes the value
  out of a reference shared between threads and puts it back with an
  unconditional exchange, so a `set` from another thread that lands in
  between is undone (a task's `r.set 1`, then `IO.wait` on it, and `r`
  reads 0 again; a spin on a flag can hang). In lean2rr tasks run on one
  thread (§5.14), so every reference operation is atomic: a completed
  `set` is seen by every later `get` (`refs/lost_update`). The other half
  of Lean 4.35's fix too: `ST.Ref.modify` is `take` then `set`, and while
  its function blocks, another thread's `get`, `take`, `set` and `swap` of
  that reference wait for modify's store, in a program that creates tasks
  (§5.14, "References"; `refs/set_during_modify`, `swap_during_modify`,
  `get_during_modify`; tests `RtRefSetDuringModify`,
  `RtRefSwapDuringModify`, `RtRefGetDuringModify`).
- *LB-02, output followed by a large read on one handle*
  ([LB-02](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-02-output-followed-by-a-large-read-on-one-handle-is-lost)):
  natively a read of at least one buffer (`read 5000`)
  right after output on the same handle drops the pending output, as glibc
  resets the buffer (C11 leaves output directly followed by input
  undefined): `putStr "x"` on a write-only handle and then `read 5000`
  fails, and `x` never reaches the file; on a read-write handle the read
  returns the old contents from the start. lean2rr writes the pending
  bytes first, then reads from the cursor (and fails with native's EBADF
  on a write-only handle); if that write fails, so does the read. A failed
  seek back over read-ahead is no failed write: on a FIFO opened
  `readWrite` and read ahead, the output cannot be written, and the read
  drops it with the read-ahead and goes on, as natively, leaving `errno`
  as it was (native's direct read makes no seek). `read 0` reads
  nothing, and small reads, `getLine` and `readToEnd` already wrote the
  bytes natively. Tests `RtReadAfterWrite`, `RtStdioStdoutRead`,
  `RtFifoReadAfterWrite`, `RtFifoErrnoRestore`.
- *LB-03, an error without a file name*
  ([LB-03](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-03-an-error-without-a-file-name-can-crash)):
  natively an error of the classes `noFileOrDirectory`
  (ENOENT) and `interrupted` (EINTR) from a call that passes no file name
  crashes (SIGSEGV, exit 139, buffered stdout lost): `decode_io_error`
  dereferences the null name, for `getCurrentDir` after its directory was
  removed, for example. lean2rr raises the class's error with an empty
  file name (`noFileOrDirectory "" 2 "no such file or directory"`) for
  every such call: `getcwd`, `waitpid`, `kill`, `flock` and the handle
  primitives (`fflush`, `fseek`, `ftruncate`, `fread`, `fwrite`, getline,
  `fputs`), reading `/dev/urandom` (`IO.getRandomBytes`), and the
  libuv-based ones (`createTempFile`, `createTempDir` with `TMPDIR` naming
  a missing directory). Test `RtErrorNoFileName`.
- *LB-15, a `null` stream leaks a `/dev/null` descriptor*
  ([LB-15](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-15-a-null-stream-leaks-a-devnull-descriptor-into-the-program)):
  natively the forked child opens `/dev/null` for each `null` stream
  without close-on-exec and never closes it after `dup2`, so the program
  (and every program it starts) has one more descriptor on `/dev/null` per
  `null` stream, at the lowest number free in the child; a program that
  audits its descriptors reports it. `IO.Process.output` without input
  spawns with `stdin := .null`, so every program it runs gets one. lean2rr
  opens `/dev/null` in the parent, close-on-exec, before the fork, and the
  child `dup2`s it: the program starts with its standard streams and what
  the parent inherited, as with `piped`. Test `RtProcessNullFd`.
- *LB-17, a `null` stream falls back to the parent's stream*
  ([LB-17](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-17-a-null-stream-falls-back-to-the-parents-stream-when-devnull-cannot-be-opened)):
  natively a failed `open("/dev/null")` in the forked child (the parent's
  descriptors exhausted: `EMFILE`) is ignored, the `dup2` fails, and the
  program runs on the parent's own descriptor: a `null` stdout writes on
  the parent's standard output, a `null` stdin reads the parent's input
  (`IO.Process.Stdio.null`: "The stream should be empty"). In lean2rr the
  parent's failed open is the spawn's error, as a failed pipe is
  (`resource exhausted (error code: 24, too many open files)`), and the
  pipes the spawn made are closed again (a failed `pipe2` leaks the
  earlier ones, as natively). Because the parent opens `/dev/null`, a
  spawn in which some `null` stream follows a piped one needs exactly one
  more free descriptor than natively (one in all, however many such
  streams), where the child has closed the pipe's other end before its
  open: with a piped stdout, `stderr := .null` and two free descriptors,
  the spawn succeeds natively and fails with `EMFILE` here. Any other
  spawn needs as many free descriptors as natively. Test
  `RtProcessNullOpenFails`.
- *LB-14, after `takeStdin`, `kill` no longer reaches a `setsid` child's
  group*
  ([LB-14](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-14-after-takestdin-kill-no-longer-reaches-a-setsid-childs-group)):
  natively the child `takeStdin` returns loses its `setsid` flag, so
  `kill` signals the pid alone and the group survives. lean2rr's `Child`
  keeps the flag (`Lower/Process.lean`), and lean-runtime's process object
  too: `kill` uses `killpg`.
- *LB-16, an over-long temporary directory aborts `createTempFile` and
  `createTempDir`*
  ([LB-16](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-16-an-over-long-temporary-directory-aborts-createtempfile-and-createtempdir)):
  natively a temporary directory of 4083 to 4095 bytes fails an assertion
  (status 134). lean2rr tries the creation and raises the system's
  `ENAMETOOLONG` (`invalid argument (error code: 36, name too long)`).
- *LB-29, `exit` waits for a stream held by a blocked reader*
  ([LB-29](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-29-exit-waits-for-a-stream-held-by-a-blocked-reader-so-an-internal-panic-or-ioprocessexit-can-hang)):
  natively an internal panic or `IO.Process.exit` while another thread is
  blocked reading a handle waits for that read, forever if it never
  returns. lean-runtime's exit skips a stream whose holder is blocked
  reading it. In lean2rr no context holds a stream across a switch (its
  tasks share one thread), so the exit never waits for a reader.
- *LB-30, LB-31, startup when the event loop's descriptors cannot be made*
  ([LB-30](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-30-when-libuv-cannot-create-the-event-loop-startup-dereferences-a-null-loop),
  [LB-31](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-31-when-libuv-cannot-create-its-global-signal-lock-pipe-startup-aborts)):
  natively a descriptor limit that leaves no room for libuv's loop crashes
  every program before `main` (SIGSEGV, 139, at `ulimit -n` 8 to 10) or
  aborts it (SIGABRT, 134, at 4 to 7). lean-runtime's startup constructor
  (feature `startup-fds`) ends it with `INTERNAL PANIC: Failed to
  initialize event loop: too many open files`, status 1. Test
  `RtStartupFdExhausted`.
- *LB-36, `Float.scaleB` with an `Int` outside the C `int` range*
  ([LB-36](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-36-floatscaleb-and-float32scaleb-with-an-int-outside-the-c-int-range-give-00-for-a-nan-an-infinity--00-and-a-negative-value)):
  natively the big-`Int` branch of `Float.scaleB x i` and `Float32.scaleB`
  returns `+0.0` when `x == 0` or `i < 0`: a NaN, an infinity scaled
  down, `-0.0` and a negative value scaled down lose their value or sign
  (`(-1.5).scaleB (-(2^40))` is `0.000000`), with a step between -2^31 and
  -2^31 - 1. lean2rr passes the `Int` saturated to `i64`
  (`l2r_int_sat_i64`) to lean-runtime's `scaleb`, `scalbn` of the exponent
  clamped to the `int` range: `x * 2^i` for every `Int` (`-0.000000`
  there). Test `RtFloatScaleBBig`.
- *LB-39, a task priority cut to 32 bits*
  ([LB-39](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-39-a-task-priority-is-cut-to-32-bits-232---1-runs-the-task-at-once-on-the-spawning-thread-and-232-to-232--8-go-to-the-pool)):
  natively `Task.spawn`, `Task.map`, `Task.bind`, `IO.asTask`,
  `IO.mapTask` and `IO.bindTask` take the priority modulo 2^32: 2^32 - 1
  runs the task at once on the spawning thread, as a `sync` task (a
  `Task.get` in it prints the `sync` task panic), 2^32 to 2^32 + 8 go to
  the pool, and a big `Nat` (2^63 or more) gives the bits of its pointer.
  lean2rr passes the whole priority, one of 2^64 or more as `u64::MAX`
  (`Lower/LazyGlue.lean`, `prioOf`), and lean-runtime makes every priority
  above 8 a dedicated task, as `Task.Priority`'s documentation says.
  Tests `RtTaskPrioBig`, `RtTaskPrioSync`.
- *LB-40, `IO.Process.output` with an input waits for good*
  ([LB-40](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-40-ioprocessoutput-with-an-input-waits-for-good-once-the-child-fills-a-pipe)):
  natively `output` writes and flushes all of the input before it reads
  the child's output, so a child that writes while it reads (`cat` with
  more input than a pipe holds) and the program wait for each other for
  good. lean-runtime's `output` writes the input while it reads both
  output pipes, and closes the input's pipe once every byte is in; a
  write error (`EPIPE` once the child has closed its standard input) still
  ends `output` at once, as Lean's `putStr` error comes first.
- *LB-41, after one stream error, every later `getLine` fails*
  ([LB-41](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-41-after-one-stream-error-every-later-getline-fails-and-loses-its-line)):
  natively a failed read or write on a handle (a write on a read-only
  handle, a non-blocking descriptor's `EAGAIN`) sets its error indicator,
  and every later `getLine` reads its line, then fails with whatever
  `errno` holds: the line is lost. lean-runtime's `getLine` clears the
  indicator first and reports only its own error; `read`, `putStr`,
  `flush` and end of file are as natively. So no Lean program reads a
  stale `errno`. Tests `RtErrnoRealpath`, `RtFifoErrnoRestore`,
  `RtFiles2`.
- *LB-42, a child that cannot start writes the parent's pending output
  again*
  ([LB-42](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-42-a-spawn-whose-child-cannot-start-writes-the-parents-pending-standard-output-a-second-time)):
  natively a child that cannot execute its program or enter `cwd` writes
  its copy of the parent's pending standard-output buffer before its
  message (`std::cerr` is tied to `std::cout`), so the bytes appear twice,
  and `IO.Process.output` returns them as the child's output. In lean2rr
  the child writes none of them. Test `RtProcessSpawn` (`out ""`,
  natively `out "pending\n"`).
- *LB-43, LB-44, descriptor leaks*
  ([LB-43](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-43-iogetrandombytes-of-a-size-whose-array-would-overflow-leaks-a-descriptor),
  [LB-44](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-44-a-spawn-that-fails-at-a-later-pipe-leaks-the-pipes-made-before-it)):
  natively `IO.getRandomBytes n` with an `n` whose array would overflow
  fails with `ENOMEM` and leaves `/dev/urandom` open, and a spawn that
  fails at a later `pipe2` leaves open the pipes it made. lean-runtime
  closes them.
- *LB-45, `Std.Internal.UV.System` cuts ids and priorities to 32 bits*
  ([LB-45](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-45-stdinternaluvsystem-cuts-process-ids-group-ids-and-priorities-to-32-bits)):
  natively `osGetPriority`, `osSetPriority` and `osGetGroup` pass their
  `UInt64` id and `Int64` priority as a C `int` or a `gid_t`: pid 2^32 is
  the calling process, priority 2^32 + 19 is 19 and accepted, gid 2^32 is
  `root`'s group. lean-runtime takes them whole: a pid outside 0 to
  2^31 - 1 is `ESRCH`, a priority outside -20 to 19 is `EINVAL`, and a gid
  above 2^32 - 1 names no group (`none`). `RtUvSysLimits`' values give the
  same answers both ways.
- *LB-46, `truncate` right after an `append` open empties the file*
  ([LB-46](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-46-truncate-right-after-an-append-open-empties-the-file)):
  natively `IO.FS.Handle.mk path .append` opens with `O_APPEND`, and
  glibc's `fdopen(fd, "a")` then leaves the cursor at 0, where
  `IO.FS.Mode.append` documents it at the end of the file: writes still go
  to the end, but `Handle.truncate` (to the cursor) deletes the whole
  content. lean2rr opens files through lean-runtime's `Handle::open`
  (`leanrt::fs::open_file`), which moves an `append` descriptor of a
  regular file to its end before `fdopen`, as glibc's `fopen(path, "a")`
  does; other descriptors (devices, FIFOs, terminals) keep native's
  cursor. Test `RtFileAppendTruncate`.
- *LB-47, `EBADMSG` is a protocol error or an unknown error*
  ([LB-47](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-47-ebadmsg-is-a-protocol-error-or-an-unknown-error-where-ioerror-documents-an-inappropriate-type)):
  natively `EBADMSG` (a file system's checksum failure) is
  `protocolError` from a C library call and `otherError` from a libuv
  call, where `IO.Error` documents `inappropriateType`. lean-runtime's
  decoders give `inappropriateType` on both paths, with native's details.
  No program can cause it on demand (a corrupted file system);
  lean-runtime's decoding table checks it.
- *LB-50, a `shutdown` during a `connect` resolves the connect `ok` before
  the connection exists*
  ([LB-50](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-50-a-shutdown-during-a-connect-resolves-the-connect-ok-before-the-connection-exists)):
  natively libuv's `uv_shutdown` makes a pending connect read the socket's
  error while the handshake goes on, and resolve `ok`. lean-runtime's
  connect stays pending until the connection exists or fails, and the
  shutdown queued behind it (LB-28) then shuts it. Case
  `net/shutdown_during_slow_connect`.
- *LB-51, `waitReadable` resolves `true` at the end of the stream*
  ([LB-51](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-51-waitreadable-resolves-true-at-the-end-of-the-stream)):
  its docstring and Lean's own end-of-file branch say `false`; lean-runtime
  gives `false` there, as LB-26's `recv? 0` decides. Case
  `net/wait_readable_eof`.
- *LB-52, a wait in a pool task wraps the pool's limit to 0 when
  `LEAN_NUM_THREADS` is 2^32 - 1*
  ([LB-52](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-52-a-wait-in-a-pool-task-wraps-the-pools-limit-to-0-when-lean_num_threads-is-232---1)):
  natively the raise of the limit while a pool task waits wraps an
  `unsigned`, and no worker takes a queued task while the wait lasts (a
  hang); lean2rr's single-thread scheduler counts the waiter's worker as
  free instead. Case `tasks/pool_limit_wrap`.
- *LB-11, `Nat.pow` with an exponent of 2^32 or more*
  ([LB-11](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#limits);
  this and the next five are lean-bugs.md's "Limits", implementation caps
  where Lean's definition has a value, which lean-runtime's rules compute
  wherever the result fits): natively `INTERNAL PANIC: Nat.pow exponent is
  too big`, whatever the base. lean2rr gives `0 ^ e = 0` and `1 ^ e = 1`
  for any `e`, and another base's power while `bit_len(a) * e` (exactly
  `j e + 1` bits for a base `2^j`) is at most `MAX_BITS` (LB-05), with
  native's message above it. Tests `RtInternalPanic`, `RtLiftedLimits`.
- *LB-12, `Nat.shiftLeft` by 2^32 or more*: natively `INTERNAL PANIC:
  Nat.shiftl exponent is too big` for a nonzero value; lean2rr computes the
  shift while the result fits `MAX_BITS`, with native's message above it
  (lean-runtime's rows `nat/shiftl*`, through `rows-check.sh`: the results
  have 2^32 bits, 512 MiB).
- *LB-04, `Nat.shiftRight` of a huge value by 2^32 or more*: natively
  `INTERNAL PANIC: Nat.shiftr exponent is too big` for an operand of 2^32
  bits or more; lean2rr computes the quotient (lean-runtime's rows
  `nat/shiftr.2^4294967296+*`).
- *LB-06, `ByteArray.copySlice` with an offset or length of 2^64 or more*:
  natively `INTERNAL PANIC: out of memory` (`lean_nat_to_size_t`); lean2rr
  gives the Lean definition's clamped copy (the offsets and the length
  passed saturated). Test `RtLiftedLimits`.
- *LB-05, a result too big for GMP*: natively a `Nat` of more than
  `INT_MAX` limbs makes GMP raise SIGFPE (status 136, no message, buffered
  output lost), e.g. `(2^62)^(2^32 - 1)`. Every rule whose result size is
  known first (`Nat` add, mul, pow, shiftLeft; `Int` add, sub, mul,
  negSucc) ends at once with `INTERNAL PANIC: out of memory`, exit 1, above
  `MAX_BITS` = (2^31 - 6) × 64 bits (GMP's cap less `mpz_pow_ui`'s margin
  of 5 limbs; `leanrt::big::MAX_BITS`), or with native's exponent message
  when the exponent or shift is 2^32 or more. Below `MAX_BITS`, memory that
  runs out ends where it is allocated: a block of `leanrt::big` with
  `INTERNAL PANIC: out of memory` (natively GMP's allocator prints its
  message and aborts, 134; the one-block numbers' known difference), GMP's
  own limbs in `pow` as natively. Test `RtLiftedLimits`.
- *LB-37, a capacity that cannot be reserved*
  ([LB-37](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md#lb-37-a-capacity-that-cannot-be-reserved-ends-mkempty-and-emptywithcapacity)):
  natively `Array.mkEmpty c`, `Array.emptyWithCapacity c`,
  `ByteArray.emptyWithCapacity c` and `FloatArray.emptyWithCapacity c` end
  with `INTERNAL PANIC: out of memory` for a `c` of 2^63 or more or a
  failed allocation, and with `integer overflow in runtime computation`
  for an object size above 2^64 - 1. The Lean definitions give the empty
  array whatever `c` is: lean2rr reserves nothing for such a capacity and
  gives the empty array (`leanrt::array::check_capacity`; the prelude
  releases a big `Nat`). `Array.replicate` keeps native's ends. Tests
  `RtAllocBigNat`, `RtAllocOverflow`, `RtAllocOom`.

**Runtime: Lean defects and candidates followed as native** (lean-runtime's
[docs/lean-bugs.md](https://github.com/QueClr/lean-runtime-rs/blob/main/docs/lean-bugs.md),
"Lean library definitions", "Not bugs" and "Candidates": a defect of a Lean
library definition that both translators compile as written, a behaviour
judged not a bug, and suspected bugs that wait for a verdict or a native
repro; until a verdict moves one to the list above, lean-runtime and lean2rr
do what native does, and the tests expect native's outcome; LBC-06 is the
one departure, where native builds no program at all)
- *LB-48* (a Lean library definition): `IO.FS.writeFile` and
  `writeBinFile` do not flush, so the content is written when the handle
  is released, and a failure there (a full disk, `/dev/full`) is dropped:
  the call has succeeded. lean2rr compiles the definitions, and the
  handle's release drops the error, as natively.
- *LB-49* (not a bug): `truncate` on an `append` handle with output
  pending counts the pending bytes from the end, so the flush leaves a NUL
  gap; glibc's behaviour, and `truncate`'s docstring says to flush first.
  The second line of `RtFileAppendTruncate`.
- *LBC-01 to LBC-05* (io candidates): `readDir`'s short list when
  `readdir` fails, `putStr`'s lost line when a line-buffered flush fails,
  `realPath`'s one error class, a `getLine` that drops the bytes it read
  before `EAGAIN`, and the libuv path's `otherError` for the `errno`s that
  libuv cannot name. lean2rr gets native's behaviour from lean-runtime's
  `io`.
- *LBC-06* (a compiler candidate; a lean2rr departure): natively a
  program with an `initialize` constant of function type does not link
  (the generated C calls the constant as a function it never defines), so
  there is no native outcome to follow. lean2rr builds it: it stores the
  function in the constant's cell and applies it at each use, the
  program's evident meaning.
- *LBC-07*: `Child.kill` sends `SIGKILL`, where its docstring says
  `SIGTERM`; lean2rr sends `SIGKILL`, as natively (a killed child's status
  is 137).
- *LBC-08*: `osEnviron`'s failure path returns a `String` as its
  `IO.Error`; in lean-runtime `osEnviron` cannot fail (it reads its own
  copy of the environment), so lean2rr never reaches that path.

**Compiler: Lean bugs we do not reproduce** (each judged a bug in Lean
4.34.0's compiler: the source lines, the kernel's value of a minimal
program, and a native repro that prints another value; lean2rr computes
the value that Lean's semantics, the kernel, give; a runtime test pins
native's output and lean2rr's in expectation files, `NAME.native.*` and
`NAME.l2r.*`)
- *Data after a `match` with a type or proof arm: a wrong value or a crash*
  (judged 2026-10-06; no upstream issue found). In a `match` whose one arm
  gives a type or a proof and whose other arm gives data, `toLCNF` gives
  the `cases` the join of its arms' types
  (`src/lean/Lean/Compiler/LCNF/ToLCNF.lean:670`, `visitCases`:
  `resultType := joinTypes altType resultType`), and `joinTypes?` gives
  `◾` when either side is `◾` (`Types.lean:243-245`);
  `InferType.mkCasesResultType` (`InferType.lean:321`) joins the same way
  when a later pass rebuilds a `cases`. So in
  ```lean
  def T : Bool → Type | true => Nat → Prop | false => Nat
  def f2 (b : Bool) (n : Nat) : Nat :=
    let v : T b := match b with | true => fun _ => True | false => n
    match b, v with | false, v => (show Nat from v) + 1 | true, _ => 0
  ```
  the join point after the first `match` gets a parameter of type
  `lcErased` (`jp _jp (_y : lcErased)`), and the jump from the `false` arm
  passes `n` to it. Native's `toImpure` removes a join-point parameter of
  erased type (`ToImpure.lean:52-53`, `:234`), and the body computes with
  `◾`, the boxed 0: `f2 false 41` is 1, and so is a constant
  `c := f2 false 41`, where the kernel gives 42 (`example : f2 false 41 =
  42 := rfl` is accepted; with `native_decide` the bug proves `False`). An
  arm that gives a type (`T true = Type`, `T false = ULift Nat`) has the
  same effect. Lean's specializer gives the declaration it makes for a
  lambda over the value (`List.map (fun x => x + v.1)`) a parameter of the
  same type `lcErased`, and `toMono` then passes `◾` at every call of it.
  So native gives a wrong value or a crash, by the type of the data: a
  wrong number for a `Nat`, a `Bool`, a `Decidable`, an `Option`, a pair
  whose fields are read, a closure applied, a structure of two scalars; a
  segmentation fault (exit 139) for a `String`, an `Array`, a structure
  with a `Float` field, pairs passed to a function; and for an unboxed
  `Float`, `UInt64` or `UInt8` Lean's C code does not compile
  (`lean_float_add(lean_box(0), …)`). lean2rr gives every parameter of type `lcErased` that receives data at a
  jump or a direct call (a join point's, a local function's, a
  declaration's) the type `lcAny`, a boxed data parameter: after Stage 1,
  before `toMono` runs, and again after Stage 2 (`ErasedData`). Data is a
  variable whose type is not `lcErased` and not a type former type; a type
  or a proof has such a type, so a type or proof parameter stays erased. A
  jump that passes `◾` there passes `box(0)`, as natively. Where Lean
  inlines the function into its caller, `simp` puts the jump's argument in
  place of the parameter, and native gives the kernel's value too. Not
  covered: data that Lean's own passes already replaced by `◾` (`simp`
  replaces a `let` of type `◾`, value and all, by `◾`), and data passed to
  a function value whose domain Lean typed `◾` (not a direct call). Tests
  `RtJoinErasedProp`, `RtJoinErasedType`, `RtJoinErasedFlow`,
  `RtJoinErasedIndirect` (a closure over the value applied elsewhere, one
  in a structure, a partial application, two joined matches),
  `RtJoinErasedMisc` (a `Decidable`, `Bool.casesOn` with a motive),
  `RtJoinErasedMerge` (two lambdas the specializer merges, three arms),
  `RtJoinErasedLayouts` (the crashes: native's expected exit code 139).
- *A boxed constant in a branch that never runs is computed at startup*
  (a Lean 4.34.0 compiler bug, judged 2026-10-07; the same class as
  lean4 issue #1965, whose fix, #12044's lazy closed terms, missed this
  path; no issue for it; unchanged on master). `ExplicitBoxing.mkCast`
  (`isExpensiveConstantValueBoxing`) boxes a scalar constant (a `Float`, a
  `UInt64`, a closed term of one) passed where a box is expected through
  an auxiliary declaration `X._boxed_const_N`, which is not registered as
  a closed term, so `EmitC.emitDeclInit` (`EmitC.lean:1003`) computes it
  at module init, before `main` and outside its branch, which forces the
  closed term it boxes. So in
  ```lean
  @[noinline] def flag (n : Nat) : Bool := n % 2 == 0
  partial def spin (b : Bool) (x : Float) : Float := if b then x else spin b x
  def K : List Float := match flag 3 with
    | true  => [spin false 2.5]
    | false => [1.0]
  ```
  the native program hangs at startup, where by Lean's semantics `K` is
  `[1.0]`; with issue #1965's program over a `Float` (`if h : 0 <
  arr.size then [arr[0]] else [42.0]` on an empty array) a native build
  with assertions aborts and one with `-DNDEBUG` reads out of bounds; a
  trace or panic in such a closed term prints at startup, also in a dead
  branch. lean2rr computes Lean's value: its boxed constants
  (`boxed-consts`) are once-cells computed at their first use, as Lean's
  other closed terms are, so it prints `[1.000000]` and `[42.000000]`
  (test `RtDeadBoxedConst`, with expectation files: native's empty output
  and exit code 124 under the test's 3-second limit, lean2rr's
  `[1.000000]`; `RtDepBoxedClosedOnce` keeps its traced closed terms in
  live branches).

**Diagnostics**
- lean2rr's own impossibilities (a `Box` unwrap of another variant, a cast
  with no conversion) print Lean's `INTERNAL PANIC: unreachable code has
  been reached` and exit 1, like a real unreachable.

**Blocking, the event loop and promises**
- *Blocking system calls* cooperate with lean-runtime's scheduler (a read
  of an empty pipe, a write to a full one, `flock`, `Child.wait`: the
  other contexts run meanwhile), but a few still block the whole program
  (`open` of a FIFO, lean-runtime's list in its `docs/sched.md`, "The
  limits of one thread").
- *Event loop details* (§5.14): lean-runtime's (its `docs/sched.md`,
  "Blocking IO and the event loop", `Std.Internal.UV`, and `docs/net.md`,
  "Where it differs from native"): the loop's callbacks run when the
  program blocks, at polling and effect points (at most once a
  millisecond), or on the loop context while other contexts run, so a
  program that computes without any of these delays them; signal delivery
  over signal-hook's safe API (SIGIO, SIGTSTP, SIGTTIN, SIGTTOU after
  their last watcher stops); two lookup threads for name resolution. A
  timer's or signal watcher's `stop` and `cancel`, and a socket's
  `cancelAccept` and `cancelRecv`, release the loop's promise on the
  caller's context (tests `RtTimerStopDropped`, `RtSockCancel`). The
  `net` cases lean2rr did not support before switch step 4 stay out of
  scope (implementation status).
- *Promises released inside a free* (§5.14): the `sync` dependents of a
  promise dropped unresolved because a container holding it is freed run
  once the whole free is over, where natively they run when the free
  reaches the promise: they see the rest of the container released too
  (a file handle held by a later element already closed). Another
  unresolved promise in the container is not resolved yet while they run,
  as natively (each resolution, its cell's store included, runs in the
  free's order after the free, since switch step 6; test
  `RtPromiseFreeLaterUnresolved`); a resolved promise is released inside
  the free, in its order (*Order of releases in one free*; test
  `RtPromiseResolvedFreeOrder`).

**Not supported** (lean2rr rejects the program at translation, naming each
extern)
- Every constant of the program is translated (§2.2), so an unused constant
  that reaches an unsupported extern makes lean2rr reject the whole
  program.
- *Lean-only target* (the owner's decision, 2026-10-03, §5.8): the C code
  of a program or of a package it requires is never compiled, linked or
  called. An `@[extern]` of the program runs the `@[export]` definition its
  C symbol binds to (whose type it is an instance of, with one compiled
  signature), else its Lean definition, also when its symbol is one of
  Lean's runtime library (never bound to the runtime);
  one with neither (an `opaque`, an axiom, a definition Lean cannot
  compile, a binding that fails its tests) is rejected (§5.8, "Externs of
  the program"). Where the package's C and the extern's Lean definition
  differ (a stub body, lean-zip's on offsets and lengths past what its
  codecs pass), the translation does what the Lean definition says. The C
  FFI work (branch `ffi-c`) stays parked: it is not a goal for now.
- *Lean definitions where native Lean runs other code:* an `@[extern]` of
  the program runs its own Lean definition where natively its C symbol
  links to Lean's runtime (an extern of the program is never bound to the
  runtime, the owner's decision of 2026-10-04: `@[extern
  "lean_array_get_size"] def mySize (a : @& Array Nat) : Nat := …`), or to
  an `@[export]` definition whose binding's tests fail (lean2rr warns,
  naming the definition and the failed test, §5.8). Where the definition
  is a stub, the result differs from native (test `RtExternStub`).
- *Re-declared runtime functions:* an `opaque` re-declaration of a
  function of Lean's runtime has no definition and is refused, the message
  naming Lean's declaration to call instead (and, when no imported module
  declares the symbol, the module of Lean's library to import). Before
  this rule, lean2rr called the prelude's function of any symbol, so
  `@[extern "lean_decode_lossy_utf8"] opaque decodeLossy` worked, though
  Lean's own declaration of that function (`Lean.decodeLossyUTF8`) is
  private to `Lean.Shell`: no program reaches the function now, and test
  `RtSweepUtf8` no longer prints its results.
- The `Lean` library's externs implemented in C++ (`Expr.mkData`,
  `evalConst`, `Dynlib`, the LLVM bindings, …): not in lean2rr's runtime
  yet, so a program that reaches one is rejected (their Lean bodies are not
  used in their place); a program that only uses data structures from
  `Lean` builds. With the optimization `unread-fields` (off by default),
  a value that is stored in a field no kept code reads is left out, with
  what only it reaches: a callback (a linter's `run`, an attribute's
  `add`, an environment extension's hooks: Batteries registers such
  callbacks for Lean's elaborator) or data (the `Expr` in a derived
  `Lean.ToExpr` instance's `toTypeExpr`), so a program that reaches the
  C++ externs only through such values builds.
- With the optimization `unread-fields` (off by default), three things
  that native Lean does at startup do not happen when only a value the
  pass leaves out (a callback or data in a field no kept code reads)
  needed them: a closed term read only to build such a value is not
  evaluated, so the `panic!` and `dbg_trace` messages of its evaluation
  do not show (Stage 2 lifts every full application with constant
  arguments into a closed term: this includes the program's own constants,
  `{ s with … }` updates and `initialize` blocks; an application with a
  non-constant argument stays); a value that such a callback or such data
  held has one reference less, which
  `dbgTraceIfShared` can show; the step of a `Lean` package's `initialize`
  constant that only such values read does not run (these steps register
  state for Lean's elaborator and print nothing).
- The `Lean` package's initializers (thousands of `builtin_initialize`
  declarations that register extensions, attributes and options; 19
  `initialize` ones in Lean 4.34.0), which natively all run
  (`lean_initialize()`) when a program imports a module of `Lean`: lean2rr
  runs only the `initialize` constants that the program reads, at startup
  after those of `Init` and `Std` (§5.12). Their effects are registrations
  in the state of Lean's compiler and elaborator, which a program that only
  uses data structures from `Lean` does not read; natively such a program
  also queries the stack limit and the number of CPUs once more at startup
  (`strace`).
- An error in an initializer of `Init` or `Std` in a program that uses the
  `Lean` package: natively `lean_initialize()` runs those initializers
  through `consume_io_result`, which turns the error into a C++ exception
  that nothing catches, and the program aborts (status 134):

      libc++abi: terminating due to uncaught exception of type lean::exception: resource exhausted (error code: 24, too many open files)
        file: /dev/urandom

  lean2rr reports it as for any other program, `uncaught exception:
  resource exhausted …` and exit code 1 (review RSG-03; test
  `RtStartupInitLeanPkg`, with expectation files). Such programs are not a
  target, and an abort is not behaviour to copy.
- Where `lean_initialize()` runs, in a program that uses the `Lean`
  package: natively each module whose own imports use `Lean` calls it at
  the start of its own initializer; lean2rr runs `Init`'s and `Std`'s
  initializers first whenever any module of the program uses `Lean`. The
  order differs only in a `prelude` program that reaches `Lean` through a
  private import of a `module` file imported after another program module
  with an initializer: natively that module's initializer runs before
  `IO.stdGenRef`, in lean2rr after it (review RSG2-01; visible only when
  that initializer prints or fails, or `IO.stdGenRef` fails).
- Loading a program that imports part of the `Lean` package but not `Init`
  or `Std` whole: lean2rr loads `Init` and `Std` as well, to find their
  initializers, which doubles its peak memory for such a program (about
  0.5 GB to 1.2 GB) and can change the advice in its build notes (review
  RSG2-02). The translated program does not change.
- Mathlib, and programs that import it: Mathlib's module initializers
  reach the `Lean` library's C++ externs (CSLib's reach 32), so such a
  program fails the same way. Mathlib is not a target. Computational code
  from such a library is: written as a program that imports only `Init`
  and `Std`, it translates like any other (CSLib's algorithms, such as
  insertion sort and merge sort, run identical to native; round 9
  RV9S-03).
