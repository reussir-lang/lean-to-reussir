# lean2rr translation plan

How a Lean 4.33 program becomes a Reussir program: what each stage receives,
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
  │  lake build (stock Lean 4.33)
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
(`runStage2`, `--emit mono` and `externs`), Stage 3 (`retypeMono`, from the
declarations the entry point calls, `--emit retyped`), the registry's
passes over mono LCNF, Stage 4 (`lowerProgram`, with the registry's
lowering hooks), the `Array Nat` literal tables and `Outline`, the
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
- Stage 3: `MonoRetype`;
- Stage 4: `RR` (the `.rr` syntax tree and its text), `LowerBase` (state,
  type translation), then `Lower/*.lean`, each importing the previous one:
  `Ctx` (the code-lowering context), `FnValues`, `LazyForce`, `Conv`,
  `Decls`, `Externs`, `LazyGlue`, `Process`, `Promises`, `Identity`,
  `ExternCall`, `Borrow` (release times of borrowed resources, §5.8),
  `Values`, `JoinPoints`, `StateMachine` (J4), `Hooks`,
  `Code` (`lowerCode`, `lowerDecl`), `Finish`;
- the program: `Emit/Startup` (initializer order, the startup chain),
  `Emit/Entry` (the entry point), `Emit/Program` (`lowerProgram`, which
  splices chains of closed terms before lowering, and the lowered
  program's steps), `ArrayLits` (`Array Nat` literals as tables),
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
`reussir-patches/` (the local Reussir patches, docs/reussir-bugs.md),
`tests/`, `docs/`.

The core translation is the plain one: the rules of this plan without the
optional passes, and correct on its own (the classic corpus at every size
and the runtime suite match native Lean with every optional pass off).
Each optimization is a module of `Opt/` with an `install : PassConfig →
PassConfig` that plugs it into a hook of `PassConfig`, keeping what was
installed before: a representation choice of the type translation (record
field order, `[value]` structs, one-word `Nat`/`Int` arrays,
placeholders kept in once-cells), a part of Stage 3 (map loops split by
element representation), a pass over the checked mono declarations
(`monoPasses`), Lean definitions replaced by prelude functions, a lowering
hook (`LowerHooks`: the body before lowering, the J1′ choice, the form of
J4's state machine, constant caching, the binding of a `cases`
alternative's fields), or a pass over the generated Reussir functions
(`rrPasses`). Every hook's default is the plain translation. A pass keeps
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
  the init functions of `initialize` constants;
- `IO.Error.toString`, which the entry point uses to report an uncaught
  exception (§5.11);
- the `IO.Error` builders, once the program reaches a fallible IO extern
  (§5.8).

Everything referenced from reachable code is collected:
- declarations with code;
- `@[extern]` declarations (provided by the runtime);
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
evaluated once at startup, while Lean runs its body at every use. Lean represents a
higher-kinded argument as a type-level function, e.g.
`StateT Nat Id ↦ fun α => Nat → α × Nat`. Substitution plus beta reduction
therefore turns `m (β × σ)` into an ordinary type such as
`Nat → (β × Nat) × Nat`.

Sometimes a type argument is not statically known, for example a type taken
out of an existential package. The instance is then built with that argument
set to `lcAny`, Lean's own "unknown type". Values of that type use the
uniform `Box` representation (§5.1). Lean itself treats every value this
way, so this is always correct, only slower.

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

Every program Lean compiles is translated (it links only if the runtime
implements every extern it reaches, §10). Where a static type is
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
  well: a typed instance there would convert whatever the uniform code
  passes on every call, and could not hold a value only `unsafeCast` to that
  type (natively any object). Growth through a type function (`m` →
  `OptionT m`) gets one typed instance at `F lcAny`, which adapts the
  dictionary the uniform instance passes, and whose request at
  `F (F lcAny)` goes back to the uniform one. Growth that no path shows is cut by bounds: a type
  argument deeper than 64 or larger than 256 nodes becomes `lcAny`, and
  past 1024 instances of one declaration every further instance is the
  uniform one. So the set of instances stays finite. This is
  necessary: Reussir's own monomorphizer cannot handle polymorphic
  recursion. Callers of a uniform instance convert their arguments
  structurally on every call (§5.1), which costs time proportional to the
  arguments' size.
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
  `lcAny`, so values of those types are `Box`es. The casts become the
  ordinary representation conversions of §5.1; between arrays of different
  element types the conversion is element by element. Stage 3 (§4) recovers
  the precise types around this code. When source and target elements have
  the same representation, the `map` loop runs on the precise array, in
  place. When they differ, Stage 3 splits the loop over two arrays: it reads
  the source at its own representation (still replacing each slot by the
  placeholder after reading it) and pushes each mapped value onto a new
  result array created with the source's size as capacity (§4).
- A `box(0)` placeholder is a value that is never inspected. It arrives as
  a unit-like value used at another type, or as `◾` at a relevant type.
  Stage 4 materializes it as the *zero* of the expected type: `0`, `false`,
  the first constructor whose fields have zeros, a function value returning
  a zero (the nullary `z` variant, §5.3), an empty array. For `Nat`, `Bool`
  and enumerations this is exactly what `box(0)` denotes in Lean. Only a
  type without a finite value gets `unreachable`. A zero that would
  allocate (a string, an array, a record, a reference, a boxed unit) is
  built once and kept in a once-cell, like a constant
  (§5.12): `modify` stores one per update, and since a placeholder is never
  inspected, a shared value serves as well as a fresh one (optional pass
  `placeholder-cache`; without it each placeholder is built where it is
  used).

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
it converts to `Nat`), while `fun n => Fin (n + 1)` stays `lcAny`,
although every `Fin (n + 1)` is a `Nat`. Every mono type lean2rr
computes itself uses the same conversion.

**`toMono`: semantic lowering done by Lean.**
- `Decidable` → `Bool`.
- `Nat` constructors and `cases` → `Nat.add x 1`, and `if n == 0 … else
  let m := n - 1`.
- `Int` `cases` → a sign test plus `natAbs`.
- `cases` on builtin runtime types (`Array`, `String`, `ByteArray`,
  `Float`, `Thunk`, `Task`, `UIntN`) → accessor externs.
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
  result of `xs.map f` is bound at `Array NonScalar`, i.e. `Array lcAny`, and
  so is every loop parameter it is passed to.

A binder typed `lcAny` uses the uniform `Box` representation (§5.1), and each
use at a precise type converts it. For an array that is an element-by-element
copy: a loop reading `ys[i]!` from a loop-invariant `Array lcAny` would copy
the whole array at every step, which is quadratic. So Stage 3 recovers the
exact type wherever the program determines it. It iterates over the whole
program until nothing changes.

A binder's type is recovered from what flows *into* it, never from how it
is used. A use at a precise type only speaks for its own branch. With a type
that depends on a value, `data : Array t.denote` is used as `Array Nat` only
in the branch where `t = .nat`. A conversion moved from that use to the
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
  convert right away anyway; the conversion moves to the callee's `return`,
  which for a constant happens once instead of at every read. A self call
  that binds the result at another type than the declaration's own counts
  as a call here: that is polymorphic recursion into the uniform instance
  (`FSeq.flatten` at `lcAny` calls itself at `lcAny × lcAny`), which returns
  a value of a different type at every depth, so the type at which the one
  typed caller binds the result (`List (Nat × Nat)`) does not hold for all
  of them (adv2 PrgPoly1, runtime test RtPolyRecResult).
- **The `map` loops of §2.7.** The loop of `Array.mapMUnsafe` or
  `Array.mapFinIdxMUnsafe` (recognized by name, as Lean's specializations of
  it) returns its array once `Array.uset` has replaced every element. If
  every value it stores, other than the `box(0)` placeholder, has the same
  precise type `β`, its result is an `Array β`: `Array lcAny` becomes
  `Array β` in its result type (`Option (Array β)` for `mapM` in `Option`).
  The rule only applies when the loop's array stays within the loop: it is
  read, written, passed back to the loop, returned or jumped with.
- **Parameters from callers.** A parameter whose type holds an erased array
  (`Array lcAny`, `Option (Array lcAny)`, …) gets `T` if every call site
  passes it at the same precise type `T`. The assumption is checked: the
  body is retyped under it, and the self calls must then pass `T` too. By
  induction on the calls, every value reaching the parameter has type `T`.
  Only call sites in declarations reachable from `main` and the startup
  work count. A partial application that leaves the parameter open blocks
  the rule. Other `lcAny` parameters are left alone. Code over a dynamically
  typed value (`Dynamic.get?`) casts it, in branches that a runtime check
  rules out, to types that a precise parameter type could not be converted
  to.
- **Externs at unknown types.** A call of a polymorphic extern instantiated
  at `lcAny`, e.g. `Array.uget` and `Array.uset` at `NonScalar`, is
  redirected to the extern's instance at the type arguments the arguments
  determine. Every argument must then have exactly the expected type, or be a
  `◾` placeholder, and a binder that already has a precise type must be
  given exactly that type. An extern does not depend on its type arguments;
  only the representation changes.
- **Placeholders.** A placeholder `let z := ◾` gets the type its uses
  expect when they agree: it has no value to convert.
- **References.** Mono types every `ST.Ref σ α` `lcAny`. An instance of
  `ST.Prim.mkRef` at a precise `α` returns `typedRef α` instead (a type
  only lean2rr uses), and the rules above carry it to the binders the
  reference flows into: the `ST.Out` field, join-point parameters, and the
  parameters of functions that every caller passes it to (the rule
  *parameters from callers* also applies to parameters that receive a
  typed reference). Stage 4 gives `typedRef α` the typed representation of
  §5.1, so an `IO.Ref Nat` counter or the state of a `StateRefT` is read
  and written without boxing. A reference stored in a structure field,
  passed to uniform code or created there stays `lcAny`.

For `xs.map (· * 2)` these rules make the whole map run on the precise array,
in place and without boxing, like native Lean. The loop is assumed to
receive `Array Nat`. Its reads become `Array.uget@Nat`, its placeholder is a
`Nat` zero, and its writes of `Nat` values become `Array.uset@Nat`, so it
passes `Array Nat` back. The loops that read the result then receive the
precise array from their callers.

When `f` changes the representation (`Nat → Bool`), the loop's array
parameter stays `Array lcAny` after the fixpoint: it holds `Nat`s and
`Bool`s. Such a loop is *split* (optional pass `split-map-loops`; without it
the loop runs on an array of `Box`es), also where it is entered inside
another split loop's body (`a.map (·.map f)`: the entry calls of the split
instances are rewritten too, until no new instance appears). Its split instance takes two arrays instead
of one, the source `src : Array α` and the result `dst : Array β`:
- a read `uget bs i` of an array derived from the parameter becomes
  `uget@α src i`, a value of `α`'s own representation;
- the placeholder write `uset bs i ◾` becomes `uset@α src i ◾` (the element
  stays unshared, as in Lean);
- the value write `uset bs i v` becomes `push@β dst v`;
- `usize`/`size` measure `src`; a self call passes both arrays; a returned
  array, or one put in a constructor (`EST.Out.ok bs w`, `some bs`), is `dst`;
  a join-point parameter receiving derived arrays gets two parameters.

An entry call `map sz 0 xs` with `xs : Array α` becomes `map' sz 0 xs
(Array.emptyWithCapacity@β xs.size)`. The push is the write at index `i`
because `dst` holds exactly the `i` values mapped so far whenever the loop
runs at index `i`: it starts empty at index 0, and every path to a self call
writes one value and passes `i + 1`. The split only happens when the loop
has this shape: derived arrays are read and written only at the loop index
(reads before the value write, the value write once per path), passed to the
loop with the index plus one after the write (or with the index to the loop
that a `_redArg` wrapper calls), returned, put in constructors or passed to
join points, and never captured or used otherwise; the entry passes the
literal index `0` (possibly through join-point parameters). The values it
stores must all have one type `β` that Stage 3 recovered, neither `lcAny`
nor `◾`. Otherwise the
loop keeps the `Box` array: its input is converted once on entry, and its
result type (`Array β` by the `map` rule) makes it convert once on exit.
A map whose function projects a field of a parametric structure
(`(xs.zip ys).map (·.2)`, `rs.map (·.y)` with `structure R (α) where s :
String; y : α`) is such a loop: the element it reads from `Array lcAny`
has type `lcAny`, so the fields of the `cases` on it stay `lcAny` (round 7
RV7D-01: they had been given the constructor's parameter types, `◾` or an
earlier field's type, so the loop's result became an `Array ◾`, read back
as zeros, or an `Array String` holding `Nat`s, an unreachable panic with
the pass off too; test `RtMapProjFields`).
The original loop is dropped when nothing reachable calls it any more, and
the fixpoint runs once more, so the values the split loop reads can type
what they flow into.

Lean sometimes runs the first iteration in a specialization of its own.
When the same function is mapped at two sites (`rows.map (·.map
Nat.toFloat)` twice), `spec_2` runs one iteration and passes the array, with
one value written, at index 1 to the actual loop `spec_2.spec_2` (or to
another specialization of the same map). `spec_2` has no self call, so the
rule *parameters from callers* gives its parameter the callers' type
`Array α`, although it stores `β` values. Its array parameter is then the
only parameter of a precise array type that it reads with `uget`, provided
the values it stores have another type `β`. It is split like the other
loops, and its continuation with it (a call with the index plus one after
the write). The `map` rule gives `spec_2` no result type, since it returns
its array or its continuation's result. Its split instance returns
`Array β`: it returns only `dst`, the result of a split instance, or a
constructor around them. Without this, the loop ran on an array of `Box`es,
converted on entry and exit (round 6 RV6L-02: 3.5x native memory).

Each rule is exact. A value's type is taken only from its definition or from
everything that flows into it, so the recovered type is the type the value
has on every path. Where the program does not determine the type, the
binder keeps `lcAny` and uses `Box`, with conversions where it meets a
precise type.

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
| `Nat` | `enum [value] Nat { Small(u64), Big(LBig) }` | `Big` only for values ≥ 2^64; `LBig` is an opaque runtime bignum (GMP) |
| `Int` | `enum [value] Int { Small(i64), Big(LBig) }` | `Big` only outside the `i64` range |
| `String` | `LStr`, an opaque copy-on-write handle to one block like Lean's string object: a 32-byte header (count, byte size, capacity, character count) and the UTF-8 bytes | literals: §5.4 |
| `Array α` | `RVec<S>`, the runtime's copy-on-write vector | in place when unique. `S` is the storage type of `α`: `⟦α⟧` itself if it can cross Reussir's FFI boundary (scalars, `bool`, runtime handles, shared records); for an enumeration or `Unit`, its index (`u8`, `u16` or `u32` by the number of constructors; Lean stores a tagged scalar); otherwise a generated one-field shared struct `ElemBox` around it (Lean boxes array elements too) |
| `Array Nat`, `Array Int` | `LNatArr`, `LIntArr` | one word per element like Lean's boxed scalars: small values inline, big ones as bignum handles, in one block with Lean's 24-byte array header (count, size, capacity); the array functions are the `natarr`/`intarr` counterparts of the generic ones, with the same arguments (optional pass `nat-arrays`; without it they are arrays like the others) |
| `ByteArray`, `FloatArray` | `RVec<u8>`, `RVec<f64>` | |
| `ST.Ref σ α` | a generated shared record `L2RRef_N(Cell<⟦α⟧>)` around Reussir's mutable cell | the contents keep their own representation; `Nat`/`Int` (`L2RNatRef`/`L2RIntRef`, a tagged word as in `LNatArr` plus a cell for a big value) and `[value]` structures (in an `ElemBox`) are stored apart, since Reussir's cells do not hold `[value]` records with counted members. Mono types a reference `lcAny`: it travels in a `Box` except where Stage 3 types it (below) |
| `Thunk α`, `Task α` | `LCell<S>`, a shared mutable runtime cell holding a generated state `S { pending(L2RUnit -> ⟦α⟧), busy, done(⟦α⟧), … }` | memoized thunks, deferred tasks (§5.14) |
| `Option α`, `Except ε α`, `EST.Out ε σ α`, … | generated types (next paragraph) | |

A type with computed fields (`Lean.Name`) is represented by its
implementation inductive `T._impl`, whose constructors also store the
computed fields. Lean's runtime does the same, and mono code uses both names
for the same values.

**`◾` (erased)** values have the unit representation. Erased parameters are
kept, so arities are exactly Lean's (§5.2), and they receive `L2RUnit::u{}`.
Erased constructor fields have no representation. Where `◾` or a unit-like
value is used at a *relevant* type, it is Lean's `box(0)` placeholder
(§2.7) and becomes the zero of that type.

**Other inductives** become one Reussir type per instantiation, mirroring
the Lean declaration: same constructors, same field order, fields typed by
translating their instantiated types. Only *relevant* type parameters
distinguish instantiations. A parameter is relevant if it appears in a data
field. A phantom parameter such as `EST.Out`'s world type does not multiply
types. The shape follows the constructors:

```
inductive Ordering | lt | eq | gt          ↦  enum [value] Ordering { lt, eq, gt }        -- no fields: unboxed
inductive Tree α | leaf | node (l) (k : α) (r)
   at α := Nat                             ↦  enum Tree_Nat { leaf, node(Tree_Nat, Nat, Tree_Nat) }
structure P where a : UInt8; b : Nat; c : Float
                                           ↦  struct P { a : u8, b : Nat, c : f64 }
Prod Nat P                                 ↦  struct Prod_Nat_P { fst : Nat, snd : P }
List (Prod Nat P)                          ↦  enum List_Prod_Nat_P { nil, cons(Prod_Nat_P, List_Prod_Nat_P) }
```

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
  other's instances; `inductive Rose | node : List Rose → Rose` gives
  `Rose` and `List_Rose`, defined together. Whether a type is a shared
  record (so that arrays store it as it is, not in an `ElemBox`) is decided
  from its constructor shapes before its fields are translated, so
  `inductive Tree | node (v : Nat) (cs : Array Tree)` holds `RVec<Tree>`,
  the representation `Array Tree` has everywhere else (also through mutual
  types, whichever is translated first).
- **Polymorphic recursion in a type.** An `unsafe inductive` may use itself
  at a larger argument: `Nest α | nil | cons (x : α) (rest : Nest (α × α))`.
  Translating `Nest Nat` would need `Nest (Nat × Nat)`, whose field needs
  `Nest ((Nat × Nat) × (Nat × Nat))`, and so on without end. So the rule of
  §2.6 applies to the instantiations requested while fields are translated,
  for an inductive whose block uses its types at other arguments than its
  parameters (only `unsafe` ones can; a safe `Tree | node (kids : List (Nat
  × Tree))`, whose `List Tree` reaches `List (Nat × Tree)`, is never cut):
  an instantiation that strictly contains the arguments of an instantiation
  of the same inductive whose fields are being translated (the path: a
  mutual partner, `A α` holding `B (α × α)` holding `A (List (α × α))`, or
  another inductive, `List (Rose (Option α))`, in between), or that is built
  from the `lcAny` of the uniform instantiation on the path, or that has 256
  instantiations of its inductive on the path, is the uniform instantiation.
  `Nest Nat` is `enum Nest_Nat { nil, cons(Nat, Nest_Box) }`, and
  `Nest_Box`'s own field is `Nest_Box`. A typed `Nest (Nat × Nat)` value
  stored in that field is converted (boxing its `x`, its own `rest` being a
  `Nest_Box` already), like any value meeting another representation of its
  type (below).

**Function types** become generated shared enums, one per (lowered,
curried) function type, whose variants say what a value is a partial
application of (§5.3). They are not Reussir closures.

**The uniform type `Box`.** When a data position has type `lcAny` (§2.6, §4),
its value is stored as `Box`.
- `Box` is a generated enum with one variant per concrete Reussir type that
  the program ever boxes, plus a unit variant. Variants are created as
  Stage 4 needs them, and the unboxing functions are regenerated until the
  set stops growing, so the set is known at the end of Stage 4. `Box` is
  always emitted, since types can mention it even when nothing is boxed.
- Converting a precise type `T` to `Box` wraps the value into `T`'s variant.
  Unwrapping must accept every variant that can hold a value of the same
  Lean type, because one Lean type can have several Reussir
  representations: the instantiations of an inductive (`List Nat` and a
  uniform `List Box`), or the representations of an array (`LNatArr`, and
  `RVec<Box>` for an `Array Nat` built by the code of §2.7). Unboxing to a
  nominal, array or word type (`Nat`, `Int`, `UInt8/16/32`, `Bool`,
  `UInt64`, floats) is therefore a generated function that matches all
  such variants and converts structurally, element by element for arrays.
  An instantiation whose Lean type cannot be the target's (`Option Nat`
  read as `Option String`) is reached only by a value that Lean's `cse`
  shared between the two types (`none`, `some []`: no data where the types
  differ). In a program that cannot cast (defined next) it converts
  through the instantiation at the arguments both types share, `lcAny`
  elsewhere: `Prod (Array S₁) Nat` read as `Prod (Array S₀) Nat` goes
  through `Prod lcAny Nat`. Converted directly, K structures of one shape
  going through uniform code made K² conversion functions, each with its
  own generic runtime calls (build time grew quadratically). The arms
  stay quadratic (each of the K unboxing functions has an arm per
  instantiation), but they are no longer the main cost, and sending them
  through one function per inductive would not make the matches smaller:
  rrc gives every `match` on `Box` one region per variant, a wildcard arm
  being copied into each variant it covers (Reussir bug 22). Measured
  (shared machine) on 80 structures of one shape through one
  polymorphically recursive function (`Prod (Array Sᵢ) Nat`; round 6
  Ty6QS80) and on the program of the round-6 report (Ty6RT1): the build
  takes 200 s and 334 s (native: 3 s and 1 s; lean2rr's translation 1 s);
  without the 6,320 and 7,287 arms that convert through the shared
  instantiation, 157 s and 270 s. The largest part is rrc compiling each
  generic runtime function instantiated at a type with a separate rustc
  run (`l2r_once_get<T>`/`l2r_once_set<T>` for every type's cached zero
  value and constants and, when this was measured, the origin records of
  every conversion, since removed): 1,970 and 1,992 runs, 100 s and 128 s
  (a small program: 368 runs, about 30 s).
  When the program can cast at all, unboxing also accepts the variants of
  types that an `unsafeCast` can read (below). A program can cast when
  some declaration it reaches outside Lean's library (`Init`, `Std`,
  `Lean`, `Lake`) and lean2rr's shim (`L2RShim`, §5.8) is `unsafe`, is an
  axiom, uses `sorry`, or is `@[extern]` or `@[export]`: `unsafeCast`
  needs `unsafe` code, a `cast` between types lean2rr represents
  differently needs an equality that only `sorry` or an axiom proves, and
  Lean does not compare the types of an extern and the `@[export]`
  definition that implements it (which lean2rr calls directly, §5.8,
  whichever of the two is the program's): `@[extern "s"] opaque asP2 (p :
  Pkg) : P2` bound to `@[export s] def payload (p : Pkg) : p.α` reads an
  existential payload as a `P2`. `implemented_by` is type-checked, but
  only by its declared type: a program declaration implemented by an
  `unsafe` function, even one of the library's, counts (`@[implemented_by
  TypeName.mk] opaque mkTN` gives two types the same `TypeName`, so
  `Dynamic.get?` reads one as the other). The code Lean 4.33 generates for
  a `partial def` (`f._unsafe_rec`) is `partial`, not `unsafe`, so it does
  not make a program cast. Which modules are Lean's library is decided by
  their names; a program module named `Init.*`, `Std.*`, `Lean.*` or
  `Lake.*` that is not the toolchain's is rejected when the program is
  loaded (§10). The declarations
  reached are those the program's code comes from and, transitively, the
  constants their definitions mention (code inlined into others) and their
  `implemented_by` targets (`LowerCtx.programCasts`). Lean's library casts
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
  scalar, any other heap object. Two kinds of casts are left out. One
  whose conversion would need a function value at another representation
  (a wrapper, §5.3): every unboxing function would then match every other
  type with function fields at the same slots (the dictionaries of uniform
  code), each wrapper adding arms to the application functions of its
  type (programs built from monad transformer towers grew by a fifth).
  And one between inductives that do not correspond constructor for
  constructor (another number of constructors), which typed code converts:
  every unboxing function would convert from every inductive sharing a
  constructor shape with its own (3 to 5 % more code). Such a cast panics
  (§10).
  A boxed unit unwraps to the zero of `T`: a unit used at another type is
  Lean's `box(0)` placeholder (§2.7). Any other variant is unreachable.
- Conversions are inserted wherever a value's Reussir type differs from
  the type expected where it is used: call arguments, return values,
  constructor fields, join-point arguments, closure arguments and results.
  This is the typed counterpart of Lean's own `explicitBoxing`, which
  converts between `obj` and unboxed scalars.
- An inductive applied to `lcAny` is instantiated with `Box`:
  `Free lcAny Nat` ↦ `Free_Box_Nat`.
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
- A reference (`ST.Ref`) is boxed under the variant of its own type. A
  reference cannot be converted without losing aliasing, so where one is
  used in a `Box` (uniform code, or typed code that got it through a
  `lcAny` position), each operation goes through a generated dispatch over
  every reference type the program boxes: it acts on that reference's one
  cell, converting the value between the cell's element type and the
  operation's (`get` at `Box` on an `L2RNatRef` boxes the `Nat`; `set`
  unboxes). Typed references come only from `ST.Prim.mkRef` instances at a
  precise element type, and flow only to binders that Stage 3 types from
  them (§4), so a typed position never receives a reference of another
  representation. `ST.Ref.ptrEq` compares the records' addresses.
- A partial application has the type of its target with the supplied
  arguments removed. Lambda lifting can give a lifted lambda the result type
  `lcAny` while its closure is used at `Nat × Int → Int`, or the reverse; the
  value is then converted to the binder's type as above, and the callee
  still runs only when the last argument arrives.
- When a structure built at a uniform type (for example a `List Box` coming
  out of polymorphically recursive code) meets code expecting the precise
  type (`List Nat`), the conversion is structural, element by element.
  An array whose elements cannot be converted (`Array String` to
  `Array Nat`) must be empty when that happens: an empty array that `cse`
  shared between two element types, or the result of mapping nothing. Its
  element step is therefore `unreachable`. (`Array Nat` to `Array Int`
  converts element by element: a `Nat` converts to an `Int`.)
  - *Loops, not recursion.* A conversion whose recursion goes through one
    field of each constructor (a list's tail, a snoc list's init) is a
    directly recursive function that Reussir compiles as a loop (tail
    recursion modulo constructors). Any other recursion (several recursive
    fields, as in a tree; through other types, as a rose tree's `List` of
    trees or mutual inductives; through array elements) is an explicit
    stack: the generated function is a loop over a stack of pending
    constructors, each holding the source value and the fields converted
    so far (`convMachine`). Converting a deep value uses heap, not stack,
    as native Lean, which converts nothing, uses none.
  - *A new value.* The converted value is a new object, equal to the
    original and unshared, so it is updated in place; the original is
    released as soon as nothing else holds it, with any resource it holds.
    Nothing links the two: converting the value back rebuilds it again (a
    value that crosses into uniform code and back is converted twice).
    Natively there is one object; only identity (`ptrAddrUnsafe`, `ptrEq`)
    and sharing (`dbgTraceIfShared`) can tell the difference, and neither
    is preserved (§9).
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
  - A `[value]` struct is natively its field.
  When the two Reussir types have the same layout (the same constructors
  with fields of the same layouts, position by position, coinductively;
  arrays of such elements) and the conversion would pair exactly those
  fields, the value is used as it is (`l2r_retype`, the same object
  reinterpreted): a user list read as another user list, or an `Array T₁`
  field read at `Array T₂`, costs nothing and keeps its sharing. This
  applies to instantiations of one inductive as well (`structConv`,
  `vecConv` otherwise rebuild). Where no conversion exists at all, lean2rr
  warns and emits a run-time panic for that cast: the program is still
  translated.
- `Box` costs one allocation per boxing, and appears only on the rare paths
  of §2.6. Typed code never pays for it.

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

### 5.3 Closures (function values)

After Stage 2, every closure is a partial application of a top-level
declaration; lambda lifting turned local functions into declarations over
their captured variables.

- **Representation.** A Lean function value of lowered, curried type
  `T = A₁ → … → Aₙ → R` is a value of a generated shared enum `L2RFn_…`
  with these variants:
  - `p<m>_<target>(c₁, …, cₘ)`: a *target* (a declaration, an extern, a
    constructor, a standard-stream primitive) with its first `m` arguments
    captured. With `m = 0` the variant is nullary and costs no allocation;
  - `raw(A₁ -> …)`: a Reussir closure, for values built by glue code;
  - `w<S>(g)`: a value `g` of another representation `S` of the same Lean
    type (§5.1);
  - `z`: the `box(0)` placeholder (§2.7), a function that is never applied.
- **Creating a function value.** A partial application of a target of
  arity `k` to `m < k` arguments builds `p<m>_<target>(args)`: one
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
- **Erased parameters.** Lean still passes erased parameters (a proof, the
  IO world, a type) to closures, and they count toward the arity. They
  remain parameters of type `L2RUnit`, in declarations and closures alike,
  and receive `L2RUnit::u{}`. Only extern calls drop them.
- **Constructors and externs** are targets like declarations. Constructors
  do no work, so their timing does not matter.
- **Prelude callbacks.** Runtime helpers that take a Reussir closure
  (`dbgTrace`, `timeit`, …) receive `|x| l2r_ap1_…(g, x)`. Glue that
  builds a function value from Reussir code uses the `raw` variant.

The enums and the application functions are generated at the end of
Stage 4, together with the `Box` unboxing functions, until no new variant or
application appears.

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
  Lean types: with these functions inlinable, rrc's inliner grew such
  programs exponentially (an 8-line `StateT` tower used at `IO` did not
  build within 30 minutes or 15 GB; Reussir bug 20). Out of line, a
  conversion, an unboxing, or the application of a wrapped value or of a
  value of uniform type costs a call (until LLVM inlines it); all are rare
  outside uniform code, and typed function values are unaffected.

### 5.4 `let`, `return`, literals

- `let x := v; k` becomes `let x = ⟦v⟧; ⟦k⟧`, and `return x` becomes `x`.
  Lean's passes have already removed dead `let`s. Lowering never drops a
  Lean `let`, never evaluates one twice on the same path, and never
  reorders them, because a `let` can run a function that panics. It does
  add bindings of its own: representation conversions, placeholders, and
  the bodies of duplicated join points (one copy per path).
- Literals:
  - `Nat` literals below 2^64 become `Nat::Small`; a bigger one is parsed
    by the runtime from its decimal digits, kept in the string literal
    table: `l2r_nat_norm(l2r_big_of_decimal_lstr(l2r_str_lit(id)))`
    (`natLiteral`). One flat call: a nested arithmetic expression per limb
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
| `cases t : Tree Nat \| leaf => e₁ \| node l k r => e₂` | `match t { Tree_Nat::leaf => ⟦e₁⟧, Tree_Nat::node(l, k, r) => ⟦e₂⟧ }` |
| `cases p : P \| P.mk a b c => e` (single constructor) | `let a = p.0; let b = p.1; let c = p.2; ⟦e⟧`, positions from the alignment-sorted layout (§5.1) |
| alternatives missing a constructor, no default | extra arm `_ => unreachable` (Lean has proved it impossible) |

Erased fields get no binders. Reussir syntax notes: match arms have no
trailing comma after the last arm, and there is no `else if` (use
`else { if … }`).

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
in `Box` is converted to the inductive's uniform instance first, which
accepts values boxed from those other types too. Where no conversion
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
  of Reussir bug 7 (docs/reussir-bugs.md). A structure (one constructor:
  no match, its fields are projections) that stays live the same way
  projects only the fields used while it is live; an inner alternative
  that no longer uses it projects the others there (the pair `(k', t)` of
  an association list, kept whole when its key does not match).
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
of the runtime. A type whose placeholder is not a finite value (a type
without one, or a record whose placeholder would hold one, such as
`inductive W | bad (e : Empty) | ok (n : Nat)`, whose placeholder is built
from `bad`) gets no slot: such a field stays in its variant, which is then
allocated as in the core form. The pass checks this on every state
machine. So a jump costs a jump and the moves of its slots, and no
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

An extern call becomes a call of the prelude function named after the
extern's C symbol (or generated glue, below). lean2rr keeps no table of
the externs it supports and does not check that the prelude defines the
function: when it does not, rrc reports an unknown function (§10, "Not
supported"); `lean2rr --emit externs` lists the externs a program calls.
The prelude function is:
- inline Reussir code, for fast paths such as small-`Nat` addition with an
  overflow check;
- or a call into the runtime crate (§6).

| Lean extern | Implementation |
|---|---|
| `Nat.add`, `Nat.decLt`, … | `leanrt` `Nat` operations: small fast path, bignum slow path |
| `UInt32.add`, `UInt8.div`, `Float.add`, … | `+ - *` map to native Reussir arithmetic, since both wrap. Division, remainder, shifts and float→int always go through wrappers with `lean.h` semantics (e.g. `x / 0 = 0`, `x % 0 = x`, shift by `b % bits`, saturating casts): Reussir lowers them straight to LLVM operations that are undefined at those edge cases. |
| `Array.push@Nat`, `Array.get!@Nat`, … | `Vec` operations; out-of-bounds follows Lean (panic message plus default value) |
| `String.append`, `String.get`, … | `leanrt` string functions with Lean's UTF-8 byte-position semantics |
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
- **Fallible IO** (files and the file system): the runtime primitive
  records its outcome in a last-error slot; `l2r_io_finish` turns it into
  `EST.Out.ok` with the payload (converted: unit, handle, `Metadata`, an
  array of `DirEntry`) or into `EST.Out.error e`, where `e` is built by
  Lean's own exported `lean_mk_io_error_*` builder for the reported kind,
  as Lean's `decode_io_error` does (the builders are instantiated when a
  program uses such an extern). `IO.FS.Handle` is the runtime's `LHandle`.
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
    would block forever. Its
    declaration is lowered to generated glue instead of its body, in
    native order (only the stderr check waits for stdout's end of file
    too, §10): spawn with stdout and stderr piped and stdin null, or
    piped when `input?` is `some s` (then `putStr s`, `flush`, and the
    handle's release closes it, like `takeStdin` and the handle's last use
    natively); `l2r_proc_drain` reads both pipes to end of file together;
    `readToEnd`'s UTF-8 check of stderr (`IO.userError "Tried to read from
    handle containing non UTF-8 data."`); `wait`; the same check of stdout.
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
  in `mutex.cpp`) are runtime handles, and their externs payload
  primitives over `leanrt::sync`. A thread that must wait blocks its
  context (§5.14, *Blocking*); a lock's owner is a thread: a context, and
  on it the innermost running task's thread (a task needed by another runs
  on a worker thread natively). As with glibc, locking a `BaseMutex` the
  same thread holds waits forever, `tryLock` then fails, and a released
  mutex goes to the thread that waited longest; the shared mutex follows
  libc++'s (a writer that has entered keeps new readers out). Everything
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
  treats it as a toolchain module (no startup work). The shim follows the C functions
  (`uv/*.cpp`) check by check, over primitives of the runtime's event loop
  (`leanrt::net`, §5.14) on plain values (numbers, strings, byte arrays,
  handles, promises); errors are built in Lean as `lean_decode_uv_error`
  builds them (libuv's code as the error number, `uv_strerror`'s text).
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
  returned in `α`'s storage type, wrapped or unwrapped if that is an
  `ElemBox`, converted to or from its index for an enumeration stored as
  one (only for externs over arrays of `α`, whose storage must be the
  array's). Other parameters, like an index, are passed as they are.
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
  does not see end of file while the helper waits for it. So for a program
  that creates resources (it calls `IO.FS.Handle.mk`, `createTempFile` or
  `IO.Process.spawn`), lean2rr runs Lean's own borrow inference on its mono
  declarations (Lower/Borrow: copies go through `toImpure` and the impure
  passes up to `inferBorrow`, as Lean compiles its own declarations; extern
  instances get their extern's `@&`) and emulates Lean's reference counting
  where a value may hold a resource (a handle, which mono types `lcAny`, so
  any `Box`; a record, array or reference with such a field):
  - a direct call keeps an argument passed to a borrowed parameter until
    the call returns (`l2r_release_after`, an effectful FFI call after the
    call, as Lean's `dec`), when the caller owns it; an argument the caller
    itself borrows (a borrowed parameter, a field or array element of one,
    a join point parameter to which every jump passes such a value) is left
    alone, as natively, so a loop's tail calls stay tail calls;
  - a function value of such a declaration calls a `_boxed` variant that
    releases its borrowed arguments after the call, as Lean's `_boxed`
    functions do for closures.
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
    if l2r_once_claim(28) { l2r_once_get<LStr>(28) } else { l2r_once_set<LStr>(28, l_main___l2r_0____closed__0_init()) }
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
0. before any of it (an ELF constructor, so before Rust's runtime starts),
   the runtime opens the descriptors that native Lean's runtime has open
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

`leanrt::rt::run_main2` implements the two threads and Lean's stack
overflow report: a stack overflow in either thread, so also in a task
(tasks run on them, §5.14), prints `Stack overflow detected. Aborting.` and
aborts (status 134, stdout not flushed), as Lean's handler does in every
thread. Each thread records the guard page below its stack and gets an
alternate signal stack; a fault in the guard page is an overflow, and so is
a fault below the stack while the stack pointer is below it (a frame
without stack probes, such as GMP's scratch space, can skip the guard
page).

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
use instead of cached. It cannot panic, trace or allocate, so this is
unobservable, and it is cheaper than a once-cell read (optional pass
`cheap-consts`). A closed term referenced exactly once, by another constant
(the steps of an array literal, `_closed_k := push _closed_(k-1) e_k`), is
evaluated where it is used instead of cached: it still runs once, and the
intermediate values are not kept (caching every step of a 10000-element
literal kept 1 GB of intermediate arrays). When its code and its user's are
straight-line (`let`s, then `return`), it is spliced into the user before
lowering (`spliceChainConsts`): an `n`-element literal (`#[…]`, `[…]`, a
`ByteArray`) becomes one straight-line body instead of `n` functions
calling each other (rrc compiles about 80 functions per second: a
100000-element `Array Nat` took ten minutes to build), each element's
literal placed right before its push. In that body, a run of 32 or more
small `Nat` literals pushed onto an `Array Nat` becomes one call
`l2r_natarr_lits(a, id)` that pushes the words of a table generated with the
program (`ArrayLits`); other long bodies are cut by `Outline` (§10, "Build
time"). The 100000-element `Array Nat` literal builds in about 25 s.
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
`zz._@.M._hyg.3`.

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
initializers:
- for each program module that natively is initialized, in Lean's module
  order (below), for each of its declarations that natively runs, in the
  order above:
  - an `initialize` action (`initialize do …`) is run;
  - for `initialize c : T ← act`, `act` is run and its result stored as
    `c`, which the program reads from a once-cell;
  - any other zero-parameter declaration of the module's base-phase code
    (the persisted base LCNF, so generated declarations are included),
    instances included, is evaluated;
- before those, the `initialize` constants of toolchain modules that the
  program uses (`IO.stdGenRef`), in module order.
An error from an initializer is reported like an uncaught exception of
`main` (the message, exit code 1), and later initializers do not run.
Toolchain constants are evaluated lazily, once: native Lean evaluates all
of them at startup without any visible effect. Closed terms are lazy, once.

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
`l2r_once_claim`/`get`/`set` over `leanrt::once`), holding a value that is
never freed. `l2r_once_claim` answers whether the value is there; if not,
the caller computes it, and another context of the scheduler (§5.14) that
needs it meanwhile (the computation blocked) waits until it is set, as
natively a thread waits for the one computing a closed term
(`lean_obj_once_cold` holds a lock); needed again by the context computing
it, it waits forever, as natively. A value that is not a pointer-sized boundary type is wrapped in
an `ElemBox` struct. The same slots back the runtime's mutable cells
(`l2r_cell_swap`). Reussir globals would be a cheaper replacement.

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
generated state, one type per value type `α` (and per kind, thunk or task):

```
enum L2RThunk_N { pending(L2RUnit -> ⟦α⟧), busy, done(⟦α⟧),
                  conv(L2RUnit -> ⟦α⟧, Box) }
enum L2RTask_N  { pending(L2RUnit -> ⟦α⟧), busy, done(⟦α⟧),
                  conv(L2RUnit -> ⟦α⟧, Box, u64), bind(L2RUnit -> LCell<L2RTask_N>) }
```

The state is a shared Reussir enum, so every `α` fits, closures and value
types included; a closure cannot be stored in a runtime cell directly.
`conv` is a converted thunk or task and `bind` a bind task that has not
started (both below).
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
needed. The translation is single-threaded and picks one such schedule: a
task runs when it is needed, on the stack of whoever needs it, or when the
running code blocks (*Blocking*, below).

- Every task created after `main` has started is *deferred*: its cell is
  `pending(|w| …)`, and the runtime (`leanrt::task`) records it and holds
  a reference while it is pending. For IO tasks (`BaseIO.asTask`,
  `mapTask`, `bindTask`) the computation is `act(w).val` (for `mapTask f
  t`, `f t.get`); for `bindTask t f` the cell is `bind(|w| (f t.get
  w).val)`, whose computation yields the task the new one continues as.
  Pure tasks (`Task.spawn`, `Task.map`, `Task.bind`) are deferred the same
  way; `Task.pure a` is `done(a)`. During module initialization Lean has no
  task manager and `lean_task_spawn_core` runs the computation at once; so
  does the translation (those tasks share the initializer's streams).
- A task that depends on a task unfinished at its creation (`mapTask`,
  `bindTask`, `Task.map`, `Task.bind`) is recorded as its dependent, as
  Lean's `add_dep` does, and waits for it; one of a finished task is queued
  at once.
- *Dropped pure tasks.* Lean keeps an IO task alive until it has run
  (`keep_alive`), but not a pure one: when the program drops a pure task
  before a worker has started it, Lean deletes it and it never runs. The
  runtime's reference does not count: when the runtime is about to start a
  pure task (the final run, the worker's pick below, a `sync` dependent
  released by its source) and holds the only reference to it, the task is
  dropped instead. So is one whose other references all come from pure
  dependents that are dropped themselves (`Task.spawn f` and its `map`,
  both dropped), to any depth (an iterative search over the tree of
  dependents that could be deleted: pure, held by the runtime, not
  running); the whole tree is then deleted, dependents before the tasks
  they hold, as natively the release of a dependent releases its source.
  A pure task a pending IO task still refers to runs; dropped pure
  dependents of a task that cannot be deleted are deleted once it has
  finished, when they come up (they cannot run before).
- *Priorities.* Lean passes `lean_unbox(prio)` as an `unsigned`: the
  priority is taken modulo 2^32. 2^32-1 is `LEAN_SYNC_PRIO`: such a task
  runs as soon as it is enqueued, on the enqueuing thread (an `asTask` or
  `Task.spawn` at once, before `main`'s next line, with `main`'s streams
  and thread id; a dependent as soon as its source finishes, like `sync :=
  true`). 0 to 8 are the task manager's queues; above 8 is a dedicated
  thread, which comes first here.
- A pending task runs at the first of:
  - `IO.wait`/`Task.get` of it, or a task that needs it running;
  - `IO.waitAny` on a list none of whose tasks has finished: the first
    pending task of the list runs (it is the one that finished first);
  - a program polling for it: `IO.getTaskState`/`IO.hasFinished` report a
    pending task `waiting`, until the program asks again after time has
    passed (an `IO.sleep`/`dbgSleep` since the first answer) or keeps asking
    (1000 times); the task then runs and is reported `finished`. A task
    that cannot finish without others (it waits for an unresolved promise,
    or for a task running on another context) does not run: the others go
    on once (due sleepers and timers, the contexts able to run, a queued
    task if a worker is free, as natively other threads run while the
    program polls), and its state is reported then; so is a task running on
    another context, at every question;
  - the running code blocks (a sleep, a lock, a promise, *Blocking* below)
    and a worker is free for it: it starts on a context of its own; or it
    was queued a while ago (5 ms) with a worker free, and the running code
    writes output (below);
  - `main` returning (§5.11): the queued tasks run in the order Lean's task
    manager starts them. It keeps a queue per priority and takes the first
    task of the highest non-empty one. An idle worker is woken by the first
    enqueue and picks its task once it is awake: about 90 µs later for the
    new worker thread of the first task, 20 µs for an idle one (measured
    natively with `LEAN_NUM_THREADS=1`). Tasks `main` queues back to back
    therefore compete by priority, while a task queued before some work has
    been started by then: the runtime compares the enqueue times, and the
    started task runs first in the final run. When a task a worker ran
    finishes, it picks the next one at once. A task starts only when one
    of the task manager's workers is free for it (below); `main` waits for
    the tasks running on other contexts too, as Lean's finalization joins
    its workers. `IO.Process.exit` exits at once, as natively.
- *Dependents.* A task that waits for another is off the queue until that
  task finishes. Then, whoever finished it (during `main` too), Lean
  walks its dependents from the newest (`handle_finished`): one created
  with `sync := true` (or at priority 2^32-1) runs there and then, on the
  finishing thread, with that thread's current streams (whatever the
  finished task left installed), before anything waiting for the finished
  task resumes; the others are enqueued at their priority. A `sync`
  dependent's own dependents are walked by the same loop, so a long chain
  of `sync` dependents does not recurse. A bind task that has run `f`
  finishes at once if the task `f` returned has finished, and otherwise
  waits for it, keeping its priority and `sync` flag, reported `waiting`
  (natively its closure is set again), and finishes as that one
  (`task_bind_fn1`). Dependents of a cycle are left behind, as Lean's
  workers stop when the queue is empty. A task needed while the tasks it
  waits for are pending first runs that chain from its deepest end, one
  task after the other, so a long chain does not recurse.
- `mapTask`/`bindTask`/`Task.map`/`Task.bind` with `sync := true` of a
  finished task apply `f` at once in the calling thread (its streams too),
  as `lean_task_map_core`/`lean_task_bind_core` do.
- `IO.cancel` sets the flag of an unfinished task; when a canceled task
  finishes, the tasks created while it was unfinished that depend on it
  are canceled too, as Lean's `handle_finished` does. `IO.checkCanceled`
  answers for the innermost running task, and is false in `main`. When
  `main` returns, Lean sets its shutdown flag, which makes
  `IO.checkCanceled` true. A task that was queued then could have been
  started by a native worker before the flag was set, so it sees the flag
  only once time has passed in it (a sleep) or from its second check on;
  so does a task it creates or releases (a dependent) before time has
  passed in it. Any other task of the final run (a dependent of a task
  still pending when `main` returned, a task created by a task that has
  slept, a bind continuation created then) could only start after the
  flag was set and sees it at once.
- *Closed terms.* Lean evaluates a closed term once, at its first use, and
  then marks it persistent (`lean_mark_persistent`), which waits for every
  task it reaches. A closed term whose type may hold tasks runs its tasks
  right after it is evaluated (`l2r_persist_T`), whether they are in
  fields, arrays, the values of tasks, the values captured by function
  values (partial applications), thunks (their computation, or their
  value: the thunk is not forced), references (their value) or boxed
  values; so `Task.spawn` of a closed function has finished once the term
  has been used. The walk
  works as Lean's does: a loop over a list of the values still to look
  at (no recursion, so a value deep through any field is walked at a
  bounded depth), which visits each cell once (the runtime keeps the set
  of addresses visited: a value whose cells are shared, a DAG, is walked
  in time linear in its number of cells, not of its paths). Natively,
  waiting for a task only blocks (`wait_for`): the term's tasks, which have
  usually not started yet, are run by the workers in their queue's order
  (a higher priority first, then first in, first out), whatever order the
  walk waits in, and their traces and panics come in that order. Here a
  pending task runs when it is waited for, so the walk has two passes. The
  first collects the unfinished tasks it reaches (without looking into
  them: their values do not exist yet). The second walks the value again
  in Lean's order (it pushes an object's fields, a closure's captured
  values and an array's elements in order and pops the last one first;
  fields in Lean's declaration order, whatever the record layout) and,
  before it waits for a task, runs the collected tasks that come before it
  in the workers' order: by priority, then in the order they were created.
  So `(List.range 4).map (Task.spawn …)` runs its tasks 0, 1, 2, 3 (test
  `RtPersistOrder`). The order of the second pass still matters: what it
  reads out of a reference or a thunk is read when it gets there, so a task
  that replaces the task a reference next to it holds has run by then, as
  natively. Only collected tasks run early: other pending tasks of the
  program, which a native worker would run first too, are not run (one
  could wait for something the program does later). The walk
  keeps what it reads out of thunks, tasks and references until it ends, so that no
  cell it has visited is freed meanwhile (a task it runs could force a
  thunk, which drops its computation) and its address given to a new
  cell. It is skipped when every task of the program has finished
  (nothing to wait for): always for constants evaluated at startup, where
  tasks run at once. The walks are generated at the end of lowering, once
  every variant of the function types and of `Box` is known, and do
  nothing for types that cannot hold a task. Values captured by a Reussir
  closure (only lean2rr's own glue makes them, not Lean code) are not
  looked into.
- A thunk or task stored at another representation (in `Box`, §5.1) is
  converted to a new cell. One that has its value gives a cell in state
  `done` with the converted value. Otherwise the new cell is in state
  `conv(g, o)`, for a task `conv(g, o, a)`: `g` forces the original and
  converts its value (so it still runs at most once); `o` is the original
  cell, boxed, so that converting the copy back gives that very cell (a
  thunk crossing between typed and uniform code in a loop stays one cell
  instead of growing a chain); a task's `a` is the original's address, the
  copy's identity for the runtime, so the copy's state (`IO.getTaskState`,
  `IO.hasFinished`), waiting for it, `IO.cancel` and cancellation, its
  priority and its dependents are the original's. The copy has no running
  state of its own: it stays `conv` while it is forced, and forcing it
  again meanwhile runs `g` again, which waits for the original if that is
  running and has the original's value once it has finished. (A copy that
  went `busy` would be waited for until its own computation ends; but the
  original's end walks its `sync` dependents inside that computation, and
  one that forces the copy, as natively it may read the finished original,
  would wait forever.) A forced copy stores `done(v)` and lets the original
  go; the original has finished then, which is what the runtime answers
  for the copy's own cell from then on. A copy of a copy records the first
  original, and converting it to a third representation converts the
  original directly, so chains stay one level deep. The copy is a cell of
  its own for `ptrAddrUnsafe` (§9).
- *Promises* (`IO.Promise α`, `lcAny` in mono code) are a runtime object
  (`LPromise`) holding the cell of their task, a task over `Option Box`
  whatever `α` is, so that typed and uniform code share it. The task stays
  unresolved (status `running`, as natively) until `Promise.resolve`, which
  stores `some v` (only the first resolution counts) and walks the task's
  dependents on the resolving thread, as Lean's `resolve_core`.
  `Promise.result?` converts the task to `Task (Option α)`, and
  `Promise.result!` maps `Option.getOrBlock!` over it, as natively.
  Dropping the last reference to an unresolved promise resolves it with
  `none` (`deactivate_promise`, through the runtime's finalizer of the
  promise object). Waiting for an unresolved promise blocks (below): other
  contexts and queued tasks run, as other threads would meanwhile, until
  one resolves it; when nothing can any more, the wait lasts forever, as
  natively. Polling a promise (`isResolved`) lets them go on once per
  question once time has passed, and `IO.waitAny` does not run a pending
  task that waits for an unresolved promise (or for a task running on
  another context). `IO.Promise.new` during initialization is Lean's
  internal panic.
- *The event loop* (`leanrt::net`): timers, sockets, name resolution and
  signals, as libuv's loop natively on a thread of its own. An operation
  that completes later (a timer firing, data received, a connection
  accepted) gets, from the shim, a promise `r` of `Unit` and a `sync`
  continuation on `r` that resolves the program's promise; when the
  operation completes, the runtime stores its outcome and drops `r`, which
  resolves it with `none` (`deactivate_promise`) and so runs the
  continuation, on the event loop's own context, as libuv's callback
  natively runs on libuv's thread (its `sync` dependents too, the others
  are queued). The scheduler polls the descriptors and timers when nothing
  else can go on, and fires a due timer at the program's next output.
  Sockets follow libuv's Unix code (descriptors created on `bind`,
  `connect` or `listen` with the address's family, nonblocking;
  `SO_REUSEADDR` before a TCP bind, whose `EADDRINUSE` `listen` reports;
  an `accept` with a connection waiting completes at once; writes complete
  through the loop). Name resolution calls `getaddrinfo`/`getnameinfo`
  at once (natively on libuv's thread pool) and completes through the
  loop. Signals are caught by a handler that writes to a pipe the loop
  watches; stopping the last watcher of a signal restores its default
  action, as libuv does. `Std.Async` (`Async`, `sleep`, `Interval`,
  `Selector`, TCP and UDP clients and servers) is Lean code over these.
- *Standard streams.* Natively each thread has its own current standard
  streams (`IO.setStdout` & co. replace the current thread's, which start as
  the process's), and a task runs on a worker thread. So a task starts with
  the process's streams, and when it ends the streams of whoever ran it are
  back (`l2r_std_enter_if`/`l2r_std_leave_if` set the stream cells aside and
  restore them). A task that runs on the current thread (a `sync`
  dependent, priority 2^32-1) shares that thread's streams. `main`, on its
  own thread, starts with the process's streams whatever the initializers
  installed (§5.11). Natively a worker keeps its streams from one task to
  the next, so a task that leaves a redirection behind can affect the next
  task on the same worker; the translation behaves as if every task (other
  than a `sync` dependent) ran on a fresh worker.

*Blocking.* A thread that blocks natively (a mutex another thread holds, a
condition variable, `IO.wait` of a task another worker runs or of an
unresolved promise, a channel, a socket, `IO.sleep`) lets the others go on.
A task that is needed runs nested on the stack of whoever needs it, but
then everything below it would have to wait for it too. So the runtime has
*contexts* (`leanrt::sched`, `coro`): `main`'s (its thread's stack) and one
per task the scheduler starts, each on a stack of its own of the size of a
native worker's (1 GiB, or `LEAN_STACK_SIZE_KB`, reserved but not
committed, with a guard page that reports Lean's stack overflow). When the
running context blocks, it is suspended, and the scheduler runs, in this
order:

1. a suspended context that can go on (its lock was handed to it, it was
   notified, the task or promise it waited for finished, its sleep ended),
   in the order they became able to;
2. a queued task, on a new context, in the order `next_tag` would start it
   (above), if one of the task manager's workers is free: their number is
   `LEAN_NUM_THREADS`, or the number of online processors, as natively
   (`std::thread::hardware_concurrency`, not limited by the CPU affinity
   mask); a context
   running a task at a priority up to `Task.Priority.max` holds one, except
   while it waits for a task or promise (Lean's `wait_for` lets another
   worker start then); a dedicated task (priority above 8) has a thread of
   its own and always starts;
3. the event loop's timers and sockets (`leanrt::net`, below) and the
   sleepers, waiting for the first of them.

When nothing can ever go on, the program waits forever, as a deadlocked
native one does. A context does not lose the processor otherwise, except at
*effect points* (output to a stream or file, `IO.Process.exit`) and
`IO.sleep 0`: what natively would have run by then on other threads goes
first: a context whose sleep is over, a due timer of the event loop and
what its completion releases (its continuations, the contexts waiting for
it, the tasks it queues, which a free worker starts at once), descriptors
and signals that have become ready (polled at most every 50 µs: a system
call at every output would cost more than the output), a context able to
go on for a while
(5 ms: a lock handed over, a promise resolved), a task queued a while ago
(5 ms) with a worker free for it (thread wake-ups take microseconds, so
these would have got past anything that takes no time); then, round after
round (up to 64), what those release in turn. What runs in those rounds
happened before natively: its own effect points start no tasks, and let
go first only what is due or able to run for a while (the context that
let it run, once it has computed for 5 ms). So sleeps and timers order
the output of tasks by time, as natively, as long as code between two
outputs takes less time than the sleeps that order them, and a context
that computes for a while lets the others print first. A `sleep 0` lets
those run whatever their age (a queued task after a worker's wake-up
time). Spawning a process and flushing a handle are effect points too.

A thunk being forced on one context and needed on another (the first
blocked in its computation, or let others run at an effect point) is
waited for until it has its value (`l2r_thunk_wait_busy`, woken by
`l2r_thunk_done`), as natively a thread waits for the one forcing it.

`LEAN_NUM_THREADS` is read as Lean reads it (`atoi`, taken as an
`unsigned`): 0 (or not a number) is no task manager: tasks run at once, as
during initialization, and `IO.Promise.new` is Lean's internal panic.

A pending task that waits for one running on another context is natively
its dependent: it runs, or is queued, when that one finishes. So `Task.get`
of it waits until that one has finished and looks again (it does not run
the dependent at once, which would then wait inside its own computation:
its state, cancellation and `sync` thread would differ).

Each context has what a thread has: its running tasks (`IO.checkCanceled`,
`IO.getTID`), the walks of dependents it does, its current standard streams
(saved and restored at a switch: the cells of `l2r_std_*`, which the
runtime records as mutable). No context is suspended inside a free (the
free's pending work is the thread's, Reussir's `reussir_rt::drop`, and
the other contexts would push their frees onto it). This decides when the
`sync` dependents of a promise dropped unresolved run (natively at once,
on the dropping thread, wherever that happens):
- a promise whose last reference is released by itself (not inside a
  free) is resolved with `none`, and its dependents run at once, as
  natively;
- a promise held by a container being freed (an array, a list, a
  structure, a map, an `Option`, ...) is resolved in its turn, and its
  dependents are walked as soon as the free is over (natively during the
  free, when it reaches the promise), before the code that released the
  container goes on. The runtime sees the end of a free that it started
  itself (`leanrt::drop::run`): one of its containers (an array, a
  reference cell, a task or thunk cell), or the old value of a reference's
  `set` (below); and of any free through local Reussir patch 0040
  (`__reussir_drop_drained`, which every drain calls when it ends).
  Without that patch, the end of a free that Reussir's record glue started
  (a structure, list or `Option` that the program's own code releases) is
  not seen: those dependents run at the context's next effect point,
  block, Std.Sync wait (before the object is looked at, so that a release
  by them is not lost) or question about a task (§10).

A reference's `set` stores the new value before it releases the old one,
as `lean_st_ref_set` does (Reussir's `cell::set` releases first): code that
the release runs sees the new value. It releases the old value as
`lean_dec` does (`leanrt::drop::release`, through the prelude's
`l2r_release_value`): a shared value is only decremented, and the last
reference to a record is freed inside a free the runtime starts, so what
it holds goes in Lean's order (its last field first, as Reussir's glue
would not do for the first cell of a free it starts) and the dependents of
the promises it drops run when that free ends, before the next statement,
with or without patch 0040. The same holds for the old state of a task or
thunk cell (`l2r_lcell_set`).
`Task.get` of a task that is `busy` because it
runs on another (suspended) context waits until it has finished
(`l2r_task_wait_running`, then it looks again); on the running context it
needs itself, and waits forever, as natively. `IO.waitAny` when every task
of its list is running waits until some task finishes
(`l2r_task_wait_progress`) and looks again.

Why tasks are deferred rather than run at creation: a task may wait for
`main`. `IO.asTask (do while !(← flag.get) do IO.sleep 1; …)` followed by
`flag.set true; IO.wait t` finishes natively; run at creation, the task
would spin forever. Running at creation also prints the task's output
before `main`'s next line, which natively comes first when the task starts
with a sleep, and computes pure tasks the program then drops. A task that
runs only when needed never waits for something that is still to happen.

What a single thread cannot do:
- a context that waits for another without blocking (a loop polling an
  `IO.Ref` that another task sets, without `IO.sleep` or output in it) does
  not let the others run, and does not terminate; with a sleep in the
  loop, it does;
- contexts do not run in parallel: one that computes without output or
  blocking delays the others (output ordered by time comes in time order
  only as far as the code between outputs is shorter than the sleeps), and
  `IO.waitAny` does not pick the fastest of several unfinished tasks;
- tasks nobody waits for stay queued, with what they hold, until `main`
  returns (a chain of 4·10⁶ `mapTask`s built by `main` takes 0.7 GB, as
  natively with one worker; with free workers native Lean runs it as it is
  built), and a dropped pure task keeps its memory until the runtime would
  start it;
- a task needed by `main` runs at once, where a single native worker would
  first finish the tasks queued before it, and a task the worker would
  start right after one `main` waits for runs only when `main` returns or
  needs it, after `main`'s next lines;
- Lean's panic for `Task.get` inside a `sync := true` task is not
  reproduced;
- a deferred task is reported `waiting` at the first question even after a
  sleep, when no worker was free to start it meanwhile (a pure task
  deferred behind a pending IO task, for example);
- a task or context that starts or goes on late counts its sleeps and
  timers from then (above).

Tasks that wait for each other in a cycle wait forever, as natively.

---

## 6. Runtime (`leanrt`)

The runtime provides what Reussir lacks:
- `Nat`/`Int`: a small value, or a GMP bignum (`leanrt::big`);
- Lean's `String` operations over UTF-8 bytes (one block with the character count, §5.1);
- `Array`/`ByteArray`/`FloatArray` operations over the copy-on-write `Vec`;
- `Float` math through libm;
- IO: stdout/stderr/stdin streams, `IO.Error`, argv, exit;
- the mutable cells of thunks and tasks, the queues of deferred tasks, and
  promises (§5.14);
- panic, trace;
- once-cells for constants.

Everything runs on one thread: tasks are deferred until needed (§5.14),
which gives one of the schedules native Lean can produce. Real
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
- a cheaper `Nat`;
- borrowed parameters, if Reussir adds them;
- globals for constants;
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
  enumerations without fields, and `Nat`/`Int`, whose arms each hold one
  64-bit word. Everything else with several arms is a shared enum (J4
  entry points, §5.6); multi-field value records are `[value]` structs,
  whose padding is explicit.
- **Candidate Reussir requests.** Guaranteed tail calls; `[value]` types
  across the FFI (for `Nat` array elements without a wrapper); borrowed
  FFI parameters (an array `get` currently takes ownership and releases);
  a no-inline attribute (lean2rr uses `#[transform_anchor]`, whose
  `no_inline` is a side effect, docs/reussir-bugs.md bug 20); small
  integers as immediates (for one-word `Nat` fields); bounded-depth frees
  (local patches 0013-0015).

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
    array, a big number, a reference, a thunk or task, a runtime handle):
    the address of its cell, whatever its count (`l2r_ptr_addr_rec`,
    `l2r_ptr_addr_obj`); a nullary constructor of a shared enum: its
    immediate;
  - a `Nat` below 2^63, an `Int` in the `int32` range, `UInt8/16/32`,
    `Char`, `Bool`, an enumeration: the boxed scalar's word `2n+1`;
    `Unit` and erased values in typed code: `1` (in uniform code an erased
    value is a `Box`, the boxed unit, which answers its `Box` cell);
  - `UInt64`, `Float`, `Float32`: their bits;
  - a `[value]` struct: its field's;
  - a `Nat` from 2^63 to 2^64, an `Int` outside `int32` (no cell, and too
    wide for a word): a number answered only once (`l2r_addr_fresh`: even,
    in [2^62, 2^63), so never a word or a pointer).

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
  cell here: a value
  converted to another representation (§5.1) is a new object, so it is not
  `ptrEq` to its original, nor are two conversions of one value; two
  boxings of one value are two `Box` cells; a function value wrapped for
  another representation (§5.3) and a converted thunk or task (§5.14) are
  cells of their own; an arm rebuilt by `fresh-rebuild` (§5.5) is a new
  cell; equal `UInt64`s, `Float`s and small numbers are `ptrEq` (natively
  each boxing of a `UInt64` or `Float` is a new cell). So code that stops
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
  Lean's library or its own shim (constants evaluated lazily,
  initializers run by the runtime, `unsafe` code trusted, §5.1, §5.12). A
  module of those names is the library's when its files (`.olean`, and
  the `.olean.server` and `.olean.private` parts) are the same files as
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
- *Tasks* run on one thread, when they are needed, when the running code
  blocks (a sleep, a lock, a condition variable, a promise, a socket) or
  when `main` returns (§5.14). Contexts never run in parallel and switch
  only when one blocks or at an effect point (output, an exit,
  `IO.sleep 0`), to what natively would have run by then (a due sleep or
  timer, a context able to run or a task queued 5 ms ago or more): a loop
  polling shared state that another task sets never sees it change unless
  it sleeps or prints, a context that computes without output or blocking
  delays the others (so output that sleeps order natively comes in time
  order only as far as the code between outputs is shorter than the
  sleeps; a context or task made able to run less than 5 ms before an
  output comes after it, natively a race), and `IO.waitAny` does not pick
  the fastest task. A task or context that starts or goes on late (at an
  effect point, when the running code blocks, in the final run) counts its
  sleeps and timers from then, natively from when a worker started it: a
  task queued long before an effect point that then sleeps 30 ms prints
  30 ms after that point. A pure task the program drops before any effect
  point or block is deleted, even where a free native worker would already
  have started it, and `IO.checkCanceled` at shutdown follows the
  heuristics above (§5.14), not the time a task natively spent before
  `main` returned. A deferred
  task is reported `waiting` at the first `IO.hasFinished`. The order of
  the final run is that of Lean's task manager, whose first pick is timed
  against a native worker's measured wake-up latency (about 90 µs, 20 µs
  when idle): tasks created about that far apart can come in either order,
  as natively. Tasks other than `sync` dependents run as if
  each had a fresh worker thread, so a redirection a task leaves behind
  never reaches another task (natively it can, on the same worker);
  `IO.getTID` inside a task is main's thread id plus a worker number (a
  `sync` dependent's is its source's), as distinct from main's as a
  worker's. A task needed before tasks queued earlier runs before them
  (`y.get` before `x.get`, `x` created first, runs `y` first; natively a
  worker takes `x` first, always with one worker), except the tasks a
  closed term waits for when it is first evaluated, which run in queue
  order (§5.14). A closed term does not wait for the task of a promise in it
  (Lean's `lean_mark_persistent` does, and waits forever for an
  unresolved one; a closed term can hold a promise only through unsafe
  code).
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
- *Merging after erasure*: natively, two uses of a type-polymorphic
  constant at different type arguments (`(emptyList : List Nat)`,
  `(emptyList : List String)`) are the same call after erasure, and Lean's
  CSE merges them; lean2rr's instances are different calls. Visible only
  when such a value traces or panics.
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
  values itself; Reussir bug 10), and lean2rr keeps the conversions,
  unboxings and the applications of wrapped and uniform function values
  out of rrc's MLIR inliner (§5.3; bug 20). The towers of the adversarial
  rounds then build in 15 s to 2.5 minutes and at most 3 GB, the whole
  build (a single `StateT` tower used at `IO`: 21 s, 0.4 GB, where it did
  not build in 30 minutes; five towers in one program: 70 s, 1.5 GB, where
  they took 15 minutes and 7.5 GB). rrc's costs also grow faster than
  linearly in the depth of nested matches (reuse across calls; every IO
  bind nests one) and in the length of straight-line code on `Nat`
  (Reussir bugs 16 and 17). So after lowering, a function with a tail path
  32 matches or `if`s deep, or 256 `let`s long (a long `main`, a 3000-arm
  literal match, a long `do` block), or with a `let` whose value is that
  deep or long, is cut (`Outline`): once a tail path is 8 levels deep or
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
  1.5 GB, a recursive function with a 3000-arm match in 80 s. Many
  instantiations of one inductive in `Box`es (K structures of one shape
  through polymorphically recursive code) make K unboxing functions of K
  arms each, and rrc compiles each generic runtime function instantiated
  at a type with its own rustc run: 80 such structures build in about
  3 minutes (§5.1). `Outline`
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
  `Box` only, a cast whose conversion would need a function value at
  another representation, or between inductives whose constructors do not
  all correspond (another number of constructors), which typed code
  converts (§5.1). Also out of reach: a cast that reads part of a scalar
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
  another representation or another cell here (a value converted to
  another representation and its original, two conversions or two
  boxings of one value, a wrapped function value, a converted thunk or
  task, an arm rebuilt by `fresh-rebuild`), and equal `UInt64`s, `Float`s
  and small numbers are `ptrEq`. `ptrEq` answering `true` still means
  equal values, and `ST.Ref.ptrEq` is exact. `dbgTraceIfShared` reports
  lean2rr's counts (below, Runtime).
- *Order of releases in one free*: when a value holding several resources
  is freed at once (handles closed, and so flushed; promises resolved),
  native Lean releases them last pushed first: an array's last element
  first, a nested array's elements before the elements before it, a
  record's last field first. Here the runtime's containers (`leanrt::drop`)
  and Reussir's drop glue for records (local patch 0014) push what they
  free on one stack of pending work per thread, so the order is Lean's
  inside every free that starts at a container (an array, a reference, a
  thunk or task cell), through any records (tests `RtDropOrder`,
  `RtDropOrderRec`), and mostly below the first cell of a free that starts
  at a record. That first cell is the difference. When user code drops a
  record by itself (a list, tree or structure of handles), Reussir's
  inline release in the user's function releases its fields in field
  order, each completely before the next. Natively the order depends on
  where the value is dropped: where Lean's code knows the constructor
  (`lean_dec_ref_known`, e.g. a structure it has just built), the fields
  go in field order too, each completely; elsewhere (`lean_dec`) they go
  last first. lean2rr's code does not drop values where Lean's does: where
  Lean borrows a parameter and drops the value in the caller, lean2rr's
  function takes the value and releases it as it destructures it. So a
  value dropped by itself can come out in the other order: a list of
  handles `L0 … L7` is closed `L0 L7 L6 … L1` (natively `L7 … L0`), and a
  tree's left subtree goes before its handle and its right subtree. No fixed
  order of the fields in Reussir's releases matches both cases. Reversing
  it was tried: that fixes these cases but breaks the field-order ones and
  the order inside containers. One case below the first cell also differs:
  a record that the first cell holds is released through its drop function
  while no free runs, and that function frees a container field (an array,
  a reference, a thunk) as soon as it reaches it, before the record fields.
  So a structure `{a : Array Handle, l : List Handle}` in a list dropped by
  itself closes `A1 A0 L1 L0` (natively `L1 L0 A1 A0`).
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
  no recursion of its own: structural conversions are loops (§5.1), the
  `Array.mk`, `String.mk` and `String.ofList` list folds are tail-recursive
  loops, and the walk of a closed term for its tasks (§5.14) is a loop over
  a work list, so converting or folding a list of 10⁷ elements, or walking
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
  releases the last record member being freed in a loop (0013) and pushes
  the other record members being freed on the same stack (0014), so a
  value deep through records too is freed at a bounded depth: a list, a
  snoc list, a binary tree deep along its left child whose right children
  are fresh nodes, a rose tree in uniform code (test `RtDropGlue`, 10⁶
  levels at an 8 MB stack). The depth at which
  `Stack overflow detected. Aborting.` (exit 134) happens is not native's,
  in either direction (the report itself is, in every thread: §5.11).
  Tasks run on `main`'s thread (Lean's 1 GiB, or `LEAN_STACK_SIZE_KB`),
  where native task workers have the same size of stack each.
- *Stream redirection* (`IO.setStdout`, `setStderr`, `setStdin`,
  `IO.FS.withIsolatedStreams`) is translated: the current streams live in
  cell slots, and panics, `dbgTrace` and `timeit` write through the current
  stderr stream (`l2r_stderr_put`), as natively, and per thread as
  natively: a task, and `main` after the initializers, start with the
  process's streams (§5.14).

**Cost** (time and memory, not results)
- *No borrowed parameters* (§5.8, §7): a parameter Lean borrows is owned
  here, so a traversal that keeps the nodes it visits (an `Expr.replace`
  over a DAG that replaces nothing) increments and releases the fields of
  every node it keeps, and every `ptrEq` operand: 1.5x native on such a
  traversal (adv4 RP4-09).
- *Structural conversions* (§5.1) rebuild a value as a tree: sharing is lost,
  so a DAG costs exponential time and memory, and a conversion on every call
  costs O(size) per call, also when the value goes back to the
  representation it came from (a round trip through uniform code converts
  twice); a conversion through an explicit stack (a tree, a rose tree)
  allocates a stack frame per node. Past the instance caps of §2.6 this can
  happen inside loops. Running out of memory changes the exit status. Values of
  types with the same layout are not converted (`l2r_retype`); a cast
  between layouts that differ (an `Array T₁` field read at `Array T₃` whose
  elements hold an `Int` where `T₁`'s hold a `Nat`) converts the field at
  each use, where natively the cast is free.
- *`Array.map` that changes the representation* (for example
  `(Array.range n).map (· % 3 == 0)`) reads the input and pushes onto a new
  result array (§4): the two arrays are live together until the map ends,
  where native Lean replaces the elements of one array (peak memory
  0.7–1.1x native for scalar targets in tests, more for records, whose cells
  are larger: §7's cheaper `Nat`). Maps that keep the representation run in
  place. A map loop of another shape (not Lean's), or one whose function
  projects a field of a parametric structure (`(xs.zip ys).map (·.2)`,
  §4), still converts its input to an array of `Box` on entry and back on
  exit.
- *Element storage*: array elements, once-cell values and polymorphic
  extern arguments whose type cannot cross the FFI boundary (`[value]`
  tuples, closures) are wrapped in an `ElemBox` cell, one allocation each;
  enumerations and `Unit` in arrays are stored as indices, but once-cell
  values and other extern arguments of those types are still wrapped.
  `ST.Ref` contents are stored in their own representation (§5.1), except
  `[value]` structures (an `ElemBox` per `set`); a `Nat` reference keeps a
  big number it held until it is replaced by another big number or the
  reference dies. A reference used through a `Box` costs a dispatch on its
  type at each operation. `UInt64` and `Float` arrays, on
  the other hand, are unboxed, unlike native.
- *Reads take their container owned* (Reussir has no borrowed FFI
  parameters, §9): every array or string read is an increment by the caller
  and a release in the inlined runtime function. LLVM cancels the pair when
  the increment's store reaches the release with no store or call on any
  path in between (Reussir's `rc.inc` lets it assume the old count was at
  least 1; the prelude ends the impossible `Nat::Big` index paths instead of
  rejoining them for this): index loops and insertion sort on
  `Array UInt64` run at 1.2x native or better. It does not when a
  structure field projected at the top of a loop body is released by the
  iteration's last read, as in Lean's `String.Slice` loops (`String.any`,
  `contains`, `toNat?`): 1.7x native (Pf4MinStrAny; 1.1x with the projection
  moved by hand to its first use); insertion sort on `Array Nat` keeps
  the count's stores and reloads it for the swap's uniqueness check: 2.1x.
- *Generic arrays* (`RVec`) are two allocations, a 32-byte counted box
  (Rust's vector: capacity, pointer, length) and the element buffer, where
  a Lean array is one object with a 24-byte header: a small array costs 8
  bytes and one allocation more than natively (an `Array String` of three
  elements: 32 + 24 bytes, natively 48). `Array Nat`/`Array Int` (one block
  with Lean's header) and strings (one block with Lean's 32-byte header)
  are laid out like Lean's objects: six million three-element `Array Nat`
  rows take native memory (Pf4SmallArrs 0: 328 MB, native 330 MB; 421 MB
  with the earlier 40-byte header), and five million short live strings
  take 270 MB (Pf4ManyStrs; native 352 MB; 306 MB as two allocations, a
  counted box and a byte buffer).
  `String.toUTF8` and `String.fromUTF8` copy the bytes, as natively.
- *Dropping a large array of records*: the runtime decrements shared
  elements inline (as `lean_del` does natively) and frees the array
  without the stack of pending work when no element is freed; an element
  whose last reference it holds goes through Reussir's out-of-line
  `<record>_ffi_release` (`leanrt::drop`, `ReleaseElems`). The Reussir
  suite's `hash-map-heavily-shared`, which frees an old version of its
  bucket array after each update while a parked version is live, went from
  1.79x native to 1.05x with this.
- *Constants read in a loop* (a top-level `Array` or `String` table)
  check their once-cell on every read: Pf4BigLit 1.16x native.

**Runtime** (details in `runtime/README.md`, "Known divergences")
- Sharing is not observable: `isExclusiveUnsafe` answers `false`;
  `dbgTraceIfShared` reads lean2rr's own counts (a converted value is a
  new, unshared object, §5.1); `shareCommon` shares nothing, and
  `ShareCommon.Object.eq` compares addresses (§9: at most the same cell;
  natively also two objects with the same fields; `L2RShim`), so an
  object converted at each call (a value cast to `ShareCommon.Object`) is
  not even equal to itself, and its hash can change.
- `IO.getNumHeartbeats` is 0; `dbgStackTrace` prints nothing; a panic's
  backtrace line is `(stack trace unavailable)`.
- `errno` after a sticky handle error can differ.
- Child processes (§5.8): code that reads one of a child's pipes in a task
  while it reads the other (as `IO.Process.output` does natively, stdout
  in the task; its glue here reads both together) deadlocks if the child
  writes more than a pipe holds to the task's pipe before closing the
  other one, since the task runs only when its value is needed. Natively `Child.pid` leaks the child, so its pipes stay open
  forever (a child waiting for end of file on stdin then hangs); here they
  are closed as usual. Natively the `Child` from `takeStdin` loses the
  `setsid` flag (`kill` reads uninitialized memory); here it keeps it.
  `output` reports a non-UTF-8 stderr once both pipes are at end of file
  (natively as soon as stderr is: different timing when a grandchild holds
  stdout open), and a read error on either pipe at once (natively a stdout
  read error after `wait`).

**Diagnostics**
- lean2rr's own impossibilities (a `Box` unwrap of another variant, a cast
  with no conversion) print Lean's `INTERNAL PANIC: unreachable code has
  been reached` and exit 1, like a real unreachable.

- *Blocking system calls* (reading a file, a pipe or standard input,
  waiting for a child process) block the whole program, where natively
  only the calling thread waits: a task reading a pipe that another task
  of the program writes, or that a child writes only after the program has
  done something else, waits forever. Name resolution
  (`Std.Async.DNS`) runs `getaddrinfo` at once, so a slow lookup holds up
  the other tasks and timers meanwhile (natively it runs on libuv's thread
  pool).
- *Event loop details* (§5.14): libuv accepts a waiting connection on
  its own when no `accept` is pending, and keeps it; here it stays in the
  kernel's queue until an `accept` (only descriptor numbers and `EMFILE`
  can tell). Timers count from the monotonic clock when they start
  (libuv from its loop's cached time, which can make a timer fire a little
  earlier). A promise the loop gives up without resolving it (a timer
  re-armed, an operation whose start failed) is released on the loop's
  context, at its next turn, where natively the C function releases it at
  once: when that was the last reference, the promise is resolved with
  `none`, and its `sync` dependents run, that much later (generated code
  does not run inside a runtime primitive). A timer's or signal watcher's
  `stop` and `cancel`, and a socket's `cancelAccept` and `cancelRecv`
  (also of a `waitReadable`), hand the promise back to the extern's glue,
  which releases it on the caller's context once the primitive has
  returned, as natively in the call (tests `RtTimerStopDropped`,
  `RtSockCancel`). Natively these calls hold the event loop's lock while
  they release the promise, so a `sync` dependent that blocks there for
  good (`Promise.result!` of the dropped promise) also stops every timer
  and socket of the program; here only the calling context blocks.
- *Promises released inside a free* (§5.14): the `sync` dependents of a
  promise dropped unresolved because a container holding it is freed run
  once the whole free is over, where natively they run when the free
  reaches the promise: they see the rest of the container released too
  (a file handle held by a later element already closed, another promise
  in it already resolved). Without local Reussir patch 0040, a free that
  Reussir's record glue started (a structure, a list after its first cell,
  an `Option` that the program's own code releases; not the old value of a
  reference's `set`, which the runtime frees) ends unseen, and its
  promises' dependents run only at the next output, block, Std.Sync wait
  or question about a task: code in between (reading a reference the
  dependent sets, a computation, a blocking system call) runs before them.
  A condition-variable loop that reads its condition before it waits
  (`while !(← c.get) do cv.wait m`) then waits forever when such a
  dependent was to set the condition and notify: the dependent runs at the
  wait, after the condition was read, and notifies no one.

**Not supported** (translation succeeds; `rrc` reports an unknown function)
- Every constant of the program is translated (§2.2), so an unused constant
  that reaches an unsupported extern makes the whole program fail to link.
  A program is therefore translated by lean2rr, but links only if the
  runtime implements every extern it reaches.
