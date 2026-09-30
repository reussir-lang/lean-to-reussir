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
built only from instance constants and types (and projections of such). The
instance key then includes the dictionary. The callee's instance binds that
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
  infinitely many instances. This is detected at the first self-call whose
  type arguments strictly contain the caller's: that call goes to the fully
  uniform instance (every type argument `lcAny`, static dictionaries
  dropped). Other growth, such as mutual polymorphic recursion, is cut by
  bounds: a type argument deeper than 64 or larger than 256 nodes becomes
  `lcAny`, and past 1024 instances of one declaration every further
  instance is the uniform one. So the set of instances stays finite. This is
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
  element types the conversion is element by element.
- A `box(0)` placeholder is a value that is never inspected. It arrives as
  a unit-like value used at another type, or as `◾` at a relevant type.
  Stage 4 materializes it as the *zero* of the expected type: `0`, `false`,
  the first constructor whose fields have zeros, a closure returning a zero,
  an empty array. For `Nat`, `Bool` and enumerations this is exactly what
  `box(0)` denotes in Lean. Only a type without a finite value gets
  `unreachable`.

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
representation. The rule is syntactic: `fun n => Fin n` also stays
`lcAny`, although every `Fin n` is a `Nat`. Every mono type lean2rr
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
  `f._closed_N`.

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

Mono can still lose type information in a few places. Types inferred
*during* the passes go through erased signatures; for example, a
constructor's mono signature is `List.cons : lcAny → List lcAny → …`. Where
a binder ends up with `lcAny` in a position that holds data, its exact type
is recovered from its context, and only when that context determines it:
- a `cases` field: the constructor's field type, instantiated at the
  discriminant's type;
- a constructor application: from its argument types;
- a call: from the callee's exact signature, which all our instances have;
- a join-point parameter: from its jump arguments, when they agree.

Where the context does not determine the type, the binder keeps `lcAny` and
uses the uniform `Box` representation (§5.1), with conversions where it meets
a precise type. Recovery is therefore an optimization that avoids boxing, but
it must be exact: a recovered type is always the binder's real type.

Stage 3 also checks the structural facts Stage 4 relies on:
- join points are not recursive, and jumps are in tail position;
- no local functions remain;
- every `cases` covers all constructors or has a default.

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
| `String` | `LStr`, an opaque copy-on-write handle over UTF-8 bytes (`Rc<Vec<u8>>`) | literals: §5.4 |
| `Array α` | `RVec<S>`, the runtime's copy-on-write vector | in place when unique. `S` is the storage type of `α`: `⟦α⟧` itself if it can cross Reussir's FFI boundary (scalars, `bool`, runtime handles, shared records), otherwise a generated one-field shared struct `ElemBox` around it (Lean boxes array elements too) |
| `Array Nat`, `Array Int` | `LNatArr`, `LIntArr` | one word per element like Lean's boxed scalars: small values inline, big ones as bignum handles; the array functions are the `natarr`/`intarr` counterparts of the generic ones, with the same arguments |
| `ByteArray`, `FloatArray` | `RVec<u8>`, `RVec<f64>` | |
| `ST.Ref σ α` | `LRef<Box>`, a shared mutable cell | mono types a reference as `lcAny`, so it travels boxed. Its contents are boxed too, whatever `α` is: uniform code (`α = lcAny`) and typed code can share one cell, and a cell cannot be converted without losing aliasing. Each `set` allocates the box. |
| `Thunk α`, `Task α` | generated one-field structs | a thunk is forced when built; a pure task is computed when spawned (§6) |
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
  (`[shared]`), like Lean's.
- **Field order.** lean2rr orders each constructor's fields by decreasing
  alignment (ties in declaration order), so records have no padding; the
  layout maps each Lean field to its record position, and constructions,
  patterns and projections go through it. (Reussir's own member packing is
  off: its in-place reuse of a cell for another variant mishandles fields
  that packing moves.)
- **Recursion.** Recursive, mutual and nested inductives refer to each
  other's instances; `inductive Rose | node : List Rose → Rose` gives
  `Rose` and `List_Rose`, defined together.

**Function types** become curried Reussir closures: `A → B → C` is
`A -> (B -> C)`. §5.3 explains why they are curried.

**The uniform type `Box`.** When a data position has type `lcAny` (§2.6, §4),
its value is stored as `Box`.
- `Box` is a generated enum with one variant per concrete Reussir type that
  the program ever boxes. Variants are created as Stage 4 needs them, and
  the unboxing functions are regenerated until the set stops growing, so
  the set is known at the end of Stage 4.
- Converting between a precise type `T` and `Box` means wrapping into or
  unwrapping out of `T`'s variant. The variant is fixed by the Lean types
  at both ends, so the unwrap always succeeds; its "other variant" arm is
  unreachable.
- Conversions are inserted wherever a value's Reussir type differs from
  the type expected where it is used: call arguments, return values,
  constructor fields, join-point arguments, closure arguments and results.
  This is the typed counterpart of Lean's own `explicitBoxing`, which
  converts between `obj` and unboxed scalars.
- An inductive applied to `lcAny` is instantiated with `Box`:
  `Free lcAny Nat` ↦ `Free_Box_Nat`.
- A closure passed where `Box -> Box` is expected is wrapped as
  `|b| box(f(unbox(b)))`. The wrapper calls `f` exactly once per
  application, so evaluation timing does not change.
- When a structure built at a uniform type (for example a `List Box` coming
  out of polymorphically recursive code) meets code expecting the precise
  type (`List Nat`), the conversion is structural, element by element.
  Programs observe values, not object identity, so this is transparent.
- Between two different inductives with the same constructor shapes, or
  between `Nat` and an enumeration (only reachable through `unsafeCast`,
  where Lean's representations coincide), values convert constructor by
  constructor, or by index. Where no conversion exists at all, lean2rr
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
| `let h := f a` with `f` of arity 2 | `let h = \|x : B\| f(a, x);` (closure, §5.3) |
| `let y := f a b c` with `f` of arity 2 | `let t = f(a, b); let y = t(c);` |
| `let y := g a b` with `g` a closure variable | `let y = g(a)(b);` |

### 5.3 Closures

After Stage 2, every closure is a partial application of a top-level
declaration; lambda lifting turned local functions into declarations over
their captured variables.

- **Creating a closure.** A partial application of a declaration of arity
  `n`, given `m` arguments, becomes a chain of `n − m` nested
  single-parameter lambdas. Only the innermost one calls the declaration:
  `f a` with arity 3 becomes `|y| |z| f(a, y, z)`.
- **Applying a closure.** A closure is applied one argument at a time:
  `g a b` becomes `g(a)(b)`.
- **Why this is right.** The declaration runs exactly when its last
  argument arrives, which is precisely Lean's runtime rule (`lean_apply_n`
  behaves like applying one argument at a time). Curried closure types are
  the only choice that works for *every* value of a function type:
  different values of the same Lean type can have different arities
  (`mkAdder` versus a function that returns a closure after doing work).
- **Erased parameters.** Lean still passes erased parameters (a proof, the
  IO world, a type) to closures, and they count toward the arity. They
  remain parameters of type `L2RUnit`, in declarations and closures alike,
  and receive `L2RUnit::u{}`. Only extern calls drop them.
- **Constructors.** A partially applied constructor becomes a lambda that
  builds it. Constructors do no work, so timing does not matter.

Cost: a `k`-argument application of an unknown closure allocates `k − 1`
intermediate closures, for example on each step of a fold over an unknown
two-argument function. Native `lean_apply_n` calls the code directly when
the closure misses exactly the arguments supplied, and allocates only when
it misses more. A faster representation is possible later (§7) without
changing when work runs.

### 5.4 `let`, `return`, literals

- `let x := v; k` becomes `let x = ⟦v⟧; ⟦k⟧`, and `return x` becomes `x`.
  Lean's passes have already removed dead `let`s. Lowering never drops a
  Lean `let`, never evaluates one twice on the same path, and never
  reorders them, because a `let` can run a function that panics. It does
  add bindings of its own: representation conversions, placeholders, and
  the bodies of duplicated join points (one copy per path).
- Literals:
  - `Nat` literals below 2^64 become `Nat::Small`; bigger ones are built
    from base-2^32 digits with runtime multiplication and addition.
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

**J1', small join point: duplicate.** A join point whose body is small (at
most 40 bindings, alternatives and exits, nested join points included) and
that is not J2 is inlined at each of its jumps, like J1. Outlining it would
put a function boundary on the path: a loop through it would become a state
machine or mutually recursive, and Reussir could not reuse a cell matched
before the jump for a construction after it. Duplication is recursive:
small join points inside a duplicated body are duplicated again. The
40-node bound covers the whole nest, so growth is bounded, but code size can
still grow by a large factor (up to about 2^10 copies of an innermost
body). Behaviour does not change.

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

**Sinking first.** Before choosing, every join point is moved down to the
smallest part of its scope that contains all its jumps: past `let`s, into
the single `cases` branch that jumps to it, into the continuation or body of
another join point. Free variables stay in scope (binders are unique), and
no code is duplicated. A join point declared before a `cases` of which only
one branch uses it often satisfies J2 once sunk into that branch.

**J4, outlined join points that call back: one state machine.** When a
self-recursive declaration has outlined join points whose bodies call the
declaration (a loop whose body is a DAG of join points, e.g. a chain of
`if`s with shared continuations), J3 would make the loop mutually
recursive. Instead the declaration becomes one function over an enum of
entry points: one variant for the declaration's own parameters and one per
outlined join point (its captured variables and parameters). The function
takes the declaration's parameters followed by the entry point, and matches
on the entry point. The declaration's own variant is nullary, so calling the
declaration (through a wrapper) and its self tail calls allocate nothing; a
jump to an outlined join point passes the parameters on unchanged together
with that join point's variant. All of these are self tail calls, which
LLVM turns into a loop. J4 is used only when an outlined join point makes a
self tail call; other calls back into the declaration are ordinary calls. The enum is a shared (heap) type for now:
Reussir miscompiles `[value]` enums with fields of mixed layout (§9);
Reussir's reuse makes the shared cell cheap.

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

Every extern the program reaches must have an entry in the extern table, and
all missing ones are reported at once. An entry gives the Reussir
implementation:
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
  by an `@[export sym]` Lean definition (`String.Internal.*`, the `IO.Error`
  constructors, `lean_string_intercalate`, …): Lean's runtime calls back
  into compiled Lean code. lean2rr calls that definition directly and
  compiles it like any other, so its semantics are exactly Lean's.
- **Fallible IO** (files and the file system): the runtime primitive
  records its outcome in a last-error slot; `l2r_io_finish` turns it into
  `EST.Out.ok` with the payload (converted: unit, handle, `Metadata`, an
  array of `DirEntry`) or into `EST.Out.error e`, where `e` is built by
  Lean's own exported `lean_mk_io_error_*` builder for the reported kind,
  as Lean's `decode_io_error` does (the builders are instantiated when a
  program uses such an extern). `IO.FS.Handle` is the runtime's `LHandle`.
- **Proofs.** A `Prop`-valued inductive has the unit representation, and a
  parameter of such a type (a proof) is not passed to the runtime.
- **`BaseIO` externs that cannot fail** call the runtime's payload
  primitive `l2r_<symbol without lean_>` when the prelude defines it; its
  result is wrapped as the IO result (`EST.Out.ok` / `ST.Out`).
- **Constructors with an implementation.** Constructors of builtin types
  that Lean implements in its runtime (`Int.ofNat` is `lean_nat_to_int`,
  `Int.negSucc`, `ByteArray.mk`, …) are calls, as in Lean's IR.
- **Element storage.** A polymorphic extern instance knows its type
  arguments. A value whose *declared* type is a type parameter `α` (the
  element of `Array.push`, or a trivial structure over `α` such as
  `[Inhabited α]`, which mono represents by its field) is passed and
  returned in `α`'s array storage type, wrapped or unwrapped if that is an
  `ElemBox`. Other parameters, like an index, are passed as they are.
  Instance keys hold base-phase types, so type arguments go through
  `toMonoType` first.
- **Borrowing.** Lean's borrow annotations (`@&`) are dropped. Reussir's
  owned convention plus its Perceus analysis gives the same results.

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
    if l2r_once_has(28) { l2r_once_get<LStr>(28) } else { l2r_once_set<LStr>(28, l_main___l2r_0____closed__0_init()) }
}
fn l_main___l2r_0_(a505 : L2RUnit) -> T_EST_Out_348 {
    let x506 : LStr = l_main___l2r_0____closed__0();
    let x507 : T_EST_Out_348 = l_IO_println___at___00main_spec__0___l2r_0_(x506, a505);
    x507
}
```

### 5.11 Program entry

A generated Reussir `#[main]` does what Lean's generated `main` does
(`EmitC`: `initialize_Main`, then `lean_io_mark_end_initialization`, then
`lean_run_main`):
1. it runs the startup work of §5.12 on the process's main thread (8 MiB
   stack), with `IO.initializing` answering `true`. An error there prints
   `uncaught exception: <message>` and exits with status 1 before `main`;
2. it clears `IO.initializing`, then starts a thread with a 1 GiB stack, as
   Lean's runtime does for `main` (deep non-tail recursion is common in Lean
   programs);
3. on that thread it calls the translated `main`, passing the argument list
   (without the program name) if `main` takes one, and the world;
4. on `error e`, it prints `uncaught exception: <message>` to stderr and
   exits with status 1;
5. otherwise it exits with the returned `UInt32` (0 for `IO Unit`).

`leanrt::rt::run_main2` implements the two threads and Lean's stack
overflow report.

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
unobservable, and it is cheaper than a once-cell read.

The initializer follows Lean's compilation order, which is not persisted in
the `.olean`. Compilation follows the source, and a declaration generated
while compiling `g` is compiled with `g`, before it.

Our translation runs, before `main`, the startup work of Lean's module
initializers:
- for each program module, for each declaration in source order (line,
  then column). An auxiliary declaration such as `main.unsafe_1`, which has
  no position of its own, goes right before its parent. A specialization
  `f._at_.g.spec_N` goes right before `g`, the declaration after the last
  `_at_`:
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

lean2rr itself never runs the program's initializers: it loads the imported
extension states without Lean's init step, which would execute the
program's `initialize` actions inside the compiler.

The storage is a runtime once-cell per constant (the prelude's
`l2r_once_has`/`get`/`set` over `leanrt::once`), holding a value that is
never freed. A value that is not a pointer-sized boundary type is wrapped in
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

---

## 6. Runtime (`leanrt`)

The runtime provides what Reussir lacks:
- `Nat`/`Int`: a small value, or a GMP bignum (`leanrt::big`);
- Lean's `String` operations over UTF-8 bytes (`Rc<Vec<u8>>`, §5.1);
- `Array`/`ByteArray`/`FloatArray` operations over the copy-on-write `Vec`;
- `Float` math through libm;
- IO: stdout/stderr/stdin streams, `IO.Error`, argv, exit;
- `ST.Ref` cells;
- memoized `Thunk`;
- eager `Task`, since pure tasks give the same values when run immediately;
- panic, trace;
- once-cells for constants.

Concurrency primitives (`IO.asTask`, promises, channels) run on a
single-threaded cooperative scheduler. A task runs until it finishes or
blocks on another task or promise, and then the scheduler switches. Every
interleaving this produces is one that native Lean could also produce. Real
threads, using Reussir's atomic reference counting, come later. Each runtime function consumes the arguments it owns, and never
mutates in place unless it has checked for uniqueness.

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
  boxes array elements);
- unboxed enum-like types;
- per-type drop code;
- exact allocation sizes.

**Room kept open.** Each of these can change later without changing when
work runs or what the program computes:
- a faster closure representation that implements `lean_apply_n` directly;
- `[value]` for small non-recursive structs;
- a cheaper `Nat`;
- borrowed parameters, if Reussir adds them;
- globals for constants;
- re-running Lean's `specialize` after monomorphization.

The lowering keeps Reussir's job easy:
- it prefers J1/J2 over J3;
- it emits structured control flow;
- it adds no closures, reference counting or reuse of its own.

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
  FFI parameters (an array `get` currently takes ownership and releases).

Answered (Lean):
- Startup order: `EmitC.emitInitFn` runs the module's compiled
  declarations in compilation order, skipping closed terms and simple ground
  declarations (§5.12).
- `lean_apply_n` (`apply.cpp`) calls the code directly at exact arity,
  builds a partial application with fewer arguments, and with more calls and
  then applies the rest: one-argument-at-a-time semantics (§5.3).
- Pointer equality in `Init`: `Array.mapMono`, `List.mapMono`,
  `withPtrEq` and `ShareCommon` use it only as a shortcut, so "not equal"
  is safe (lean2rr's `ElemBox`-wrapped values always compare unequal, and
  the shortcut is just lost). `ST.Ref.ptrEq` is real identity, implemented
  by `l2r_ref_ptr_eq`.

---

## 10. Known divergences and unsupported features

Where a translated program can behave differently from its native build.
Each item says what differs and when.

**Evaluation and effects**
- *Dictionary rebuilding* (§2.4): an instance function applied to static
  arguments may run more often than natively. Visible only through traces
  or panics inside instance code, or as extra time.
- *Tasks* run eagerly and synchronously when created. This matches native
  only for tasks that finish without waiting for later actions of their
  creator; a task that waits for its creator never terminates or takes
  another branch. Promises are read after every resolution that can come
  before the read.
- *Stack depth* in general: frame sizes differ from native, and lean2rr
  adds recursion of its own (structural conversions, the `Array.mk` and
  `String.mk` list folds). The depth at which `Stack overflow detected.
  Aborting.` (exit 134) happens is not native's, in either direction.
- *Stream redirection*: `IO.setStdout`, `setStderr` and `setStdin` (and so
  `IO.FS.withIsolatedStreams`) are not translated yet. Panic messages and
  `dbgTrace` go to descriptor 2, where native uses the current stderr
  stream.

**Cost** (time and memory, not results)
- *Structural conversions* (§5.1) rebuild a value as a tree: sharing is lost,
  so a DAG costs exponential time and memory, and a conversion on every call
  costs O(size) per call. Past the instance caps of §2.6 this can happen
  inside loops. Running out of memory changes the exit status.
- *Closure wrappers* pile up: every crossing into or out of `Box` wraps a
  closure again, so a function value that passes through uniform code `n`
  times costs O(n) per application.
- *Element storage*: array elements, `ST.Ref` contents, once-cell values and
  polymorphic extern arguments whose type cannot cross the FFI boundary
  (enumerations, `L2RUnit`, `[value]` tuples, closures) are wrapped in an
  `ElemBox` cell, one allocation each, where native stores tagged scalars.
  `ST.Ref` contents are always boxed (§5.1). `UInt64` and `Float` arrays, on
  the other hand, are unboxed, unlike native.
- *Unknown closures*: `k − 1` intermediate closures per `k`-argument
  application (§5.3).

**Runtime** (details in `runtime/README.md`, "Known divergences")
- Sharing is not observable: `isExclusiveUnsafe` answers `false`.
- `IO.getNumHeartbeats` is 0; `dbgStackTrace` prints nothing; a panic's
  backtrace line is `(stack trace unavailable)`.
- Huge capacity reservations are capped.
- `errno` after a sticky handle error can differ.

**Diagnostics**
- lean2rr's own impossibilities (a `Box` unwrap of another variant, a cast
  with no conversion) print Lean's `INTERNAL PANIC: unreachable code has
  been reached` and exit 1, like a real unreachable.

**Not supported** (translation succeeds; `rrc` reports an unknown function)
- `IO.Process.spawn` and other processes, sockets, `Std.Sync`, timers.
- Every constant of the program is translated (§2.2), so an unused constant
  that reaches an unsupported extern makes the whole program fail to link.
  A program is therefore translated by lean2rr, but links only if the
  runtime implements every extern it reaches.
