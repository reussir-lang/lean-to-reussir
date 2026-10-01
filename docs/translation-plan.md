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
  the same representation, the `map` loop runs on the precise array. When
  they differ, the array is converted once on entry and once on exit, never
  inside a loop.
- A `box(0)` placeholder is a value that is never inspected. It arrives as
  a unit-like value used at another type, or as `◾` at a relevant type.
  Stage 4 materializes it as the *zero* of the expected type: `0`, `false`,
  the first constructor whose fields have zeros, a closure returning a zero,
  an empty array. For `Nat`, `Bool` and enumerations this is exactly what
  `box(0)` denotes in Lean. Only a type without a finite value gets
  `unreachable`. A zero that would allocate (a string, an array, a record,
  a closure) is built once and kept in a once-cell, like a constant
  (§5.12): `modify` stores one per update, and since a placeholder is never
  inspected, a shared value serves as well as a fresh one.

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
  instantiated at the discriminant's type. A constructor application gets
  the type its argument types determine. Parameters that no field
  determines, such as the error type of `EST.Out.ok`, come from the binder's
  own type. A call, full or partial, gets the type the callee's signature
  gives. A join-point parameter gets the type of its jump arguments when all
  of them are known and agree.
- **Result types.** A declaration whose result type is unknown gets `T` when
  all its returned values have type `T`. The results of its own self calls
  do not count, and neither do constructors without fields (`none`) of `T`'s
  inductive. It also gets `T` when every call of it binds the result at `T`,
  provided it is used nowhere else, e.g. not as a closure. The callers would
  convert right away anyway; the conversion moves to the callee's `return`,
  which for a constant happens once instead of at every read.
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

For `xs.map (· * 2)` these rules make the whole map run on the precise array,
in place and without boxing, like native Lean. The loop is assumed to
receive `Array Nat`. Its reads become `Array.uget@Nat`, its placeholder is a
`Nat` zero, and its writes of `Nat` values become `Array.uset@Nat`, so it
passes `Array Nat` back. When `f` changes the representation (`Nat →
String`), the loop keeps the `Box` array, its input is converted once on
entry, and the loop's result type, `Array String` by the `map` rule, makes
it convert once on exit. The loops that read the result then receive
`Array String` from their callers.

Each rule is exact. A value's type is taken only from its definition or from
everything that flows into it, so the recovered type is the type the value
has on every path. Where the program does not determine the type, the
binder keeps `lcAny` and uses `Box`, with conversions where it meets a
precise type.

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
| `String` | `LStr`, an opaque copy-on-write handle over UTF-8 bytes and their character count (`Rc<(Vec<u8>, u64)>`) | literals: §5.4 |
| `Array α` | `RVec<S>`, the runtime's copy-on-write vector | in place when unique. `S` is the storage type of `α`: `⟦α⟧` itself if it can cross Reussir's FFI boundary (scalars, `bool`, runtime handles, shared records), otherwise a generated one-field shared struct `ElemBox` around it (Lean boxes array elements too) |
| `Array Nat`, `Array Int` | `LNatArr`, `LIntArr` | one word per element like Lean's boxed scalars: small values inline, big ones as bignum handles; the array functions are the `natarr`/`intarr` counterparts of the generic ones, with the same arguments |
| `ByteArray`, `FloatArray` | `RVec<u8>`, `RVec<f64>` | |
| `ST.Ref σ α` | `LRef<Box>`, a shared mutable cell | mono types a reference as `lcAny`, so it travels boxed. Its contents are boxed too, whatever `α` is: uniform code (`α = lcAny`) and typed code can share one cell, and a cell cannot be converted without losing aliasing. Each `set` allocates the box. |
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
  contains itself by value).
- **Field order.** lean2rr orders each constructor's fields by decreasing
  alignment (ties in declaration order), so records have no padding; the
  layout maps each Lean field to its record position, and constructions,
  patterns and projections go through it. (Reussir's own member packing is
  off: its in-place reuse of a cell for another variant mishandles fields
  that packing moves.)
- **Recursion.** Recursive, mutual and nested inductives refer to each
  other's instances; `inductive Rose | node : List Rose → Rose` gives
  `Rose` and `List_Rose`, defined together. Whether a type is a shared
  record (so that arrays store it as it is, not in an `ElemBox`) is decided
  from its constructor shapes before its fields are translated, so
  `inductive Tree | node (v : Nat) (cs : Array Tree)` holds `RVec<Tree>`,
  the representation `Array Tree` has everywhere else (also through mutual
  types, whichever is translated first).

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
  It also accepts the variants of types that an `unsafeCast` can read this
  way (below): another inductive with the same layout (the value as it
  is), words as words, `UInt64`/`Float` by their bits; an existential
  payload, an `IO.Ref`'s contents or a value in polymorphically recursive
  code cast to such a type converts like a typed value. Other casts convert
  only in typed code, where they are written: through a `Box`, every
  unboxing function would have to match and convert every type its
  constructors can read (every structure with one function field, the
  dictionaries of uniform code, reads every other one).
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
- A partial application has the type of its target with the supplied
  arguments removed. Lambda lifting can give a lifted lambda the result type
  `lcAny` while its closure is used at `Nat × Int → Int`, or the reverse; the
  value is then converted to the binder's type as above, and the callee
  still runs only when the last argument arrives.
- When a structure built at a uniform type (for example a `List Box` coming
  out of polymorphically recursive code) meets code expecting the precise
  type (`List Nat`), the conversion is structural, element by element.
  Programs observe values, not object identity, so this is transparent.
  An array whose elements cannot be converted (`Array Nat` to `Array Int`)
  must be empty when that happens: an empty array that `cse` shared between
  two element types, or the result of mapping nothing. Its element step is
  therefore `unreachable`.
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
    reinterpreted: a `UInt64` field read as `Float` is its bits.
  - *Words*: `Nat`, `Int`, `UInt8/16/32`, `Char`, `Bool`, enumerations and
    constructors without fields are boxed scalars natively, and convert as
    Lean's `lean_unbox` reads them: truncated to the target's width
    (`unsafeCast (300 : Nat) : UInt8` is 44, `Bool` is the low byte being
    nonzero), an index past an enumeration's last constructor selects the
    last one (Lean's `switch`), a small `Int` is its 32 bits (read as a
    `Nat`, `-5` is `2^32 - 5`), a word read as an `Int` is signed 32 bits.
    `Nat` and `Int` convert by value (natively the same object when big). An
    index selects the nullary constructor at that position (`0` is `[]` or
    `none`), and back; a constructor with fields read as a word is natively
    an address: unreachable.
  - A `[value]` struct is natively its field.
  When the two Reussir types have the same layout (the same constructors
  with fields of the same layouts, position by position, coinductively;
  arrays of such elements) and the conversion would pair exactly those
  fields, the value is used as it is (`l2r_retype`, the same object
  reinterpreted): a user list read as another user list, or an `Array T₁`
  field read at `Array T₂`, costs nothing and keeps its identity. This
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
sharing. Code that stops when `ptrEq` says a step changed nothing (Lean's
`Expr.replace`, fixpoint loops) depends on it, and a lookup returning an
existing node must not copy it.

Two shapes help Reussir's token reuse, which gives a cell freed by a match
to a later construction:
- In the arm of a constructor without fields, the matched value is that
  constructor (`leaf{}`), which costs nothing to build.
- In an arm where the matched value stays live because it is stored whole
  in a new constructor or returned whole (`simp` turns `t@(node l k r)`
  rebuilt into `t`: a BST insert of a key already present), the match binds
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
  an association list, kept whole when its key does not match). The rule
  is limited to values stored in constructors or returned. For a value
  only passed to calls (merge's `go l₁ ys (y :: acc)`), reusing its cell
  measured slower on the classic `mergesort`: the result keeps the
  scattered memory order of the input cells.

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
- **Borrowing.** Lean's borrow annotations (`@&`) are dropped. Reussir's
  owned convention plus its Perceus analysis gives the same results, except
  for when a value is freed: natively a parameter that Lean's IR infers as
  borrowed is released by the caller after the call returns, while here the
  callee releases it at its last use, possibly earlier. Only resources can
  tell: a file handle is closed (and so flushed) earlier, a child sees end
  of file on a pipe earlier (§10). The process glue keeps a `Child` alive
  across `wait`, `tryWait` and `kill`, which borrow it by annotation.

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
(`EmitC`: `initialize_Main`, then `lean_io_mark_end_initialization` and
`lean_init_task_manager`, then `lean_run_main`, then
`lean_finalize_task_manager`):
1. it runs the startup work of §5.12 on the process's main thread (8 MiB
   stack), with `IO.initializing` answering `true`. An error there prints
   `uncaught exception: <message>` and exits with status 1 before `main`;
2. it clears `IO.initializing` and starts the task manager: IO tasks are
   deferred from now on (§5.14). It then starts a thread with a 1 GiB
   stack, as Lean's runtime does for `main` (deep non-tail recursion is
   common in Lean programs); `main` starts there with the process's
   standard streams, as a new thread does natively, whatever the
   initializers redirected;
3. on that thread it calls the translated `main`, passing the argument list
   (without the program name) if `main` takes one, and the world;
4. it runs the IO tasks still pending, whatever `main` returned, as
   `lean_finalize_task_manager` does before the result is looked at;
5. on `error e`, it prints `uncaught exception: <message>` to stderr and
   exits with status 1;
6. otherwise it exits with the returned `UInt32` (0 for `IO Unit`).

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

A float literal arrives as a call of a Lean function on literal arguments,
`Float.ofScientific 15 true 301` for `1.5e-300` (or `Float.ofNat n`,
`Float32.…`), which is not cheap: the slow path (a mantissa of `2^53` or
more, an exponent above 22) goes through `Float.Model` with bignum
arithmetic. lean2rr evaluates such calls itself, with the same Lean
functions (lean2rr is compiled from the same `Init` code, so the bits are
Lean's, subnormals and rounding included), and replaces them by
`Float.ofBits` of the bit pattern, a cheap constant as above. Calls with
an exponent above 2000 or a mantissa of more than 4096 bits are left to run
(cached as usual when they are a constant).

The initializer follows Lean's compilation order, which is not persisted in
the `.olean`. Compilation follows the source, command by command. A `def`
or `instance` command is compiled after it is elaborated, together with its
`where`/`let rec` helpers: the elaborator lists the helpers (those of later
`mutual` members first, outer ones before nested ones, otherwise in source
order), then the command's own declarations, and compiles the strongly
connected components of their reference graph one at a time, callees first
(Tarjan's order over that list). A declaration generated while compiling a
component, such as a specialization `f._at_.g.spec_N` made while compiling
`g`, comes right before the component's members; an auxiliary declaration
made during elaboration (`c.unsafe_1`, `instInhabitedP.default`) comes
before the whole command. For example

    def p : Nat := t "p" (h1 + h2)
    where
      h1 : Nat := t "p.h1" 1
      h2 : Nat := t "p.h2" (h3 + 1)
      h3 : Nat := t "p.h3" 3

initializes `p.h1`, `p.h3`, `p.h2`, then the specializations made in `p`,
then `p`. lean2rr rebuilds this order from declaration ranges (a helper's
range lies inside its parent's; the kernel's `all` lists a recursive mutual
block) and from the references in the declarations' kernel values (for a
`partial` definition, its `_unsafe_rec`). The function of an `initialize`
declaration belongs to its constant: a specialization made inside the
action comes right before the action.

Positions are compared as (line, column). Lean's own record of the order
(`declOrderExt`, which `EmitC` follows) is not persisted, and neither the
module's constant list nor the compiler's declaration tables keep the order
of addition, so declarations with the same range need more. Every
declaration of one macro expansion has the macro call's range, and the
instances of one `deriving instance … for A, B` command share one range
too. A range equal to another one is therefore not "inside" it: `mk foo
foo.bar` makes two commands, not `foo` and its helper. Such commands are
ordered by the position of their names (a macro that takes the names from
its arguments keeps their positions; a hygienic name made by the macro has
the call's position, so it comes first), then by the order in which the
module added its instances (the instance extension keeps it), and last by
name, with the numbers in names compared by value: the auxiliary constants
`c._unsafe_1`, `c._unsafe_4`, …, `c._unsafe_10` of a declaration with
several `unsafe` parts start in that order.

Our translation runs, before `main`, the startup work of Lean's module
initializers:
- for each program module, for each declaration in that order:
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

The startup steps are emitted as functions of at most 128 steps each,
called in order (with a further level of grouping when there are more than
128 of those): one chain of nested matches, one per initializer, would be
as deep as the program has initializers, and rrc's recursive lowering
overflows its stack on a few thousand. An error in a step exits from inside
it, so later steps do not run.

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

### 5.14 Thunks and tasks

Both are a runtime cell `LCell<S>`: one allocation holding a count and one
value, updated in place and seen through every alias. The value is a
generated state, one type per value type `α` (and per kind, thunk or task):

```
enum L2RThunk_N { pending(L2RUnit -> ⟦α⟧), busy, done(⟦α⟧),
                  conv(L2RUnit -> ⟦α⟧, Box, u64), busyconv(u64),
                  convdone(⟦α⟧, Box, u64) }
enum L2RTask_N  { …the same…, bind(L2RUnit -> LCell<L2RTask_N>) }
```

The state is a shared Reussir enum, so every `α` fits, closures and value
types included; a closure cannot be stored in a runtime cell directly.
`conv` is a converted thunk or task (`busyconv` while it is forced,
`convdone` once it has its value) and `bind` a bind task that has not
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
task runs when it is needed, on the stack of whoever needs it.

- *IO tasks* (`BaseIO.asTask`, `mapTask`, `bindTask`) are deferred. The new
  cell is `pending(|w| act(w).val)` (for `mapTask f t`, the action is `f
  t.get`); for `bindTask t f` it is `bind(|w| (f t.get w).val)`, whose
  computation yields the task the new one continues as. The runtime
  (`leanrt::task`) queues it and holds a reference until it runs, since
  Lean runs an IO task even if the program drops it. A task that depends
  on a task unfinished at its creation (`mapTask`, `bindTask`, and the pure
  `Task.map`, `Task.bind`) is recorded as its dependent, as Lean's
  `add_dep` does.
- *Pure tasks* (`Task.spawn`, `Task.map`, `Task.bind`) are computed when
  they are created if no task is pending or running: `Task.spawn f` is then
  `l2r_lcell_new(S::done{f(())})`, and nothing, not even `dbgTrace`,
  shows the difference from a worker computing it. Otherwise they are
  deferred and queued like IO tasks: their code may need a pending task,
  which may be waiting for `main` (`Task.spawn fun _ => t.get + 1` with `t`
  waiting for a flag `main` sets later finishes natively). `Task.pure a` is
  `done(a)`.
- A pending task runs at the first of:
  - `IO.wait`/`Task.get` of it, or a task that needs it running;
  - `IO.waitAny` on a list none of whose tasks has finished: the first
    pending task of the list runs (it is the one that finished first);
  - a program polling for it: `IO.getTaskState`/`IO.hasFinished` report a
    pending task `waiting`, until the program asks again after time has
    passed (an `IO.sleep`/`dbgSleep` since the first answer) or keeps asking
    (1000 times); the task then runs and is reported `finished`;
  - `main` returning (§5.11): the queued tasks run in the order Lean's task
    manager with one worker (`LEAN_NUM_THREADS=1`) starts them. The task
    manager keeps a queue per priority (0 to 8; a dedicated task, above 8,
    has a thread of its own, so it comes first here) and takes the first
    task of the highest non-empty one. An idle worker starts the first
    task queued at once, and when a task finishes it starts the next one
    right away: that started task runs first, whatever is queued after it.
    `IO.Process.exit` exits at once, as natively.
- *Dependents.* A task that waits for a task unfinished at its creation
  (`mapTask`, `bindTask`, `Task.map`, `Task.bind`) is off the queue until
  that task finishes. Then, whoever finished it (during `main` too), Lean
  walks its dependents from the newest (`handle_finished`): one created
  with `sync := true` runs there and then, on the finishing thread, before
  anything waiting for the finished task resumes; the others are enqueued
  at their priority. A bind task that has run `f` finishes at once if the
  task `f` returned has finished, and otherwise waits for it, keeping its
  priority and `sync` flag, and finishes as that one (`task_bind_fn1`).
  Dependents of a cycle are left behind, as Lean's workers stop when the
  queue is empty. A task needed while the tasks it waits for are pending
  first runs that chain from its deepest end, one task after the other,
  so a long chain does not recurse.
- `mapTask`/`bindTask`/`Task.map`/`Task.bind` with `sync := true` of a
  finished task apply `f` at once in the calling thread (its streams too),
  as `lean_task_map_core`/`lean_task_bind_core` do.
- `IO.cancel` sets the flag of a pending or running task; when a canceled
  task finishes, the tasks created while it was unfinished that depend on
  it (`mapTask`, `bindTask`) are canceled too, as Lean's `handle_finished`
  does. `IO.checkCanceled` answers for the innermost running task, and is
  false in `main`. During the final run of queued tasks, Lean has set its
  shutdown flag, which makes `IO.checkCanceled` true; natively those tasks
  have usually started long before, so a task sees the flag only once time
  has passed in it (a sleep) or from its second check on.
- A thunk or task stored at another representation (in `Box`, §5.1) is
  converted to a new cell in state `conv(g, o, a)`: `g` forces the original
  and converts its value (so it still runs at most once); `o` is the
  original cell, boxed, so that converting back gives that very cell (a
  thunk crossing between typed and uniform code in a loop stays one cell
  instead of growing a chain); `a` is the original's address: the copy's
  identity (`ptrAddrUnsafe`, §9) and, for a task, its identity for the
  runtime, so the copy's state, `IO.cancel` and cancellation are the
  original's, also while the copy is being forced (`busyconv`). A forced
  copy, and the copy of a thunk or task that already has its value, is
  `convdone(v, o, a)`: it keeps the original, so that its identity stays
  the original's (which stays alive, so its address is not reused). A copy
  of a copy records the first original, and converting it to a third
  representation converts the original directly, so chains stay one level
  deep.
- *Standard streams.* Natively each thread has its own current standard
  streams (`IO.setStdout` & co. replace the current thread's, which start as
  the process's), and a task runs on a worker thread. So a task starts with
  the process's streams, and when it ends the streams of whoever ran it are
  back (`l2r_std_enter`/`l2r_std_leave` set the stream cells aside and
  restore them); a pure task computed at once does the same. During module
  initialization, where Lean runs tasks on the calling thread, they share
  the caller's streams. `main`, on its own thread, starts with the
  process's streams whatever the initializers installed (§5.11). Natively
  a worker keeps its streams from one task to the next, so a task that
  leaves a redirection behind can affect the next task on the same worker;
  the translation behaves as if every task ran on a fresh worker.
- During module initialization Lean has no task manager, and
  `lean_task_spawn_core` runs the action at once; so does the translation.

Why tasks are deferred rather than run at creation: a task may wait for
`main`. `IO.asTask (do while !(← flag.get) do IO.sleep 1; …)` followed by
`flag.set true; IO.wait t` finishes natively; run at creation, the task
would spin forever. Running at creation also prints the task's output
before `main`'s next line, which natively comes first when the task starts
with a sleep. A task that runs only when needed never waits for something
that is still to happen.

What a single thread cannot do:
- a task that waits for another by other means than the task operations
  above (`main` or a task polling an `IO.Ref` that another task sets) does
  not terminate;
- output ordered by sleeps across tasks comes in the order tasks are
  needed, not by time, and `IO.waitAny` does not pick the fastest of
  several unfinished tasks;
- tasks nobody waits for stay queued, with what they hold, until `main`
  returns (a chain of 4·10⁶ `mapTask`s built by `main` takes 1.6 GB, where
  native workers run it as it is built);
- a task needed by `main` runs at once, where a single native worker would
  first finish the tasks queued before it;
- Lean's panic for `Task.get` inside a `sync := true` task is not
  reproduced;
- a deferred task is reported `waiting` at the first question even after a
  sleep, where natively a worker would long have run it (a pure task
  deferred behind a pending IO task, for example): running it then could
  hang, if it needs a task that waits for `main`.

Tasks that wait for each other in a cycle wait forever, as natively.
Promises are not translated yet.

---

## 6. Runtime (`leanrt`)

The runtime provides what Reussir lacks:
- `Nat`/`Int`: a small value, or a GMP bignum (`leanrt::big`);
- Lean's `String` operations over UTF-8 bytes (`Rc<(Vec<u8>, u64)>` with the character count, §5.1);
- `Array`/`ByteArray`/`FloatArray` operations over the copy-on-write `Vec`;
- `Float` math through libm;
- IO: stdout/stderr/stdin streams, `IO.Error`, argv, exit;
- `ST.Ref` cells;
- the mutable cells of thunks and tasks, and the queue of deferred IO
  tasks (§5.14);
- panic, trace;
- once-cells for constants.

Everything runs on one thread: IO tasks are deferred until needed
(§5.14), which gives one of the schedules native Lean can produce. Real
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
  boxes array elements);
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
  is safe there. Other code stops when `ptrEq` says a step returned its
  argument itself (`Expr.replace`, fixpoint loops, over any type), so
  `ptrAddrUnsafe` answers what native Lean answers (`addrOf`):
  - a boxed scalar's word, `lean_box(n) = 2n+1`, for what Lean represents
    so: a `Nat` below 2^63, an `Int` in the `int32` range (`2·u32(i)+1`),
    `UInt8/16/32`, `Char`, `Bool` and enumerations (their index), a
    nullary constructor of any inductive (its index: `[]` and `none` are
    1), `Unit` and erased values (`box(0) = 1`);
  - a heap value's handle pointer (`l2r_ptr_addr_obj`, `l2r_ptr_addr_rec`),
    big numbers included;
  - a `[value]` struct, represented natively by its field: the field's;
  - `UInt64`, `Float`, `Float32`, `USize`: natively boxed into a new cell at
    each call (two calls on the same variable give different cells, unless
    Lean's CSE merged them, which lean2rr keeps): a fresh number;
  - uniform code holds lean2rr's own wrappers, which answer what they hold:
    a `Box` its payload's identity (for a `UInt64`/`Float` payload, the `Box`
    cell, which is the cell native boxing made), a function value wrapped for
    another representation (`w`) the wrapped value's, a thunk or task
    converted to another representation (`conv`, `convdone`, §5.14) the
    original's address, which it records.
  So `ptrEq x x` holds for every representation, a payload returned by its
  own function is `ptrEq` to itself, and fixpoint loops stop where native
  ones do. Values without a native object (a `Nat` from 2^63 to 2^64, an
  `Int` outside `int32` but inside `i64`: natively big number objects) answer
  a number computed from the value, so equal ones are `ptrEq`; an array
  converted to another element representation (§5.1) is a new array (§10).
  `ST.Ref.ptrEq` is real identity, implemented by `l2r_ref_ptr_eq`.

---

## 10. Known divergences and unsupported features

Where a translated program can behave differently from its native build.
Each item says what differs and when.

**Evaluation and effects**
- *Dictionary rebuilding* (§2.4): an instance function applied to static
  arguments may run more often than natively. Visible only through traces
  or panics inside instance code, or as extra time.
- *Tasks* run on one thread, when they are needed or when `main` returns
  (§5.14): a task or `main` polling shared state that another task sets
  never sees it change, output ordered by sleeps across tasks comes in the
  order tasks are needed, and `IO.waitAny` does not pick the fastest task.
  A pure task created while no other task is pending is computed at once,
  so one that never finishes hangs the program, where native Lean runs it
  on a worker thread and can exit without it. A deferred task is reported
  `waiting` at the first `IO.hasFinished`, even after a sleep. Tasks run as
  if each had a fresh worker thread, so a redirection a task leaves behind
  never reaches another task (natively it can, on the same worker);
  `IO.getTID` inside a task is main's thread id plus the depth of running
  tasks, as distinct from main's as a worker's. Promises are not
  translated yet.
- *Startup order of generated constants*: specializations with every
  parameter fixed that Lean generated while compiling the same declaration
  run in the order of their numbers (`spec_0`, `spec_2`, …). Lean's own
  order among them depends on how its specializer recursed, which the
  `.olean` does not record, and can differ. Visible only when such
  constants trace or panic.
- *Startup order of a macro's made-up names* (§5.12): declarations of one
  macro expansion that the macro names itself (hygienic names, which all
  have the macro call's position) and that are not instances start in name
  order; natively in the order the macro wrote them. Declarations named by
  the macro's arguments start in the order of those arguments.
- *Startup order in `mutual` blocks and several `let rec` groups* (§5.12):
  the members of a `mutual` block that do not call each other are ordered
  as separate commands, because the block is not recorded in the `.olean`
  (natively the helpers of all its members run first, those of later
  members first). Within one declaration, a `let rec` in the body and a
  `where` clause are ordered by source position (natively the `where`
  helpers come first). Visible only when such helper constants trace or
  panic.
- *Compiler options of the program's modules* (`set_option
  compiler.extract_closed false`, `compiler.small`, `maxRecInline`, …) are
  not recorded in the `.olean`, so lean2rr runs Lean's passes with the
  defaults: a declaration compiled without closed-term extraction natively
  can have its closed terms extracted (and evaluated once) under lean2rr.
  The recursion limit (`maxRecDepth`, which large literals need raised)
  is effectively unlimited in lean2rr, bounded by its stack (4 GiB, set by
  `scripts/l2r.py` through `LEAN_STACK_SIZE_KB`): a 60000-element list
  literal needs more than 64 MiB.
- *Merging after erasure*: natively, two uses of a type-polymorphic
  constant at different type arguments (`(emptyList : List Nat)`,
  `(emptyList : List String)`) are the same call after erasure, and Lean's
  CSE merges them; lean2rr's instances are different calls. Visible only
  when such a value traces or panics.
- *Build time*: rrc compiles about 80 small functions per second; a program
  with thousands of constants (each an initializer and an accessor, plus its
  closed terms) takes minutes to build where native takes seconds.
  Polymorphic recursion through type functions (monad transformer towers)
  makes deeply nested function representations (`L2RFn_*` enums, `Box`),
  and two rrc costs grow superlinearly on them: closure devirtualization
  (part of `-O aggressive`) prints each closure's result type, every named
  type expanded, at every vtable and indirect call site, and the
  module-level SCCP pass iterates over the large call graph of the uniform
  code. The driver turns closure devirtualization off (`--no-closure-wpd`:
  no classic benchmark changes by more than 1%, since lean2rr dispatches
  function values itself). Such programs still take a minute or more to
  build, and the largest towers (four transformers) up to a quarter of an
  hour and several GB.
  rrc's costs also grow faster than linearly in the depth of nested matches
  (reuse across calls; every IO bind nests one) and in the length of
  straight-line code on `Nat` (Reussir bugs 16 and 17). So after lowering,
  a function with a tail path 32 matches or `if`s deep, or 256 `let`s long
  (a long `main`, a 3000-arm literal match, a long `do` block), is cut into
  a chain of functions of at most 8 levels and 64 `let`s on a path, each
  part a function of the variables it uses, called in tail position
  (`Outline`). Ordinary functions are below both bounds; the classic
  corpus only has some `main`s cut. Recursive functions are not cut: LLVM
  turns a self tail call into a loop, but a cycle of tail calls through
  the parts is not always a sibling call and would use stack on every
  iteration, so a loop with such a body still builds slowly. A 2000-line
  `main` builds in about three minutes and 2 GB.
- *Open descriptors*: native Lean starts with libuv's descriptors open (8
  more), so `/proc/self/fd` listings and the point where opening files
  fails with `EMFILE` differ.
- *Casts that natively read an address* (§5.1): `unsafeCast` of a big
  `Nat` or `Int` to a fixed-width scalar or an enumeration natively reads
  the bits of its object's address; lean2rr uses the low bits of its value.
  A constructor with fields read as a word, or a word read as a constructor
  with fields, is natively an address read as a number or a number used as
  an address; it panics here. A `Nat` from 2^31 to 2^63 cast to `Int` is
  natively not a valid small `Int` (results then depend on the operation);
  lean2rr keeps its value. A `Box` holding a constructor without fields,
  read as a word (or the reverse), or a value of an inductive whose
  lean2rr layout differs from the one it is read as, panics (§5.1).
- *Pointer identity* (§9): a structural conversion (§5.1) builds new
  objects, so a value converted to another representation is not `ptrEq`
  to the original; in particular an array converted to another element
  representation (an `Array Nat` stored in a field of uniform type `Array α`)
  is a new array each time. A `Nat` from 2^63 to 2^64 and an `Int` outside
  `int32` (natively a new big number object per computation) answer a
  number computed from their value, so equal values are `ptrEq` (natively
  only the same object is); likewise a rebuilt `[value]` struct over the
  same field. A thunk or task converted to another representation keeps its
  original alive (§5.14), so that its identity stays unique.
- *Release time of borrowed parameters* (§5.8): a resource passed to a
  function that Lean infers to borrow it is released by Lean's caller
  after the call; here it is released at its last use inside the callee.
  A handle written and then dropped by a helper that goes on to read the
  same file, or a pipe to a child that the helper then waits for, is
  closed earlier than natively (the file is already flushed; the child
  sees end of file, where natively it may wait forever).
- *Order of panics in pure code*: when several pure computations panic
  (`get!` on a short array, an `assert!`), their messages can come out in
  another order than natively, because Lean's closed-term extraction may
  group them differently in lean2rr's instances. stdout and results are the
  same.
- *Stack depth* in general: frame sizes differ from native, and lean2rr
  adds recursion of its own (structural conversions, the `Array.mk` and
  `String.mk` list folds). The depth at which `Stack overflow detected.
  Aborting.` (exit 134) happens is not native's, in either direction.
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
  costs O(size) per call. Past the instance caps of §2.6 this can happen
  inside loops. Running out of memory changes the exit status. Values of
  types with the same layout are not converted (`l2r_retype`); a cast
  between layouts that differ (an `Array T₁` field read at `Array T₃` whose
  elements hold an `Int` where `T₁`'s hold a `Nat`) converts the field at
  each use, where natively the cast is free.
- *`Array.map` that changes the representation* (for example
  `(Array.range n).map some`) converts the input to an array of `Box` on
  entry and back on exit (§2.7), so the input, the boxed copy with one box
  per element, and the result are live together: peak memory 1.5–2.7x
  native in tests. Maps that keep the representation run in place.
- *Element storage*: array elements, `ST.Ref` contents, once-cell values and
  polymorphic extern arguments whose type cannot cross the FFI boundary
  (enumerations, `L2RUnit`, `[value]` tuples) are wrapped in an
  `ElemBox` cell, one allocation each, where native stores tagged scalars.
  `ST.Ref` contents are always boxed (§5.1). `UInt64` and `Float` arrays, on
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
- *`Array Nat`/`Array Int` objects* have a 40-byte header (a Lean array's is 24): six
  million three-element `Array Nat` rows take 1.3x native memory
  (Pf4SmallArrs 0).
- *Strings* are two allocations, the counted box (with the character
  count, 40 bytes) and the byte buffer, where a Lean string is one object:
  five million short live strings take 306 MB (native 352 MB; 270 MB
  before the count was cached; Pf4ManyStrs).
- *Dropping a large array of records* releases each element through
  Reussir's out-of-line `<record>_ffi_release` (natively an inline
  decrement in `lean_del`'s loop): freeing 6,000 hash-map versions (300
  million bucket references) at the end of Pf4HashPersist takes about half
  of its 0.8 s CPU time (native 0.4 s).
- *Constants read in a loop* (a top-level `Array` or `String` table)
  check their once-cell on every read: Pf4BigLit 1.16x native.

**Runtime** (details in `runtime/README.md`, "Known divergences")
- Sharing is not observable: `isExclusiveUnsafe` answers `false`.
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
  read error after `wait`). Native Lean has
  about 8 more descriptors open (libuv's), so descriptor numbers inherited
  by children and `EMFILE` thresholds differ.

**Diagnostics**
- lean2rr's own impossibilities (a `Box` unwrap of another variant, a cast
  with no conversion) print Lean's `INTERNAL PANIC: unreachable code has
  been reached` and exit 1, like a real unreachable.

**Not supported** (translation succeeds; `rrc` reports an unknown function)
- Sockets, `Std.Sync`, timers.
- Every constant of the program is translated (§2.2), so an unused constant
  that reaches an unsupported extern makes the whole program fail to link.
  A program is therefore translated by lean2rr, but links only if the
  runtime implements every extern it reaches.
