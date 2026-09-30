# lean2rr translation plan

How a Lean 4.33 program becomes a Reussir program: what each stage receives,
what it does, and what it hands on. The goal is that every rule here is
*right*: the translated program behaves like the Lean program. Each rule
states what it does and why it is correct in plain terms. Reviewers check
the rules against Lean's actual behaviour (its compiler sources, `lean.h`,
and native executables), and tests compare our executables with native
ones.

Items marked **(probe)** depend on a Reussir capability that is still being
confirmed (see §9). Items marked **(verify)** are Lean facts still to
be confirmed by a small experiment.

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
confirmed on a hand-monomorphized probe. We reuse all of Lean's LCNF-level
work and re-implement none of it.

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

The roots are `main`, plus the user CAFs that must run at startup (§5.12).
Everything referenced from reachable code is collected:
- declarations with code;
- `@[extern]` declarations (provided by the runtime);
- constructors.

Nothing else can occur in a program Lean compiled: Lean refuses to compile
code that uses noncomputable constants. So anything else would indicate a bug
in lean2rr, not in the program.

### 2.3 Instances

A polymorphic declaration becomes one monomorphic copy, an *instance*, per
distinct list of type arguments it is used with. `main` has none. It calls
`Tree.insert` at `α := Nat`, so the instance `Tree.insert@Nat` is created;
that instance's calls create further instances, and so on. Each instance
gets a **fresh name** that no Lean module uses. This matters in Stage 2: the
fresh names guarantee Lean's passes only ever see our monomorphic copies,
never Lean's saved polymorphic versions.

How an instance is built: substitute each type parameter by its type argument
everywhere, drop those parameters, and re-simplify the types. This is exactly
what Lean's own specializer does (`Specialize.mkSpecDecl`). Lean represents a
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

A dictionary with polymorphic methods is sometimes *not* statically known:
it is stored in a data structure, or passed through code that neither Lean
nor we specialized. Its polymorphic methods are then instantiated at `lcAny`
and work on boxed values (§5.1), just as in Lean's uniform representation.
Statically known dictionaries, the common case, take the fast path above.
The M0 stats measure how often the slow path occurs.

### 2.5 Local polymorphic functions and externs

- A local `fun` that still takes type parameters is copied once per type
  it is applied at.
- An extern with type parameters (`Array.push {α}`) gets a typed instance,
  e.g. `Array.push@Nat : Array Nat → Nat → Array Nat`, which is still an
  extern. Monomorphic externs keep their original names, so Lean's
  constant folding still recognizes them.

### 2.6 When a type is not statically known

Every program Lean compiles is translated. Where a static type is
unavailable, the uniform `Box` representation (§5.1) takes its place:
- **A type argument that is not fully known.** The instance is built at
  `lcAny` (§2.3).
- **Polymorphic recursion.** Nested datatypes, or a function calling itself
  at a growing type such as `α`, `List α`, `List (List α)`, … would need
  infinitely many instances. Past a small depth, the growing argument
  becomes `lcAny`, so the set of instances stays finite. This is necessary:
  Reussir's own monomorphizer cannot handle polymorphic recursion.
- **Existential values.** A structure with a `Type`-valued field stores its
  payload boxed, and functions over the payload take `Box`.
- **Dynamic polymorphic dictionaries** (§2.4).

---

## 3. Stage 2 — Lean's mono pipeline (Lean's passes, driven by us)

We run Lean's own passes on the closed monomorphic program, in Lean's order.
Groups of mutually recursive declarations go bottom-up, callees first. Each
declaration is saved to the local extension so later passes can inline it,
and Lean's checker runs after every pass. This stage involves no new
translation logic; its job is to leave the code in the shape Stage 4
expects.

**`toMono`: semantic lowering done by Lean.**
- `Decidable` → `Bool`.
- `Nat` constructors and `cases` → `Nat.add x 1`, and `if n == 0 … else
  let m := n - 1`.
- `Int` `cases` → a sign test plus `natAbs`.
- `cases` on builtin runtime types (`Array`, `String`, `ByteArray`,
  `Float`, `Thunk`, `Task`, `UIntN`) → accessor externs.
- Single-field structures are unwrapped: `Char`→`UInt32`, `Fin n`→`Nat`,
  `Subtype`→its value, `Int8`→`UInt8`, `String.Pos`→`Nat`.
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
| `Unit`/`PUnit`, `lcVoid` | `unit` | the IO world is a `unit` value (probe) |
| `Nat`, `Int` | runtime type `Nat` / `Int`: a small machine word, or a bignum | Reussir has no bignum (§6) (probe) |
| `String` | runtime string type: an opaque, copy-on-write handle over Rust's `String` | std's `String` cannot be read from outside the std package (private field, probe); literals are built from `str` |
| `Array α` | `std::collections::cow::vec::Vec<⟦α⟧>` | copy-on-write, in place when unique (probe) |
| `ByteArray`, `FloatArray` | `Vec<u8>`, `Vec<f64>` | |
| `Thunk α`, `Task α`, `ST.Ref σ α` | runtime types over `⟦α⟧` | `σ` is a phantom |
| `Option α` | `std::option::Option<⟦α⟧>` | same constructors |
| `Except ε α`, `EST.Out ε σ α` | generated enums (next paragraph) | std has no `Result` at the pinned commit (probe) |

**`◾` (erased)** has no representation. Erased parameters, fields and `let`s
disappear, consistently at definitions and uses. One exception, for
closures, is in §5.3.

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

- **Shapes.** No fields anywhere means a `[value]` enum (no allocation).
  One constructor means a `struct`. Anything else is an `enum`.
- **Allocation.** Non-enum types are heap-allocated and reference-counted
  (`[shared]`), like Lean's.
- **Field order.** Reussir reorders fields by alignment internally, which
  is invisible to the program.
- **Recursion.** Recursive, mutual and nested inductives refer to each
  other's instances; `inductive Rose | node : List Rose → Rose` gives
  `Rose` and `List_Rose`, defined together.

**Function types** become curried Reussir closures: `A → B → C` is
`A -> (B -> C)`. §5.3 explains why they are curried.

**The uniform type `Box`.** When a data position has type `lcAny` (§2.6, §4),
its value is stored as `Box`.
- `Box` is a generated enum with one variant per concrete Reussir type that
  the program ever boxes; the set is known after Stage 1.
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
  IO world) to closures, and they count toward the arity. So in closure
  types they become `unit` parameters, applied as `()`, instead of
  disappearing. Direct calls simply drop them.
- **Constructors.** A partially applied constructor becomes a lambda that
  builds it. Constructors do no work, so timing does not matter.

Cost: a multi-argument call through an unknown closure allocates
intermediate closures. The same holds in native Lean for partial
applications. A faster representation is possible later (§7) without
changing when work runs.

### 5.4 `let`, `return`, literals

- `let x := v; k` becomes `let x = ⟦v⟧; ⟦k⟧`, and `return x` becomes `x`.
  Lean's passes have already removed dead `let`s. Lowering never adds or
  removes any, because a `let` can run a function that panics.
- Literals:
  - `Nat` literals become `Nat` values; big ones are built from their
    decimal string.
  - `UIntN` literals become typed Reussir literals.
  - String literals become a `String` built from a `str` literal with the
    same UTF-8 bytes. Escaping must round-trip every character.

### 5.5 `cases`

| Mono LCNF | Reussir |
|---|---|
| `cases b : Bool \| false => e₁ \| true => e₂` | `if b { ⟦e₂⟧ } else { ⟦e₁⟧ }` |
| `cases t : Tree Nat \| leaf => e₁ \| node l k r => e₂` | `match t { Tree_Nat::leaf => ⟦e₁⟧, Tree_Nat::node(l, k, r) => ⟦e₂⟧ }` |
| `cases p : P \| P.mk a b c => e` (single constructor) | `let a = p.a; let b = p.b; let c = p.c; ⟦e⟧` (probe: or a one-arm `match`) |
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
Three strategies, all correct because `body` is pure and runs exactly once on
each path that reaches it:

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

**Choice and nesting.** J1 applies first, then J2, then J3.
- J2 requires every jump to `j` to stay inside the same Reussir function.
  If `j` is also jumped to from inside a join point that was outlined, `j`
  is outlined too.
- Inner join points are lowered before the outer ones that contain them.

**Why the choice matters beyond style.**
- *Stack use.* Loops are recursive functions, and Lean runs self tail calls
  as loops. Under J1 and J2, a self tail call stays inside its own
  function, where LLVM reliably turns it into a loop. Under J3, the tail
  call goes through the outlined function. Reussir has no guaranteed tail
  calls. A probe showed that at `-O default` and above, mutual tail calls
  between separate functions compile to sibling calls, which run in
  constant stack; at `-O none` they do not. J3 is therefore the last
  resort, each use of it is reported, and lean2rr always compiles with
  optimization. Guaranteed tail calls remain a candidate Reussir request.
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
| `UInt32.add`, `UInt8.div`, `Float.add`, … | `+ - *` map to native Reussir arithmetic, since both wrap. Division, remainder, shifts and float→int always go through wrappers with `lean.h` semantics (e.g. `x / 0 = 0`, `x % 0 = x`, shift by `b % bits`, saturating casts): Reussir lowers them straight to LLVM operations that are undefined at those edge cases (probe). |
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
  functions are opaque side-effecting calls. The IO world is only `unit`,
  so nothing else stops Reussir or LLVM from merging, dropping or reordering
  two identical `println` calls (probe).
- **Lean-defined types in signatures.** Externs that take or return
  Lean-defined types (`IO.FS.Stream`, `IO.Error`, `Option`, `List`) get a
  small generated wrapper around runtime primitives on native types. That
  keeps the runtime independent of generated type names.
- **Borrowing.** Lean's borrow annotations (`@&`) are dropped. Reussir's
  owned convention plus its Perceus analysis gives the same results.

### 5.9 Panics and unreachable code

- `panic!` prints what native prints (`PANIC at …: msg`) to stderr, then
  **returns the default value and continues**, as native does.
- Reaching `unreachable` stops the program as Lean's
  `lean_internal_panic_unreachable` does (verify message).

### 5.10 IO and the world token

In mono, an IO function takes the world as an extra `lcVoid` parameter and
returns `EST.Out ε σ α`, with constructors `ok a` and `error e`. The world
becomes a `unit` parameter. `EST.Out` becomes an ordinary two-constructor
enum; its phantom `σ` is ignored. Effects happen inside runtime calls in
program order.

```
def main (w : lcVoid) : EST.Out IO.Error lcAny PUnit :=     fn main_(w : unit) -> EST_Out_IOError_Unit {
  let s := "hi"; let r := IO.println@spec s w; return r  ↦     let s = String::from_str("hi"); IO_println_spec(s, w)
                                                            }
```

### 5.11 Program entry

A generated Reussir `#[main]`:
1. runs the startup work of §5.12;
2. calls the translated `main`, passing the argument list (without the
   program name) if `main` takes one, and the world `()`;
3. on `error e`, prints `uncaught exception: <message>` to stderr and exits
   with status 1;
4. otherwise exits with the returned `UInt32` (0 for `IO Unit`).

The runtime flushes stdout at exit. These behaviours were observed on native
executables.

### 5.12 Constants (CAFs) and closed terms

Native Lean behaves as follows (observed):
- every zero-parameter declaration of a module is **evaluated at program
  start**, in the module initializer, *even if unused*;
- `extractClosed` constants are evaluated **lazily, once**, on first use;
- all of these values live for the whole run.

Our translation:
- **User-module constants whose value involves a function call** are
  evaluated at startup, before `main`, including unused ones. They can
  panic, trace, or loop, just as natively.
- **Constants that are plain data** (literals, constructors, partial
  applications) may be built lazily; that is indistinguishable.
- **Toolchain constants** (Init/Std) are evaluated lazily, once. Every
  native Lean program evaluates all of them at startup without any visible
  effect, so laziness changes nothing but speed.
- **Closed terms** are lazy, once.
- **`initialize`/`builtin_initialize` declarations** of user modules are IO
  actions that native runs in the module initializer. They run at startup in
  the same module order, and their results are stored like constants.

The storage is a once-cell per constant, holding a value that is never
freed. It is either a runtime facility or a Reussir global, and is a
candidate Reussir feature.

### 5.13 Names

Generated names are unique per (Lean name, instance type arguments), valid
Reussir identifiers, and never clash with runtime or std names. Lean names
are mangled with Lean's own scheme; type arguments are appended in an
unambiguous encoding.

---

## 6. Runtime (`leanrt`)

The runtime provides what Reussir lacks:
- `Nat`/`Int`: a small value, or a Rust bignum;
- Lean's `String` operations over `std::string::String`;
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

---

## 9. Open items

Probe results so far (preliminary; to be re-checked when the probes are
completed):
- **Output.** Printing and argv go through Reussir's polymorphic FFI: Rust
  function bodies (`println!`, `std::env::args`) compiled into the program.
- **Standard library.** Using it requires linking the prebuilt std
  interfaces and archives. It has no `Result` type. `std::string::String`
  cannot be read from outside the std package, so the runtime defines its
  own string handle.
- **Runtime types in Rust.** An opaque runtime type must be nameable with
  only `std` and `reussir_rt` in scope, and the Rust glue is compiled at
  edition 2015. External Rust crates (e.g. `num-bigint`) are usable when
  built by the same `rustc`. A C-ABI shared library and statically linked
  GMP also work.
- **Recursion limits.** Polymorphic recursion makes Reussir's monomorphizer
  loop without a diagnostic, and non-regular datatypes crash it at nesting
  depth 128. lean2rr must never emit either; the §2.6 depth cap and `Box`
  guarantee that.
- **Arithmetic.** It lowers directly to LLVM: division, remainder, shifts
  and float→int are undefined at the edge cases (hence the wrappers of
  §5.8), and `+ - *` wrap.
- **Tail calls.** Mutual tail calls compile to sibling calls at
  `-O default` and above (§5.6).

Still to probe (Reussir):
- whether a `[value]` enum can hold a runtime handle (for `Nat`);
- `unit` parameters, and closures returning closures;
- whether effectful runtime calls are kept and ordered;
- syntax limits for generated names and matches;
- globals or once-cells;
- compile time on large generated files.

To verify (Lean):
- the message printed on reaching unreachable code;
- the evaluation order of startup constants and initializers;
- that no local functions survive `lambdaLifting`;
- the exact `lean_apply_n` behaviour;
- that every Lean use of pointer equality is a shortcut, so answering
  "not equal" is safe.
