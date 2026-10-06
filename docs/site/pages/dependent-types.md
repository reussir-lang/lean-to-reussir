# Dependent types

<p class="lead">How lean2rr compiles a type that depends on a run-time value.
Sources: translation plan
<a href="repo:docs/translation-plan.md#26-when-a-type-is-not-statically-known">§2.6</a>,
<a href="repo:docs/translation-plan.md#4-stage-3--check-and-recover-lost-types">§4</a> and
<a href="repo:docs/translation-plan.md#10-known-divergences-and-unsupported-features">§10</a>,
and the implementation notes on
<a href="repo:docs/implementation/types/uniform-types.md">unknown types</a> and
<a href="repo:docs/implementation/representations/box-and-uniform.md">the uniform type</a>.</p>

<div class="rule" markdown="1">
**Types do not compute. Values do.** A Lean program can look at a value's
constructor, but it can never look at a type. So lean2rr erases every type.
Where Lean's compiler marks a type as unknown (`lcAny`), the value goes into
one enum, `L2RBox`. Code reads the value by matching the enum's variant.
lean2rr compiles every program that Lean compiles, and gives the same
results as the native build.
</div>

A *dependent type* is a type that mentions a value, such as the `n` in
`Vector String n`, or a type that a value chooses, such as `t.denote` below.
This page shows why such types need nothing special at run time.

## Why types can be erased

- **A program cannot compute with a type.** Lean has no `match` on a type.
  A `match` looks at a value and selects a branch by the value's
  constructor.
- **Types and proofs hold no data.** A type argument, a field whose value is
  a type (`α : Type`), and a proof give the program no information at run
  time. Lean's compiler erases them. It writes `◾` for an erased argument,
  and `lcAny` for a value whose type it does not know.
- **The two marks are different.** `◾` replaces a value that holds no data
  (a type or a proof), and lean2rr discards it. `lcAny` replaces only the
  value's *type*. The value itself is data that the program uses, such as
  the number 5 in `⟨.nat, 5⟩` below, so lean2rr keeps it, in the enum. Lean's
  own documentation says the same: `lcErased` is "information that has been
  erased", and `lcAny` is a "type dependency that has been erased". A native
  build keeps an `lcAny` value as an object and drops a `◾` value.
- **Native Lean does the same.** In a native build, every value is one
  machine word (`lean_object*`): a pointer to an object, or a small number
  inside the word. No value carries its type.

In Rust terms: a value of unknown type is like a `Box<dyn Any>`. A Rust
program gets the value back with `downcast`, which checks a type id. lean2rr
needs no type id, because the program's own values tell which variant to
expect (see [The rule](#the-rule)).

## The rule

1. **Types, type parameters and proofs have no storage.** For example, the
   field `α : Type` of a structure takes no space.
2. **A value of unknown type is an `L2RBox`.** `L2RBox` is one enum per
   program, with one variant for each kind of value that the program puts
   into it, and a unit variant for Lean's `box(0)` placeholder.
3. **Code that needs the value matches the variant.** Lean's type checker
   guarantees which variant is there. The match only takes the value out.
4. **A generic function called at an unknown type has one copy that works
   on boxes:** the *uniform instance*.

For the examples on this page, lean2rr generates this `L2RBox` (checked
with `lean2rr --emit rr`):

```rust
enum L2RBox {
    b0(L2RUnit),   // the unit variant: Lean's box(0)
    b1(LStr),      // a boxed String
    b2(Nat)        // a boxed Nat
}
```

In Rust terms, this is `enum L2RBox { Unit, Str(LStr), Nat(Nat) }`. The
variants have numbers, in the order in which lean2rr needs them.

## Examples

### A column whose element type is a field

```lean
inductive Ty | nat | str

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String

structure Column where
  ty : Ty
  data : Array ty.denote
```

- Line 1: `Ty` is an enumeration with two values, `nat` and `str`.
- Line 3: `Ty.denote` is a function from a `Ty` to a type. `@[reducible]`
  lets Lean's type checker unfold it.
- Lines 4 and 5: `.nat` gives the type `Nat`, and `.str` gives the type
  `String`.
- Line 7: `Column` is a structure.
- Line 8: the field `ty` is a `Ty`.
- Line 9: the field `data` is an array. Its element type is `ty.denote`, so
  it depends on the value of the field `ty`.

Rust has no direct equivalent: a field's type cannot depend on another
field's value. The nearest Rust type is an enum with one variant per tag:
`enum Column { Nat(Vec<Nat>), Str(Vec<String>) }`.

Code that uses a column matches on the value `ty` first:

```lean
def Column.push (c : Column) (i : Nat) : Column :=
  match c with
  | ⟨.nat, d⟩ => ⟨.nat, d.push i⟩
  | ⟨.str, d⟩ => ⟨.str, d.push (toString i)⟩
```

- Line 1: `push` takes a column `c` and a number `i`, and returns a column.
- Line 2: it looks at the two fields of `c`.
- Line 3: if `ty` is `.nat`, then `d` is an `Array Nat`. `push` adds `i`
  and builds a new column.
- Line 4: if `ty` is `.str`, then `d` is an `Array String`. `push` adds
  `i` as a string.

The match is on the value `ty`, not on a type. lean2rr generates this code
(abridged, names shortened):

```rust
struct T_Column(RVec<L2RBox>, T_Ty)   // data, then ty
enum [value] T_Ty { c_nat, c_str }    // stored inline, never allocated

fn Column_push(c : T_Column, i : Nat) -> T_Column {
    let ty : T_Ty = c.1;
    let d : RVec<L2RBox> = c.0;
    match ty {
        T_Ty::c_nat => {
            let d2 : RVec<L2RBox> = lean_array_push<L2RBox>(d, L2RBox::b2{i});
            T_Column{d2, T_Ty::c_nat{}}
        },
        T_Ty::c_str => {
            let s : LStr = l2r_nat_repr(i);
            let d2 : RVec<L2RBox> = lean_array_push<L2RBox>(d, L2RBox::b1{s});
            T_Column{d2, T_Ty::c_str{}}
        }
    }
}
```

- `data` is an `RVec<L2RBox>`: an array of boxes.
- `push` puts the new element into its variant (`L2RBox::b2{i}`). It
  updates the array in place when the array is unique.
- `ty` is a `[value]` enum, so a `Column` is one cell, plus its array.

A read takes the value out of its variant. This is a read of one element of
a `.str` column (abridged):

```rust
let s : LStr = match lean_array_uget<L2RBox>(d, i) {
    L2RBox::b1(s) => { s },                // the String variant
    L2RBox::b0(_) => { l2r_zero_LStr() },  // Lean's box(0): the zero String
    _ => { l2r_unreachable<LStr>() }       // no other variant holds a String
};
```

The program matched `ty = .str` before the read, so the element is a
`String`. The last arm never runs.

### A type chosen by a Boolean

```lean
def pick (b : Bool) : if b then Nat else String :=
  match b with
  | true => (42 : Nat)
  | false => "hello"

def describe : (b : Bool) → (if b then Nat else String) → String
  | true, n => let m : Nat := n; s!"nat {m + 1}"
  | false, s => let t : String := s; s!"str {t}"
```

- Line 1: `pick` takes a Boolean `b`. Its result type is `Nat` if `b` is
  true, else `String`.
- Lines 2 to 4: it returns the number 42 or the string `"hello"`.
- Line 6: `describe` takes a Boolean and a value whose type depends on that
  Boolean. It returns a string.
- Line 7: if the Boolean is true, the value is a `Nat`.
- Line 8: if the Boolean is false, the value is a `String`.

Both functions give that position the type `L2RBox`:

```rust
fn pick(b : bool) -> L2RBox                 // L2RBox::b2{42} or L2RBox::b1{"hello"}
fn describe(b : bool, v : L2RBox) -> LStr   // each branch takes v out of its variant
```

`describe` decides by the value of `b`, then takes `v` out of the variant
that `b` guarantees.

### Sigma types

A Sigma type `(x : A) × B x` is a pair. The type of its second component
depends on the value of its first component.

```lean
def entries : List ((t : Ty) × t.denote) :=
  [⟨.nat, (5 : Nat)⟩, ⟨.str, "five"⟩]

def vecs : List ((n : Nat) × Vector String n) :=
  [⟨2, ⟨#["a", "b"], rfl⟩⟩, ⟨0, ⟨#[], rfl⟩⟩]
```

- Line 1: `entries` is a list of pairs. In each pair, the first component
  `t` is a `Ty`, and the second component has the type `t.denote`.
- Line 2: the first pair holds `.nat` and the `Nat` 5. The second pair
  holds `.str` and the `String` `"five"`.
- Line 4: `vecs` is a list of pairs. The first component `n` is a `Nat`.
  The second is a `Vector String n`: an array of exactly `n` strings.
- Line 5: `⟨#["a", "b"], rfl⟩` builds a vector from an array and a proof
  (`rfl`) that the size of the array is 2.

| Lean type | lean2rr build (checked with `--emit rr`) | Boxed |
|---|---|---|
| `(t : Ty) × t.denote` | `struct T_Sigma(L2RBox, T_Ty)`: the second component, then the first | the second component |
| `(n : Nat) × Vector String n` | `struct T_Sigma(Nat, RVec<LStr>)` | nothing |

- `t.denote` is a different type for each `t`, so the second component is
  an `L2RBox`.
- `Vector String n` holds the same data for every `n`: an `Array String`.
  `n` occurs only in the type and in the proof, and both are erased. So
  the second component is an `RVec<LStr>`, and nothing is boxed.

### At run time

{{svg:depvalues}}

### A type unpacked from an existential

```lean
structure Pkg where
  α : Type
  val : α
  fmt : α → String
```

- Line 1: `Pkg` is a structure: a package of a type and a value.
- Line 2: the field `α` is a type. It holds no data, so it is erased.
- Line 3: the field `val` is a value of the type `α`.
- Line 4: the field `fmt` is a function that turns an `α` into a string.

In Rust terms, a `Pkg` is like a `Box<dyn Display>`. lean2rr generates
`struct T_Pkg(L2RBox, …)`: `val` is an `L2RBox`, and `fmt` is a function
value that takes an `L2RBox`. The code that builds a package knows the type
of `val`. It puts `val` into its variant, and it wraps `fmt` so that `fmt`
takes the value out of that variant. Generic code calls `p.fmt p.val`
without knowing the type.

### Polymorphic recursion

```lean
def nest {α : Type} [ToString α] : Nat → α → String
  | 0, x => toString x
  | n + 1, x => nest n (x, x)
```

- Line 1: `nest` is generic over a type `α` that can be printed. `nest`
  takes a count and an `α`.
- Line 2: at count 0, it prints `x`.
- Line 3: otherwise, it calls itself with the pair `(x, x)`, at the type
  `α × α`.

The types grow without end (`Nat`, `Nat × Nat`, …), so no copy per type is
possible. lean2rr calls the uniform instance for the growing calls. There,
`x` is an `L2RBox`, and the `ToString` dictionary is a run-time value.

### A partial application that leaves a type open

```lean
structure Op where
  run : {α : Type} → List α → Nat

def ops : List Op := [⟨List.length⟩, ⟨fun xs => xs.length * 2⟩]
```

- Line 1: `Op` is a structure.
- Line 2: its one field, `run`, is a generic function: it takes a list of
  any element type and returns a `Nat`.
- Line 4: `ops` holds two such functions.

The field's function takes a list of boxes: `List.length` runs at `lcAny`.

## What was checked

Two independent reviews checked four statements against the source of Lean
4.34.0 and against native builds. They agree on every verdict.

| Statement | Verdict |
|---|---|
| A value marked `◾` holds no data, and a compiler can drop it. | correct (one exception in Lean itself, see below) |
| A value of type `lcAny` can be dropped, because a program cannot compute with types. | **incorrect** |
| A value of type `lcAny` holds data that can change the result, so a compiler must keep it. | correct |
| One layout for each datatype, with an enum in the unknown positions, gives native results. | correct when the rule covers all the cases of [The planned implementation](#the-planned-implementation) |

The reason: `lcAny` replaces only the *type* of a value. Lean's compiler
erases a value only when its type is a proposition or a type
(`ToLCNF.lean`). A native build keeps an `lcAny` value as an object pointer
(`ToImpureType.lean`). An example from the reviews:

```lean
def pick (α : Type) (b : Bool) (x y : α) : α := if b then x else y
```

- `pick` takes a type `α`, a Boolean and two values of the type `α`. It
  returns `x` if `b` is true, else `y`.
- After erasure, `α` is `◾`: it is dropped. `x` and `y` have the type
  `lcAny`: they are kept. The result is one of them, so a compiler that
  dropped them could not return it.

**One exception in Lean itself.** A review found a program where Lean
4.34.0's own compiler gives a value that holds data the mark `◾`. The
native build then prints a wrong result: 100, where Lean's kernel proves
200. This is recorded for judgment. lean2rr does not copy a Lean bug after
a judge confirms it (plan §10, "Lean bugs we do not reproduce").

## The planned implementation

This is native Lean's own representation. lean2rr writes Lean's uniform
pointer as an explicit enum, because Reussir is a typed language.

1. **Not stored:** types, type arguments and proofs (`◾`). A function keeps
   its parameter list. A function whose parameters are all erased stays a
   function, and does not become a constant: a constant is computed at
   startup, and the function body would then run when no call runs it.
2. **One layout for each datatype.** lean2rr computes the layout of each
   constructor one time, from its declared field types, whatever the type
   arguments are. `Tree Nat` and `Tree α` are the same type.
3. **Every `lcAny` position holds an `L2RBox`.** This includes fields,
   parameters, results, local values and the arguments of function values.
   The type can be unknown in four ways:
    - a type parameter (`x : α`);
    - a type stored in another field (`val : α` in a package with the field
      `α : Type`);
    - a type computed from a value (`Sigma.snd`, `Array ty.denote`);
    - a type function applied to an argument (`f Nat`, with `f` a
      parameter).
4. **The enum has one variant for each run-time layout,** not one for each
   type:
    - one variant for each datatype;
    - one for each kind of scalar;
    - one for function values;
    - one for strings, arrays and big numbers;
    - one *erased* variant, because a type or a proof can occupy such a
      position.

   Thus the set of variants is finite, also when polymorphic recursion
   makes the set of types infinite.
5. **A field with a concrete type keeps that type.** In
   `structure P where x : Float`, `x` is a raw `f64`.
6. **Box and unbox at the boundary.** A value of a known type is put into
   its variant where it goes into an `lcAny` position. It is taken out where
   it comes back to a known type.
7. **One calling convention for function values.** A function that is
   stored where its type is generic gets an entry that takes and returns
   `L2RBox` values. Native Lean uses `_boxed` wrappers in the same way.
8. **A structure with one relevant field is that field** (`Fin n`,
   `Subtype`), as in native Lean.
9. **Casts in Lean's library go through the enum.** `Dynamic`,
   `Array.mapM` (through `mapMUnsafe`) and `ShareCommon` use `NonScalar`
   with unsafe casts. lean2rr represents `NonScalar` as an `L2RBox`, so each
   such cast is a box or an unbox.
10. **Unsafe functions that look at representations** (`ptrAddrUnsafe`,
    `isExclusiveUnsafe`, `ptrEq`) can answer differently, as today (see
    [Known differences](differences.html#identity-and-sharing)).

The enum is closed: it lists the variants of one program. That is possible
because lean2rr compiles the whole program at one time.

### Memory compared with native

The enum's encoding is not chosen yet. A two-word enum (an 8-byte tag word
and an 8-byte payload) works with Reussir today:

| Value | Native | Two-word enum |
|---|---|---|
| `structure P where a : UInt64; b : Nat; c : Float` | 1 allocation, 32 B | the same |
| `UInt64 × UInt64` | 3 allocations, 56 B | 1 allocation, 40 B |
| `List Float`, one cell | 2 allocations, 40 B | 1 allocation, 32 B |
| `List Nat` (small values), one cell | 1 allocation, 24 B | 1 allocation, 32 B |
| `Array Nat`, one element | 8 B | 16 B |
| `Array Float`, one element | 8 B and a 16 B box | 16 B, no allocation |

- The two-word enum never allocates where native does not. It saves the
  box of each 64-bit scalar in a generic position. It doubles the size of a
  generic position that holds a pointer or a small value.
- A one-word encoding (a small value inside the word, an object as its
  pointer) has the same sizes as native, and boxes 64-bit scalars as native
  does. It needs more support from Reussir.
- Measured natively: a list of 10<sup>6</sup> small `Nat`s takes 47 MB, a
  list of 10<sup>6</sup> `Float`s 63 MB (the boxes).

Status: planned, not implemented.

## The current version

The current version does not follow rule 2. It gives a generic type a
separate layout for each type argument: a `Tree Float` leaf holds the `f64`
itself, and a `Tree Nat` leaf holds the `Nat` word. The unknown case,
`Tree lcAny`, has another layout, whose leaf holds an `L2RBox`. When a value
goes from one layout to another, the current version rebuilds it, node by
node:

```lean
def build : Nat → Tree Nat
  | 0 => .leaf 7
  | n + 1 => let t := build n; .node t t   -- both children are the same t

structure Packed where                      -- a tree whose element type is a field
  α : Type
  tree : Tree α

leftDepth ⟨Nat, build n⟩                    -- Tree Nat goes into Tree lcAny
```

- `build n` has only n + 1 nodes, because each node points two times to the
  same child.
- The conversion follows each pointer separately, so it makes
  2<sup>n+1</sup> − 1 nodes.

| n | native Lean | current version |
|---|---|---|
| 16 | 7.9 MB | 11 MB |
| 20 | 7.9 MB | 65 MB |
| 24 | 7.9 MB | 927 MB |

The output is correct, but the memory grows exponentially, and a loop that
crosses at each step is quadratic. Today each boxed value is also one heap
cell: a column of 10<sup>6</sup> small `Nat`s takes 48 MB, natively 31 MB.
The planned implementation removes the conversions, because each datatype
has one layout. Plan
[§10](repo:docs/translation-plan.md#10-known-divergences-and-unsupported-features)
lists these costs.
