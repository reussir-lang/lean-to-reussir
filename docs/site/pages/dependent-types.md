# Dependent types

<p class="lead">How lean2rr stores a value whose type depends on another
value, or whose type is not known at compile time. Sources: translation
plan
<a href="repo:docs/translation-plan.md#26-when-a-type-is-not-statically-known">§2.6</a>
and
<a href="repo:docs/translation-plan.md#10-known-divergences-and-unsupported-features">§10</a>,
and the implementation notes on
<a href="repo:docs/implementation/types/uniform-types.md">unknown types</a> and
<a href="repo:docs/implementation/representations/box-and-uniform.md">the uniform type</a>.</p>

<div class="rule" markdown="1">
**lean2rr keeps values and discards types.** A value whose type the
compiler does not know goes into one enum, `L2RBox`. The program reads the
value with a `match` on the enum's variant.
</div>

A *dependent type* is a type that contains a value, such as the `n` in
`Vector String n`, or a type that a value selects, such as `t.denote` below.

## Types and values

Lean's compiler replaces two kinds of items before lean2rr reads the code:

- **`◾`** replaces an item without data: a type, a type argument or a proof.
  lean2rr does not store it.
- **`lcAny`** replaces the *type* of a value when the compiler does not know
  that type. The value itself has data. lean2rr stores the value in an
  `L2RBox`.

An example:

```lean
def pick (α : Type) (b : Bool) (x y : α) : α := if b then x else y
```

- `pick` takes a type `α`, a Boolean `b`, and two values `x` and `y` of the
  type `α`. It returns `x` if `b` is true, else `y`.
- `α` becomes `◾`. lean2rr does not store it.
- `x` and `y` have the type `lcAny`. Each one is an `L2RBox`.

In Rust terms, an `L2RBox` is similar to a `Box<dyn Any>`.

## The enum `L2RBox`

Each program has one `L2RBox` enum. It has one variant for each run-time
layout:

- one variant for each datatype;
- one variant for each kind of scalar;
- one variant for function values;
- one variant for strings, one for arrays, one for big numbers;
- one *erased* variant, for a type or a proof in such a position.

The set of variants is finite. It stays finite when polymorphic recursion
makes the set of types infinite. lean2rr compiles the whole program at one
time, so it knows all the variants.

For the examples on this page, the enum has three variants:

```rust
enum L2RBox {
    b0(L2RUnit),   // the unit variant: Lean's box(0)
    b1(LStr),      // a String
    b2(Nat)        // a Nat
}
```

Code that needs the value matches the variant. This code reads one element
of an array of boxes as a `String`:

```rust
let s : LStr = match lean_array_uget<L2RBox>(d, i) {
    L2RBox::b1(s) => { s },                // the String variant
    L2RBox::b0(_) => { l2r_zero_LStr() },  // Lean's box(0): the zero String
    _ => { l2r_unreachable<LStr>() }       // no other variant holds a String
};
```

Lean's type checker makes sure that the value is a `String` at this point.
The last arm does not run.

## Where lean2rr uses the enum

Every position whose type is `lcAny` holds an `L2RBox`: a field, a
parameter, a result, a local value, or an argument of a function value. A
type is unknown in these cases:

- a type parameter (`x : α`);
- a type that another field holds (`val : α` in a structure with the field
  `α : Type`);
- a type that a value selects (`Sigma.snd`, `Array ty.denote`);
- a type function applied to an argument (`f Nat`, with `f` a parameter).

lean2rr puts a value into its variant where the value goes into such a
position. It takes the value out where the value comes back to a known
type.

## Layouts of generic types

These are the layout rules:

1. **One layout for each datatype.** lean2rr computes the layout of each
   constructor one time, from the declared field types. `Tree Nat` and
   `Tree α` have the same layout.
2. **A field with a concrete type keeps that type.** In
   `structure P where x : Float`, `x` is a raw `f64`.
3. **A structure with one relevant field is that field** (`Fin n`,
   `Subtype`).
4. **A function keeps its parameter list.** A function whose parameters are
   all erased stays a function. It does not become a constant, because
   lean2rr computes constants at startup.
5. **Function values have one calling convention.** A function that is
   stored where its type is generic gets an entry that takes and returns
   `L2RBox` values.
6. **Casts in Lean's library go through the enum.** `Dynamic`,
   `Array.mapM` and `ShareCommon` use `NonScalar` with unsafe casts.
   lean2rr represents `NonScalar` as an `L2RBox`.
7. **Unsafe functions that read a representation** (`ptrAddrUnsafe`,
   `isExclusiveUnsafe`, `ptrEq`) can give other answers than in a native
   build (see [Known differences](differences.html#identity-and-sharing)).

Native Lean uses the same layout scheme. In a native build, a field of
unknown type is one `lean_object*` word.

### Memory

The encoding of the enum is not fixed yet. This table shows a two-word
enum (an 8-byte tag word and an 8-byte payload):

| Value | Native | Two-word enum |
|---|---|---|
| `structure P where a : UInt64; b : Nat; c : Float` | 1 allocation, 32 B | 1 allocation, 32 B |
| `UInt64 × UInt64` | 3 allocations, 56 B | 1 allocation, 40 B |
| `List Float`, one cell | 2 allocations, 40 B | 1 allocation, 32 B |
| `List Nat` (small values), one cell | 1 allocation, 24 B | 1 allocation, 32 B |
| `Array Nat`, one element | 8 B | 16 B |
| `Array Float`, one element | 8 B and a 16 B box | 16 B, no allocation |

A one-word encoding has the same sizes as native. It puts a small value
inside the word and an object as its pointer. It boxes 64-bit scalars, as
native does. It needs more support from Reussir.

Status: rule 1 is planned. Today a generic type has one layout for each
type argument, and the enum has one variant for each such layout (see
[The current version](#the-current-version)).

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
- Line 3: `Ty.denote` is a function from a `Ty` to a type.
- Lines 4 and 5: `.nat` gives the type `Nat`, and `.str` gives the type
  `String`.
- Line 7: `Column` is a structure.
- Line 8: the field `ty` is a `Ty`.
- Line 9: the field `data` is an array. Its element type depends on the
  value of the field `ty`.

The nearest Rust type is an enum with one variant for each tag:
`enum Column { Nat(Vec<Nat>), Str(Vec<String>) }`.

Code that uses a column matches on the value `ty` first:

```lean
def Column.push (c : Column) (i : Nat) : Column :=
  match c with
  | ⟨.nat, d⟩ => ⟨.nat, d.push i⟩
  | ⟨.str, d⟩ => ⟨.str, d.push (toString i)⟩
```

- Line 1: `push` takes a column `c` and a number `i`, and returns a column.
- Line 3: if `ty` is `.nat`, then `d` is an `Array Nat`. `push` adds `i`.
- Line 4: if `ty` is `.str`, then `d` is an `Array String`. `push` adds
  `i` as a string.

lean2rr generates this code (abridged, names shortened):

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
  changes the array in place when the array is unique.
- `ty` is a `[value]` enum. A `Column` is one cell, plus its array.

### A type selected by a Boolean

```lean
def pickT (b : Bool) : if b then Nat else String :=
  match b with
  | true => (42 : Nat)
  | false => "hello"

def describe : (b : Bool) → (if b then Nat else String) → String
  | true, n => let m : Nat := n; s!"nat {m + 1}"
  | false, s => let t : String := s; s!"str {t}"
```

- Line 1: the result type of `pickT` is `Nat` if `b` is true, else
  `String`.
- Lines 2 to 4: `pickT` returns the number 42 or the string `"hello"`.
- Line 6: `describe` takes a Boolean and a value whose type depends on that
  Boolean.
- Lines 7 and 8: each branch uses the value at the type that the Boolean
  selects.

Both functions use the type `L2RBox` for that position:

```rust
fn pickT(b : bool) -> L2RBox                // L2RBox::b2{42} or L2RBox::b1{"hello"}
fn describe(b : bool, v : L2RBox) -> LStr   // each branch takes v out of its variant
```

### Sigma types

A Sigma type `(x : A) × B x` is a pair. The type of its second component
depends on the value of its first component.

```lean
def entries : List ((t : Ty) × t.denote) :=
  [⟨.nat, (5 : Nat)⟩, ⟨.str, "five"⟩]
```

- Line 1: `entries` is a list of pairs. In each pair, the second component
  has the type `t.denote`, where `t` is the first component.
- Line 2: the first pair holds `.nat` and the number 5. The second pair
  holds `.str` and the string `"five"`.

The type of the second component is not known at compile time. The second
component is an `L2RBox`.

### A type stored in a field

```lean
structure Pkg where
  α : Type
  val : α
  fmt : α → String
```

- Line 2: the field `α` is a type. lean2rr does not store it.
- Line 3: the field `val` is a value of the type `α`. It is an `L2RBox`.
- Line 4: the field `fmt` is a function that turns an `α` into a string.

In Rust terms, a `Pkg` is similar to a `Box<dyn Display>`. The code that
builds a package knows the type of `val`. It puts `val` into its variant.
The function `fmt` takes an `L2RBox` and takes the value out of that
variant.

### Polymorphic recursion

```lean
def nest {α : Type} [ToString α] : Nat → α → String
  | 0, x => toString x
  | n + 1, x => nest n (x, x)
```

- Line 1: `nest` takes a count and a value of a type `α` that can be
  printed.
- Line 2: at count 0, it prints the value.
- Line 3: else it calls itself with the pair `(x, x)`, at the type `α × α`.

The types grow without end: `Nat`, `Nat × Nat`, and so on. lean2rr compiles
one copy of `nest` for these calls. In that copy, `x` is an `L2RBox`, and
the `ToString` dictionary is a value that the copy receives.

### A partial application that leaves a type open

```lean
structure Op where
  run : {α : Type} → List α → Nat

def ops : List Op := [⟨List.length⟩, ⟨fun xs => xs.length * 2⟩]
```

- Line 2: the field `run` is a function that takes a list of any element
  type.
- Line 4: `ops` holds two such functions.

The function in the field takes a list whose elements are `L2RBox`
values.

## The current version

The current version gives a generic type one layout for each type
argument. A `Tree Float` leaf holds the `f64`, and a `Tree Nat` leaf holds
the `Nat` word. The unknown case, `Tree lcAny`, has another layout, whose
leaf holds an `L2RBox`.

When a value goes from one layout to another, the current version rebuilds
it, node by node:

```lean
def build : Nat → Tree Nat
  | 0 => .leaf 7
  | n + 1 => let t := build n; .node t t   -- both children are the same t

structure Packed where                      -- a tree whose element type is a field
  α : Type
  tree : Tree α

leftDepth ⟨Nat, build n⟩                    -- Tree Nat goes into Tree lcAny
```

- `build n` has n + 1 nodes. Each node points two times to the same child.
- The conversion follows each pointer separately. It makes
  2<sup>n+1</sup> − 1 nodes.

| n | Native | Current version |
|---|---|---|
| 16 | 7.9 MB | 11 MB |
| 20 | 7.9 MB | 65 MB |
| 24 | 7.9 MB | 927 MB |

Each boxed value is also one heap cell in the current version. A column of
10<sup>6</sup> small `Nat`s takes 48 MB, and 31 MB in a native build. With
rule 1 of [Layouts of generic types](#layouts-of-generic-types), a value
keeps one layout, and lean2rr does not convert it. Plan
[§10](repo:docs/translation-plan.md#10-known-divergences-and-unsupported-features)
lists the costs of the current version.
