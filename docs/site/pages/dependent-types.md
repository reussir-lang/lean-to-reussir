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

The Reussir code on this page is the code that lean2rr generates for one
program with all the examples (checked with `--keep-rr`). The names are
shorter and easier to read than the generated names.

## Types and values

Lean's compiler translates a program to LCNF, its intermediate code. In
LCNF, it replaces two kinds of items:

- **`◾`** replaces an item without data: a type, a type argument or a proof.
  In a type, LCNF writes it as `lcErased`. lean2rr does not store it.
- **`lcAny`** replaces the *type* of a value when the compiler does not know
  that type. The value itself has data. lean2rr stores the value in an
  `L2RBox`.

An example:

```lean
def pick (α : Type) (b : Bool) (x y : α) : α := if b then x else y
```

- `pick` takes a type `α`, a Boolean `b`, and two values `x` and `y` of the
  type `α`. It returns `x` if `b` is true, else `y`.

Lean's compiler gives this LCNF (mono phase, with the parameter types):

```text
def pick (α : lcErased) (b : Bool) (x : lcAny) (y : lcAny) : lcAny :=
  cases b : lcAny
  | Bool.false =>
    return y
  | Bool.true =>
    return x
```

- `α` is `lcErased`. lean2rr does not store it.
- `x`, `y` and the result have the type `lcAny`. Each one holds data.
- `cases b : lcAny` is a match on `b`. In LCNF, the type after the colon is
  the type of the result of the whole match, not the type of `b`.

lean2rr makes a copy of `pick` for each type argument that the program
uses. The program on this page calls `pick Nat`. lean2rr generates this
copy:

```rust
fn pick_Nat(b : bool, x : Nat, y : Nat) -> Nat {   // α is not a parameter
    if b { x } else { y }
}
```

- In the copy at `Nat`, `x` and `y` are `Nat` values. A copy at an unknown
  type uses `L2RBox` for `x` and `y`.

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

All the examples on this page are in one program. For that program,
lean2rr generates this enum:

```rust
enum L2RBox {
    b0(L2RUnit),      // the unit variant: Lean's box(0)
    b1(LStr),         // a String
    b2(Nat),          // a Nat
    b3(Ref_StdGen),   // a reference cell (IO.stdGenRef, made at startup)
    b4(Prod_Box),     // a pair of two boxes (Prod lcAny lcAny)
    b5(Prod_Nat)      // a pair of two Nats (Prod Nat Nat)
}
```

`b4` and `b5` are two layouts of `Prod`. The current version gives each
type argument its own layout (see [The current version](#the-current-version)).

Code that needs the value matches the variant. This code, from `describe`
below, takes a `String` out of an `L2RBox` `v`:

```rust
match v {
    L2RBox::b1(s) => { s },                  // the String variant
    L2RBox::b0(_) => { zero_String() },      // Lean's box(0): the empty String
    _ => { l2r_unreachable<LStr>() }         // no other variant holds a String
}
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

LCNF (mono phase):

```text
def Column.push (c : Column) (i : Nat) : Column :=
  cases c : Column
  | Column.mk (ty.1 : Ty) (data.2 : Array lcAny) =>
    cases ty.1 : Column
    | Ty.nat =>
      let _x.3 := Array.push ◾ data.2 i;
      let _x.4 := mk ty.1 _x.3;
      return _x.4
    | Ty.str =>
      let _x.5 := Nat.reprFast i;
      let _x.6 := Array.push ◾ data.2 _x.5;
      let _x.7 := mk ty.1 _x.6;
      return _x.7
```

- `cases ty.1 : Column` is a match on `ty.1`, a `Ty`. `Column` is the type
  of the result of the match: each branch returns a column.
- The field `data` has the type `Array lcAny`: an array whose element type
  is not known.
- `Array.push ◾ data.2 i`: the first argument is the element type. It is
  `◾`: it holds no data.

lean2rr generates this code:

```rust
struct Column(RVec<L2RBox>, Ty)       // data, then ty
enum [value] Ty { c_nat, c_str }      // stored inline, never allocated

fn Column_push(c : Column, i : Nat) -> Column {
    let ty : Ty = c.1;
    let data : RVec<L2RBox> = c.0;
    match ty {
        Ty::c_nat => {
            let data2 : RVec<L2RBox> = lean_array_push<L2RBox>(data, L2RBox::b2{i});
            Column{data2, Ty::c_nat{}}
        },
        Ty::c_str => {
            let s : LStr = l2r_nat_repr(i);
            let data2 : RVec<L2RBox> = lean_array_push<L2RBox>(data, L2RBox::b1{s});
            Column{data2, Ty::c_str{}}
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

LCNF (mono phase):

```text
def pickT (b : Bool) : lcAny :=
  cases b : lcAny
  | Bool.false =>
    let _x.1 := "hello";
    return _x.1
  | Bool.true =>
    let _x.2 := 42;
    return _x.2

def describe (x.1 : Bool) (x.2 : lcAny) : String :=
  cases x.1 : String
  | Bool.false =>
    let _x.3 := "str ";
    let _x.4 := String.append _x.3 x.2;
    return _x.4
  | Bool.true =>
    let _x.5 := "nat ";
    let _x.6 := 1;
    let _x.7 := Nat.add x.2 _x.6;
    let _x.8 := Nat.reprFast _x.7;
    let _x.9 := String.append _x.5 _x.8;
    return _x.9
```

- The result of `pickT` has the type `lcAny`. In one branch it is a
  `String`, in the other a `Nat`.
- The parameter `x.2` of `describe` has the type `lcAny`. The `false` branch
  uses it as a `String` (`String.append`). The `true` branch uses it as a
  `Nat` (`Nat.add`).

The program's `L2RBox` enum (shown in [The enum](#the-enum-l2rbox)) is:

```rust
enum L2RBox {
    b0(L2RUnit),      // the unit variant: Lean's box(0)
    b1(LStr),         // a String
    b2(Nat),          // a Nat
    b3(Ref_StdGen),   // a reference cell
    b4(Prod_Box),     // a pair of two boxes
    b5(Prod_Nat)      // a pair of two Nats
}
```

lean2rr generates this code (the string constants are written as
literals):

```rust
fn pickT(b : bool) -> L2RBox {
    if b {
        let n : Nat = l2r_nat_small(42);
        L2RBox::b2{n}
    } else {
        let s : LStr = "hello";
        L2RBox::b1{s}
    }
}

fn describe(b : bool, v : L2RBox) -> LStr {
    if b {
        let one : Nat = l2r_nat_small(1);
        let m : Nat = lean_nat_add(match v {
            L2RBox::b2(n) => { n },
            L2RBox::b0(_) => { zero_Nat() },
            _ => { l2r_unbox_Nat(v) }
        }, one);
        lean_string_append("nat ", l2r_nat_repr(m))
    } else {
        lean_string_append("str ", match v {
            L2RBox::b1(s) => { s },
            L2RBox::b0(_) => { zero_String() },
            _ => { l2r_unreachable<LStr>() }
        })
    }
}
```

- `pickT` returns an `L2RBox`. The `true` branch puts 42 into the `Nat`
  variant `b2`. The `false` branch puts `"hello"` into the `String` variant
  `b1`.
- `describe` takes the value as an `L2RBox` (`v`). The `true` branch
  takes a `Nat` out of the box and adds 1. The `false` branch takes a
  `String` out of the box and appends it.

The `true` branch of `describe` takes the `Nat` out with this `match`:

```rust
match v {
    L2RBox::b2(n) => { n },                  // arm 1
    L2RBox::b0(_) => { zero_Nat() },         // arm 2
    _ => { l2r_unbox_Nat(v) }                // arm 3
}
```

- **Arm 1: the variant `b2`** holds a `Nat`. The arm gives that `Nat`
  (`n`). This is the arm that runs: `pickT true` put 42 into `b2`.
- **Arm 2: the variant `b0`** is Lean's `box(0)` placeholder. Lean's
  library puts it into some positions that the program never reads (for
  example in `Array.modify`). The arm gives the zero of the type `Nat`:

  ```rust
  fn zero_Nat() -> Nat {
      l2r_nat_small(0)
  }
  ```

- **Arm 3: all the other variants** (`b1`, `b3`, `b4`, `b5`). None of them
  holds a `Nat`. The arm calls the general unbox function for `Nat`:

  ```rust
  fn l2r_unbox_Nat(b : L2RBox) -> Nat {
      match b {
          L2RBox::b2(n) => { n },
          L2RBox::b0(_) => { zero_Nat() },
          _ => {
              let released : u64 = l2r_ptr_addr_rec<L2RBox>(b);
              l2r_unreachable<Nat>()
          }
      }
  }
  ```

  For a variant other than `b2` and `b0`, it releases the box with one call
  (`l2r_ptr_addr_rec`), which keeps the code small, and then stops the
  program (`l2r_unreachable`). Lean's type checker makes sure that the
  value in the `true` branch is a `Nat`, so this arm does not run.

The `false` branch uses the same three arms for a `String`: `b1` gives the
`String`, `b0` gives the empty string, and the last arm stops the program
(`l2r_unreachable`) directly.

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

LCNF (mono phase):

```text
def entries : List (Sigma Ty lcAny) :=
  let _x.1 := Ty.nat;
  let _x.2 := 5;
  let _x.3 := Sigma.mk ◾ ◾ _x.1 _x.2;
  let _x.4 := Ty.str;
  let _x.5 := "five";
  let _x.6 := Sigma.mk ◾ ◾ _x.4 _x.5;
  let _x.7 := [] ◾;
  let _x.8 := List.cons ◾ _x.6 _x.7;
  let _x.9 := List.cons ◾ _x.3 _x.8;
  return _x.9
```

- The pair has the type `Sigma Ty lcAny`: the type of the second component
  is not known.
- In `Sigma.mk ◾ ◾ _x.1 _x.2`, the two `◾` are the type arguments. The
  pair does not store them.
- The second component (`5`, `"five"`) is an `L2RBox`.

lean2rr generates this pair type and these two pairs:

```rust
struct Sigma_Ty(L2RBox, Ty)   // the second component, then the first

let p1 : Sigma_Ty = Sigma_Ty{L2RBox::b2{l2r_nat_small(5)}, Ty::c_nat{}};   // ⟨.nat, 5⟩
let p2 : Sigma_Ty = Sigma_Ty{L2RBox::b1{"five"}, Ty::c_str{}};             // ⟨.str, "five"⟩
```

- The first component is a `Ty`.
- The second component is an `L2RBox`: `5` is in the `Nat` variant, and
  `"five"` is in the `String` variant.

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

In Rust terms, a `Pkg` is similar to a `Box<dyn Display>`. A function that
uses a package:

```lean
def Pkg.show (p : Pkg) : String := p.fmt p.val
```

LCNF (mono phase):

```text
def Pkg.show (p : Pkg) : String :=
  cases p : String
  | Pkg.mk (α : lcErased) (val : lcAny) (fmt : lcAny → String) =>
    let _x.1 := fmt val;
    return _x.1
```

- The field `α` is `lcErased`. It has no storage.
- The field `val` is `lcAny`. It is an `L2RBox`.
- The field `fmt` takes an `lcAny`. It takes an `L2RBox`.

lean2rr generates this code:

```rust
struct Pkg(L2RBox, Fn_Box_Str)        // val, fmt; α has no field

enum Fn_Box_Str {                     // a function value: L2RBox -> LStr
    z,
    raw(L2RBox -> LStr),
    wrap_ProdBox(Fn_ProdBox_Str),     // wraps a Prod_Box -> LStr function
    wrap_ProdNat(Fn_ProdNat_Str),     // wraps a Prod_Nat -> LStr function
    wrap_Nat(Fn_Nat_Str)              // wraps a Nat -> LStr function
}

fn Pkg_show(p : Pkg) -> LStr {
    let val : L2RBox = p.0;
    let fmt : Fn_Box_Str = p.1;
    apply_Fn_Box_Str(fmt, val)
}
```

- A `Pkg` has two fields: `val` is an `L2RBox`, and `fmt` is a function
  value that takes an `L2RBox`.
- The program builds `⟨Nat, 5, toString⟩`. `toString` at `Nat` takes a
  `Nat`, so lean2rr stores it in the variant `wrap_Nat`. A call through
  that variant takes the `Nat` out of the box, then calls `toString`.
- `Pkg_show` reads the two fields and applies `fmt` to `val`
  (`apply_Fn_Box_Str`).

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

LCNF (mono phase), the part that recurses:

```text
def nest._redArg (inst.1 : lcAny → String) (x.2 : Nat) (x.3 : lcAny) : String :=
  let _f.4 := instToStringProd._redArg._lam_0 inst.1 inst.1;
  ...
  let _x.7 := Prod.mk ◾ ◾ x.3 x.3;
  let _x.8 := nest._redArg _f.4 n.6 _x.7;
  ...
```

- `x.3` has the type `lcAny`, and the `ToString` dictionary `inst.1` takes
  an `lcAny`.
- The recursive call passes the pair `Prod.mk ◾ ◾ x.3 x.3`.

The types grow without end: `Nat`, `Nat × Nat`, and so on. lean2rr compiles
one copy of `nest` for these calls. In that copy, `x` is an `L2RBox`, and
the `ToString` dictionary is a value that the copy receives:

```rust
fn nest_Box(inst : Fn_Box_Str, n : Nat, x : L2RBox) -> LStr {
    let instPair : Fn_ProdBox_Str = Fn_ProdBox_Str::toStringPair{inst, inst};
    if lean_nat_dec_eq(n, l2r_nat_small(0)) {
        apply_Fn_Box_Str(inst, x)
    } else {
        let n1 : Nat = lean_nat_sub(n, l2r_nat_small(1));
        let pair : Prod_Box = Prod_Box{x, x};
        nest_Box(wrap_ProdBox_as_Box(instPair), n1, L2RBox::b4{pair})
    }
}
```

- `x` is an `L2RBox`. `inst` is the `ToString` dictionary: a function value
  that takes an `L2RBox`.
- At count 0, the copy applies the dictionary to `x`.
- Else it builds the pair `(x, x)` as a `Prod_Box` (two boxes), puts the
  pair into the variant `b4`, and calls itself. The dictionary for the pair
  is wrapped (`wrap_ProdBox_as_Box`) so that it also takes an `L2RBox`.

### A partial application that leaves a type open

```lean
structure Op where
  run : {α : Type} → List α → Nat

def ops : List Op := [⟨List.length⟩, ⟨fun xs => xs.length * 2⟩]
```

- Line 2: the field `run` is a function that takes a list of any element
  type.
- Line 4: `ops` holds two such functions.

LCNF (mono phase):

```text
def ops._lam_0 (α.1 : lcErased) (xs : List lcAny) : Nat :=
  let _x.2 := List.lengthTR._redArg xs;
  let _x.3 := 2;
  let _x.4 := Nat.mul _x.2 _x.3;
  return _x.4

def ops : List ({α : lcErased} → List lcAny → Nat) :=
  ...
```

- The field's function type is `{α : lcErased} → List lcAny → Nat`: the
  type argument is erased, and the list holds values of an unknown type.

The function in the field takes a list whose elements are `L2RBox`
values:

```rust
enum List_Box {                  // List lcAny
    c_nil,
    c_cons(L2RBox, List_Box)
}

fn ops_lam(α : L2RUnit, xs : List_Box) -> Nat {
    let len : Nat = List_length_Box(xs);
    lean_nat_mul(len, l2r_nat_small(2))
}
```

- `α` is the erased type argument: an `L2RUnit`, which holds no data.
- `xs` is the list: each cell holds an `L2RBox` and the rest of the list.
- The function counts the cells and multiplies by 2.

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

lean2rr generates two tree types and a conversion call:

```rust
enum Tree_Nat {                   // Tree Nat: the layout that build uses
    c_leaf(Nat),
    c_node(Tree_Nat, Tree_Nat)
}
enum Tree_Box {                   // Tree lcAny: the layout that leftDepth uses
    c_leaf(L2RBox),
    c_node(Tree_Box, Tree_Box)
}

// in main:
let t : Tree_Nat = build(n);
let depth : Nat = leftDepth(conv_Tree_Nat_to_Tree_Box(t));
```

- `build n` has n + 1 nodes. Each node points two times to the same child.
- `conv_Tree_Nat_to_Tree_Box` makes a `Tree lcAny` with the same
  shape: each leaf's `Nat` goes into `L2RBox::b2`. It follows each pointer
  separately, so it makes 2<sup>n+1</sup> − 1 nodes.

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
