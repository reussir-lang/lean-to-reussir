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

All the Lean code on this page is one program. It type-checks, and its
lean2rr build gives the same output as its native build. The LCNF on this
page is the output of Lean's compiler for that program (mono phase, with
the types of parameters and `let` values). The Reussir code is the output
of lean2rr for that program (`--keep-rr`), with shorter, readable names.

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
@[noinline] def pick (α : Type) (b : Bool) (x y : α) : α := if b then x else y
```

- `pick` takes a type `α`, a Boolean `b`, and two values `x` and `y` of the
  type `α`. It returns `x` if `b` is true, else `y`.
- `@[noinline]` keeps `pick` a separate function in the output.

LCNF:

```text
def pick._redArg (b : Bool) (x : lcAny) (y : lcAny) : lcAny :=
  cases b : lcAny
  | Bool.false =>
    return y
  | Bool.true =>
    return x
```

- `_redArg` is the copy of `pick` without the parameter `α`. The parameter
  is `lcErased`, so Lean's compiler removes it.
- `x`, `y` and the result have the type `lcAny`. Each one holds data.
- `cases b : lcAny` is a match on `b`. In LCNF, the type after the colon is
  the type of the result of the whole match, not the type of `b`.

lean2rr makes a copy of `pick` for each type argument that the program
uses. The program calls `pick Nat`. lean2rr generates this copy:

```rust
fn pick_Nat(b : bool, x : Nat, y : Nat) -> Nat {
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

For the program on this page, lean2rr generates this enum:

```rust
enum L2RBox {
    b0(L2RUnit),      // the unit variant: Lean's box(0)
    b1(Ref_StdGen),   // a reference cell (IO.stdGenRef, made at startup)
    b2(Nat),          // a Nat
    b3(LStr),         // a String
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
    L2RBox::b3(s) => { s },                  // the String variant
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
@[noinline] def Column.push (c : Column) (i : Nat) : Column :=
  match c with
  | ⟨.nat, d⟩ => ⟨.nat, d.push i⟩
  | ⟨.str, d⟩ => ⟨.str, d.push (toString i)⟩
```

- Line 1: `push` takes a column `c` and a number `i`, and returns a column.
- Line 3: if `ty` is `.nat`, then `d` is an `Array Nat`. `push` adds `i`.
- Line 4: if `ty` is `.str`, then `d` is an `Array String`. `push` adds
  `i` as a string.

LCNF:

```text
def Column.push (c : Column) (i : Nat) : Column :=
  cases c : Column
  | Column.mk (ty.1 : Ty) (data.2 : Array lcAny) =>
    cases ty.1 : Column
    | Ty.nat =>
      let _x.3 : Array Nat := Array.push ◾ data.2 i;
      let _x.4 : Column := mk ty.1 _x.3;
      return _x.4
    | Ty.str =>
      let _x.5 : String := Nat.reprFast i;
      let _x.6 : Array String := Array.push ◾ data.2 _x.5;
      let _x.7 : Column := mk ty.1 _x.6;
      return _x.7
```

- `cases ty.1 : Column` is a match on `ty.1`, a `Ty`. Each branch returns a
  column.
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
            let data2 : RVec<L2RBox> = lean_array_push<L2RBox>(data, L2RBox::b3{s});
            Column{data2, Ty::c_str{}}
        }
    }
}
```

- `data` is an `RVec<L2RBox>`: an array of boxes.
- `push` puts the new element into its variant: `b2` for a `Nat`, `b3` for
  a `String`. It changes the array in place when the array is unique.
- `ty` is a `[value]` enum, so a `Column` is one cell, plus its array.
  Each branch writes the tag again (`Ty::c_nat{}`), where LCNF reuses
  `ty.1`: a `[value]` enum costs nothing to build.

### A type selected by a Boolean

```lean
@[noinline] def pickT (b : Bool) : if b then Nat else String :=
  match b with
  | true => (42 : Nat)
  | false => "hello"

@[noinline] def describe : (b : Bool) → (if b then Nat else String) → String
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

LCNF:

```text
def pickT (b : Bool) : lcAny :=
  cases b : lcAny
  | Bool.false =>
    let _x.1 : String := "hello";
    return _x.1
  | Bool.true =>
    let _x.2 : Nat := 42;
    return _x.2

def describe (x.1 : Bool) (x.2 : lcAny) : String :=
  cases x.1 : String
  | Bool.false =>
    let _x.3 : String := "str ";
    let _x.4 : String := String.append _x.3 x.2;
    return _x.4
  | Bool.true =>
    let _x.5 : String := "nat ";
    let _x.6 : Nat := 1;
    let _x.7 : Nat := Nat.add x.2 _x.6;
    let _x.8 : String := Nat.reprFast _x.7;
    let _x.9 : String := String.append _x.5 _x.8;
    return _x.9
```

- The result of `pickT` has the type `lcAny`. In one branch it is a
  `String`, in the other a `Nat`.
- The parameter `x.2` of `describe` has the type `lcAny`. The `false` branch
  uses it as a `String` (`String.append`). The `true` branch uses it as a
  `Nat` (`Nat.add`).

The program's enum, from [The enum](#the-enum-l2rbox):

```rust
enum L2RBox {
    b0(L2RUnit),      // the unit variant: Lean's box(0)
    b1(Ref_StdGen),   // a reference cell
    b2(Nat),          // a Nat
    b3(LStr),         // a String
    b4(Prod_Box),     // a pair of two boxes
    b5(Prod_Nat)      // a pair of two Nats
}
```

lean2rr generates this code:

```rust
fn pickT(b : bool) -> L2RBox {
    if b {
        let n : Nat = l2r_nat_small(42);
        L2RBox::b2{n}
    } else {
        let s : LStr = hello();          // the constant "hello", made once
        L2RBox::b3{s}
    }
}

fn describe(b : bool, v : L2RBox) -> LStr {
    if b {
        let prefix : LStr = nat_prefix();    // the constant "nat "
        let one : Nat = l2r_nat_small(1);
        let m : Nat = lean_nat_add(match v {
            L2RBox::b2(n) => { n },
            L2RBox::b0(_) => { zero_Nat() },
            _ => { l2r_unbox_Nat(v) }
        }, one);
        let digits : LStr = l2r_nat_repr(m);
        lean_string_append(prefix, digits)
    } else {
        let prefix : LStr = str_prefix();    // the constant "str "
        lean_string_append(prefix, match v {
            L2RBox::b3(s) => { s },
            L2RBox::b0(_) => { zero_String() },
            _ => { l2r_unreachable<LStr>() }
        })
    }
}
```

- `pickT` returns an `L2RBox`. The `true` branch puts 42 into the `Nat`
  variant `b2`. The `false` branch puts `"hello"` into the `String` variant
  `b3`.
- `describe` takes the value as an `L2RBox` (`v`). The `true` branch takes
  a `Nat` out of the box and adds 1. The `false` branch takes a `String` out
  of the box and appends it.
- A string constant (`"hello"`, `"nat "`, `"str "`) is made once and kept;
  each use reads it.

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
- **Arm 2: the variant `b0`** is Lean's `box(0)`. lean2rr adds this arm to
  each unbox, because Lean's library can write `box(0)` as a temporary
  value into a slot of any type (`Array.modify`). Here no `box(0)` can
  arrive: the value comes from `pickT`. The arm gives `0`, the value that
  `box(0)` has as a `Nat` in a native build:

  ```rust
  fn zero_Nat() -> Nat {
      l2r_nat_small(0)
  }
  ```

- **Arm 3: all the other variants** (`b1`, `b3`, `b4`, `b5`). A `match` must
  cover each variant. None of these holds a `Nat`. The arm calls the general
  unbox function for `Nat`:

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

  In a program that casts, this function has more arms: a value of another
  word type can be read as a `Nat` through `unsafeCast`. In this program it
  has none. For the other variants, it releases the box with one call
  (`l2r_ptr_addr_rec`) and stops the program (`l2r_unreachable`). Lean's
  type checker makes sure that the value is a `Nat`, so this arm does not
  run.

The `false` branch uses the same three arms for a `String`: `b3` gives the
`String`, `b0` gives the empty string, and the last arm stops the program
(`l2r_unreachable`) directly, because no other type is read as a `String`.

### Sigma types

A Sigma type `(x : A) × B x` is a pair. The type of its second component
depends on the value of its first component.

```lean
@[noinline] def entries (n : Nat) : List ((t : Ty) × t.denote) :=
  [⟨.nat, n⟩, ⟨.str, toString n⟩]
```

- Line 1: `entries` takes a number `n` and returns a list of pairs. In each
  pair, the second component has the type `t.denote`, where `t` is the
  first component.
- Line 2: the first pair holds `.nat` and the number `n`. The second pair
  holds `.str` and `n` as a string.

LCNF:

```text
def entries (n : Nat) : List (Sigma Ty lcAny) :=
  let _x.1 : Ty := Ty.nat;
  let _x.2 : Sigma Ty lcAny := Sigma.mk ◾ ◾ _x.1 n;
  let _x.3 : Ty := Ty.str;
  let _x.4 : String := Nat.reprFast n;
  let _x.5 : Sigma Ty lcAny := Sigma.mk ◾ ◾ _x.3 _x.4;
  let _x.6 : List (Sigma Ty lcAny) := [] ◾;
  let _x.7 : List (Sigma Ty lcAny) := List.cons ◾ _x.5 _x.6;
  let _x.8 : List (Sigma Ty lcAny) := List.cons ◾ _x.2 _x.7;
  return _x.8
```

- A pair has the type `Sigma Ty lcAny`: the type of the second component is
  not known.
- `Sigma.mk ◾ ◾ fst snd`: the two `◾` are the type arguments. The pair
  does not store them.

lean2rr generates this code:

```rust
struct Sigma_Ty(L2RBox, Ty)                  // snd, then fst
enum List_Sigma_Ty { c_nil, c_cons(Sigma_Ty, List_Sigma_Ty) }

fn entries(n : Nat) -> List_Sigma_Ty {
    let t1 : Ty = Ty::c_nat{};
    let p1 : Sigma_Ty = Sigma_Ty{L2RBox::b2{n}, t1};     // ⟨.nat, n⟩
    let t2 : Ty = Ty::c_str{};
    let s : LStr = l2r_nat_repr(n);
    let p2 : Sigma_Ty = Sigma_Ty{L2RBox::b3{s}, t2};     // ⟨.str, toString n⟩
    let nil : List_Sigma_Ty = List_Sigma_Ty::c_nil{};
    let l2 : List_Sigma_Ty = List_Sigma_Ty::c_cons{p2, nil};
    List_Sigma_Ty::c_cons{p1, l2}
}
```

- The code follows the LCNF line by line: two pairs, then the list.
- The second component of a pair is an `L2RBox`: `n` goes into the `Nat`
  variant `b2`, and the string goes into the `String` variant `b3`.
- In `Sigma_Ty`, the second component comes first. lean2rr sorts the
  fields of a structure by size, largest first (pass `field-order`): the
  8-byte box comes before the 1-byte `Ty`.

### A type stored in a field

```lean
structure Pkg where
  α : Type
  val : α
  fmt : α → String

@[noinline] def Pkg.show (p : Pkg) : String := p.fmt p.val
```

- Line 2: the field `α` is a type. lean2rr does not store it.
- Line 3: the field `val` is a value of the type `α`.
- Line 4: the field `fmt` is a function that turns an `α` into a string.
- Line 6: `Pkg.show` applies `fmt` to `val`.

In Rust terms, a `Pkg` is similar to a `Box<dyn Display>`.

LCNF:

```text
def Pkg.show (p : Pkg) : String :=
  cases p : String
  | Pkg.mk (α : lcErased) (val : lcAny) (fmt : lcAny → String) =>
    let _x.1 : String := fmt val;
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
  (`apply_Fn_Box_Str`), as the LCNF does (`fmt val`).

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

LCNF:

```text
def nest._redArg (inst.1 : lcAny → String) (x.2 : Nat) (x.3 : lcAny) : String :=
  let _f.4 : Prod lcAny lcAny → String := instToStringProd._redArg._lam_0 inst.1 inst.1;
  let zero : Nat := 0;
  let isZero : Bool := Nat.decEq x.2 zero;
  cases isZero : String
  | Bool.true =>
    let _x.5 : String := inst.1 x.3;
    return _x.5
  | Bool.false =>
    let one : Nat := 1;
    let n.6 : Nat := Nat.sub x.2 one;
    let _x.7 : Prod lcAny lcAny := Prod.mk ◾ ◾ x.3 x.3;
    let _x.8 : String := nest._redArg _f.4 n.6 _x.7;
    return _x.8
```

- `x.3` has the type `lcAny`, and the `ToString` dictionary `inst.1` takes
  an `lcAny`.
- `_f.4` is the `ToString` dictionary for pairs, built from `inst.1`.
- The recursive call passes the pair `Prod.mk ◾ ◾ x.3 x.3` and `_f.4`.

The types grow without end: `Nat`, `Nat × Nat`, and so on. lean2rr compiles
one copy of `nest` for these calls. In that copy, `x` is an `L2RBox`, and
the `ToString` dictionary is a value that the copy receives:

```rust
fn nest_Box(inst : Fn_Box_Str, n : Nat, x : L2RBox) -> LStr {
    let instPair : Fn_ProdBox_Str = Fn_ProdBox_Str::toStringPair{inst, inst};
    let zero : Nat = l2r_nat_small(0);
    let isZero : bool = lean_nat_dec_eq(n, zero);
    if isZero {
        apply_Fn_Box_Str(inst, x)
    } else {
        let one : Nat = l2r_nat_small(1);
        let n1 : Nat = lean_nat_sub(n, one);
        let pair : Prod_Box = Prod_Box{x, x};
        nest_Box(wrap_ProdBox_as_Box(instPair), n1, L2RBox::b4{pair})
    }
}
```

- `instPair` is `_f.4`: the dictionary for pairs.
- At count 0, the copy applies `inst` to `x`.
- Else it builds the pair `(x, x)` as a `Prod_Box` (two boxes), puts the
  pair into the variant `b4`, and calls itself. `instPair` takes a
  `Prod_Box`, and the copy needs a dictionary that takes an `L2RBox`, so
  lean2rr wraps it (`wrap_ProdBox_as_Box`).

### A partial application that leaves a type open

```lean
structure Op where
  run : {α : Type} → List α → Nat

def ops : List Op := [⟨List.length⟩, ⟨fun xs => xs.length * 2⟩]
```

- Line 2: the field `run` is a function that takes a list of any element
  type.
- Line 4: `ops` holds two such functions.

LCNF of the second function:

```text
def ops._lam_0 (α.1 : lcErased) (xs : List lcAny) : Nat :=
  let _x.2 : Nat := List.lengthTR._redArg xs;
  let _x.3 : Nat := 2;
  let _x.4 : Nat := Nat.mul _x.2 _x.3;
  return _x.4
```

- The type argument `α.1` is `lcErased`. The list holds values of an
  unknown type: `List lcAny`.

lean2rr generates this code:

```rust
enum List_Box {                  // List lcAny
    c_nil,
    c_cons(L2RBox, List_Box)
}

fn ops_lam(α : L2RUnit, xs : List_Box) -> Nat {
    let len : Nat = List_length_Box(xs);
    let two : Nat = l2r_nat_small(2);
    lean_nat_mul(len, two)
}
```

- `α` is the erased type argument: an `L2RUnit`, which holds no data. The
  function keeps the parameter (rule 4).
- `xs` is the list: each cell holds an `L2RBox` and the rest of the list.
- The function counts the cells and multiplies by 2.

## The current version

The current version gives a generic type one layout for each type
argument. A `Tree Float` leaf holds the `f64`, and a `Tree Nat` leaf holds
the `Nat` word. The unknown case, `Tree lcAny`, has another layout, whose
leaf holds an `L2RBox`. When a value goes from one layout to another, the
current version rebuilds it, node by node:

```lean
inductive Tree (α : Type) where
  | leaf (x : α)
  | node (left right : Tree α)

@[noinline] def build : Nat → Tree Nat
  | 0 => .leaf 7
  | n + 1 => let t := build n; .node t t   -- both children are the same t

structure Packed where                      -- a tree whose element type is a field
  α : Type
  tree : Tree α

@[noinline] def leftDepth (p : Packed) : Nat := go p.tree
where
  go {α : Type} : Tree α → Nat
    | .leaf _ => 0
    | .node l _ => 1 + go l
```

- `build n` returns a `Tree Nat` with n + 1 nodes. Each node points two
  times to the same child.
- `Packed` holds a type and a tree of that type. `leftDepth` counts the
  nodes on the leftmost path.
- The program's `main` (see [The program's main](#the-programs-main))
  calls `leftDepth ⟨Nat, build n⟩`: it packs a `Tree Nat` with
  `α := Nat`.

LCNF:

```text
def build (x.1 : Nat) : Tree Nat :=
  ...
  let t : Tree Nat := build n.4;
  let _x.5 : Tree Nat := @Tree.node ◾ t t;
  return _x.5

def leftDepth (p : Tree lcAny) : Nat :=
  let _x.1 : Nat := leftDepth.go._redArg p;
  return _x.1
```

- `build` returns a `Tree Nat`. `leftDepth` takes a `Tree lcAny`: Lean's
  compiler stores a `Packed` as its one data field, the tree.
- In a native build, `Tree Nat` and `Tree lcAny` have the same layout, so
  `main` passes the tree as it is.

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

- `conv_Tree_Nat_to_Tree_Box` makes a `Tree lcAny` with the same shape:
  each leaf's `Nat` goes into `L2RBox::b2`. It follows each pointer
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

## The program's main

The program's `main` calls each example:

```lean
def main (args : List String) : IO Unit := do
  let b := args.length == 0
  let n := args.length + 3
  IO.println (pick Nat b 1 2)
  let c := Column.push ⟨.nat, #[]⟩ n
  IO.println c.data.size
  IO.println (describe b (pickT b))
  IO.println (entries n).length
  IO.println (Pkg.show ⟨Nat, 5, toString⟩)
  IO.println (nest 2 n)
  IO.println (ops.map (fun o => o.run [1, 2, 3]))
  IO.println (leftDepth ⟨Nat, build n⟩)
```

Without arguments, the native build and the lean2rr build both print:

```text
1
1
nat 43
2
5
((3, 3), (3, 3))
[3, 6]
3
```
