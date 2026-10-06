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
of lean2rr for that program (`--keep-rr`), with shorter, readable names and
without `lcErased` (rule 4 of
[Layouts of generic types](#layouts-of-generic-types)).

## Types and values

Lean's compiler translates a program to LCNF, its intermediate code. In
LCNF, it replaces two kinds of items:

- **`◾`** replaces an item without data: a type, a type argument or a proof.
  In a type, LCNF writes it as `lcErased`. It carries no information, and
  lean2rr does not need it: the Reussir code has no field, no parameter
  and no argument for it.
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
- one unit variant (`b0`), for the unit value `()` and Lean's `box(0)`.

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

The payload types:

```rust
struct Ref_StdGen(Cell<StdGen>)       // IO.Ref StdGen: a reference cell
struct Prod_Box(L2RBox, L2RBox)       // Prod lcAny lcAny
struct Prod_Nat(Nat, Nat)             // Prod Nat Nat
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
4. **`lcErased` is removed.** It carries no information, and lean2rr does
   not need it. No function, function type or call has an `lcErased`
   parameter or argument. A function whose parameters are all `lcErased`
   keeps one unit parameter, so that it stays a function.
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

Status: rules 1 and 4 are planned. Today a generic type has one layout for
each type argument, and the enum has one variant for each such layout (see
[The current version](#the-current-version)). Today a function value keeps
its erased parameters, as in LCNF.

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
- A string constant (`"hello"`, `"nat "`, `"str "`) is made once and kept
  in a once-cell; each use reads it. The constant `"hello"`:

```rust
fn hello_init() -> LStr {
    l2r_str_lit(28)                 // literal number 28 of the program: "hello"
}

fn hello() -> LStr {
    let r : u64 = if l2r_once_ready(35) { 0 } else {
        if l2r_once_claim(35) { 0 } else { l2r_once_put<LStr>(35, hello_init()) }
    };
    l2r_once_get<LStr>(35)
}
```

`nat_prefix` and `str_prefix` are the same, with other slots.

The `true` branch of `describe` takes the `Nat` out with this `match`:

```rust
match v {
    L2RBox::b2(n) => { n },                  // arm 1
    L2RBox::b0(_) => { zero_Nat() },         // arm 2
    _ => { l2r_unbox_Nat(v) }                // arm 3
}
```

- **Arm 1: the variant `b2`** holds a `Nat`. The arm gives that `Nat`.
- **Arm 2: the variant `b0`** is Lean's `box(0)`. It is reached only with
  `unsafeCast`. The arm gives `0`, as in a native build:

```rust
fn zero_Nat() -> Nat {
    l2r_nat_small(0)
}
```

- **Arm 3: all the other variants.** The arm calls the general unbox
  function for `Nat`:

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


The `false` branch does the same for a `String`. Its `b0` arm gives the
empty string, a constant:

```rust
fn zero_String_init() -> LStr { l2r_str_lit(0) }   // literal number 0: ""

fn zero_String() -> LStr {
    let r : u64 = if l2r_once_ready(38) { 0 } else {
        if l2r_once_claim(38) { 0 } else { l2r_once_put<LStr>(38, zero_String_init()) }
    };
    l2r_once_get<LStr>(38)
}
```

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
- `Pkg_show` reads the two fields and applies `fmt` to `val`, as the LCNF
  does (`fmt val`).

`main` builds the package `⟨Nat, 5, toString⟩`. LCNF (part of `main`):

```text
let _f.29 : Nat → String := Nat.reprFast;
let _x.30 : Nat := 5;
let _x.31 : Pkg := Pkg.mk ◾ _x.30 _f.29;
let _x.32 : String := Pkg.show _x.31;
```

lean2rr generates this code:

```rust
enum Fn_Nat_Str {                     // a function value: Nat -> LStr
    z,
    raw(Nat -> LStr),
    reprFast                          // the function Nat.reprFast
}

let f : Fn_Nat_Str = Fn_Nat_Str::reprFast{};
let five : Nat = l2r_nat_small(5);
let p : Pkg = Pkg{L2RBox::b2{five}, Fn_Box_Str::wrap_Nat{f}};
let s : LStr = Pkg_show(p);
```

- `Pkg.mk ◾ _x.30 _f.29`: the `◾` is the type `Nat`. It has no field.
- `5` goes into the `Nat` variant `b2`.
- `Nat.reprFast` takes a `Nat`, not an `L2RBox`, so lean2rr puts it into the
  variant `wrap_Nat`.

`apply_Fn_Box_Str` applies a function value of the type
`Fn_Box_Str`:

```rust
fn apply_Fn_Box_Str(f : Fn_Box_Str, x : L2RBox) -> LStr {
    match f {
        Fn_Box_Str::z => { zero_String() },
        Fn_Box_Str::raw(c) => { c(x) },
        Fn_Box_Str::wrap_ProdBox(g) => { apply_Fn_ProdBox_Str(g, unbox_Prod_Box(x)) },
        Fn_Box_Str::wrap_ProdNat(g) => { apply_Fn_ProdNat_Str(g, unbox_Prod_Nat(x)) },
        Fn_Box_Str::wrap_Nat(g) => { apply_Fn_Nat_Str(g, match x {
            L2RBox::b2(n) => { n },
            L2RBox::b0(_) => { zero_Nat() },
            _ => { l2r_unbox_Nat(x) }
        }) }
    }
}

fn apply_Fn_Nat_Str(f : Fn_Nat_Str, n : Nat) -> LStr {
    match f {
        Fn_Nat_Str::z => { zero_String() },
        Fn_Nat_Str::raw(c) => { c(n) },
        Fn_Nat_Str::reprFast => { Nat_reprFast(n) }
    }
}
```

- `z` is the placeholder function. It gives the zero of the result.
- `raw` holds a closure.
- Each `wrap_…` variant holds a function that takes another type. The call
  takes the value out of the box at that type, then calls the function.
  For `Pkg.show ⟨Nat, 5, toString⟩`, the call goes through `wrap_Nat`, then
  `reprFast`.

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
  lean2rr wraps it.

The dictionary for pairs, and its wrapper:

```rust
enum Fn_ProdBox_Str {                 // a function value: Prod_Box -> LStr
    z,
    raw(Prod_Box -> LStr),
    toStringPair(Fn_Box_Str, Fn_Box_Str)  // ToString (α × β), from the two dictionaries
}

fn wrap_ProdBox_as_Box(f : Fn_ProdBox_Str) -> Fn_Box_Str {
    Fn_Box_Str::wrap_ProdBox{f}
}

fn toStringPair(fa : Fn_Box_Str, fb : Fn_Box_Str, p : Prod_Box) -> LStr {
    let a : L2RBox = p.0;
    let b : L2RBox = p.1;
    let open : LStr = open_paren();              // the constant "("
    let sa : LStr = apply_Fn_Box_Str(fa, a);
    let s1 : LStr = lean_string_append(open, sa);
    let sep : LStr = comma();                    // the constant ", "
    let s2 : LStr = lean_string_append(s1, sep);
    let sb : LStr = apply_Fn_Box_Str(fb, b);
    let s3 : LStr = lean_string_append(s2, sb);
    let close : LStr = close_paren();            // the constant ")"
    lean_string_append(s3, close)
}
```

- A call through `wrap_ProdBox` takes the `Prod_Box` out of the box
  (`b4`), then calls `toStringPair`.

The program calls `nest 2 n` with `n : Nat`. lean2rr makes a copy of `nest`
at `Nat` for this call. It makes the first pair, then calls the copy at
`L2RBox`:

```rust
fn nest_Nat(n : Nat, x : Nat) -> LStr {
    let zero : Nat = l2r_nat_small(0);
    let isZero : bool = lean_nat_dec_eq(n, zero);
    if isZero {
        l2r_nat_repr(x)
    } else {
        let instPair : Fn_ProdNat_Str = Fn_ProdNat_Str::toStringPairNat{};
        let one : Nat = l2r_nat_small(1);
        let n1 : Nat = lean_nat_sub(n, one);
        let pair : Prod_Nat = Prod_Nat{x, x};
        nest_Box(wrap_ProdNat_as_Box(instPair), n1, L2RBox::b5{pair})
    }
}
```

- The first pair is a `Prod_Nat` (two `Nat`s), in the variant `b5`.
- `nest_Box` makes the next pairs as `Prod_Box` values (`b4`).
- `unbox_Prod_Box` accepts both layouts. It converts a `Prod_Nat` to a
  `Prod_Box`:

```rust
fn unbox_Prod_Box(b : L2RBox) -> Prod_Box {
    match b {
        L2RBox::b4(p) => { p },
        L2RBox::b5(p) => { conv_Prod_Nat_to_Prod_Box(p) },
        L2RBox::b0(_) => { zero_Prod_Box() },
        _ => {
            let released : u64 = l2r_ptr_addr_rec<L2RBox>(b);
            l2r_unreachable<Prod_Box>()
        }
    }
}
```

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

fn ops_lam(xs : List_Box) -> Nat {
    let len : Nat = List_length_Box(xs);
    let two : Nat = l2r_nat_small(2);
    lean_nat_mul(len, two)
}
```

- The type argument `α.1` is `lcErased`. `ops_lam` has no parameter for
  it.
- `xs` is the list: each cell holds an `L2RBox` and the rest of the list.
- The function counts the cells and multiplies by 2:

```rust
fn List_length_Box(xs : List_Box) -> Nat {
    let zero : Nat = l2r_nat_small(0);
    List_length_aux_Box(xs, zero)
}

fn List_length_aux_Box(xs : List_Box, acc : Nat) -> Nat {
    match xs {
        List_Box::c_nil => { acc },
        List_Box::c_cons(h, t) => {
            let one : Nat = l2r_nat_small(1);
            let acc1 : Nat = lean_nat_add(acc, one);
            List_length_aux_Box(t, acc1)
        }
    }
}
```

The list `ops`. LCNF:

```text
def ops : List ({α : lcErased} → List lcAny → Nat) :=
  let _f.1 : lcErased → List lcAny → Nat := ops._lam_0;
  let _x.2 : {α : lcErased} → List lcAny → Nat := List.lengthTR;
  let _x.3 : List ({α : lcErased} → List lcAny → Nat) := [] ◾;
  let _x.4 : List ({α : lcErased} → List lcAny → Nat) := List.cons ◾ _f.1 _x.3;
  let _x.5 : List ({α : lcErased} → List lcAny → Nat) := List.cons ◾ _x.2 _x.4;
  return _x.5
```

lean2rr generates this code:

```rust
enum Fn_Op {                          // a function value: List_Box -> Nat
    z,
    raw(List_Box -> Nat),
    ops_lam,                          // the function ops_lam
    List_length                       // the function List.lengthTR
}
enum List_Fn_Op { c_nil, c_cons(Fn_Op, List_Fn_Op) }

fn ops_tail() -> List_Fn_Op {             // the constant [ops_lam]
    let nil : List_Fn_Op = List_Fn_Op::c_nil{};
    let f : Fn_Op = Fn_Op::ops_lam{};
    List_Fn_Op::c_cons{f, nil}
}

fn ops_init() -> List_Fn_Op {
    let tail : List_Fn_Op = ops_tail();
    let g : Fn_Op = Fn_Op::List_length{};
    List_Fn_Op::c_cons{g, tail}
}
```

- `ops` is a constant: lean2rr computes `ops_init()` once and keeps the
  list in a once-cell. Lean's compiler also makes the tail `[ops_lam]` a
  constant of its own (`ops_tail`).
- Each element is a function value. It names the function; it allocates
  nothing.

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
  let zero : Nat := 0;
  let isZero : Bool := Nat.decEq x.1 zero;
  cases isZero : Tree Nat
  | Bool.true =>
    let _x.2 : Nat := 7;
    let _x.3 : Tree Nat := @Tree.leaf ◾ _x.2;
    return _x.3
  | Bool.false =>
    let one : Nat := 1;
    let n.4 : Nat := Nat.sub x.1 one;
    let t : Tree Nat := build n.4;
    let _x.5 : Tree Nat := @Tree.node ◾ t t;
    return _x.5

def leftDepth.go._redArg (a.1 : Tree lcAny) : Nat :=
  cases a.1 : Nat
  | Tree.leaf (x.2 : lcAny) =>
    let _x.3 : Nat := 0;
    return _x.3
  | Tree.node (left.4 : Tree lcAny) (right.5 : Tree lcAny) =>
    let _x.6 : Nat := 1;
    let _x.7 : Nat := leftDepth.go._redArg left.4;
    let _x.8 : Nat := Nat.add _x.6 _x.7;
    return _x.8

def leftDepth (p : Tree lcAny) : Nat :=
  let _x.1 : Nat := leftDepth.go._redArg p;
  return _x.1
```

The call in `main`:

```text
let _x.46 : Tree Nat := build n;
let _x.47 : Nat := leftDepth _x.46;
```

- `build` returns a `Tree Nat`. `leftDepth` takes a `Tree lcAny`: Lean's
  compiler stores a `Packed` as its one data field, the tree.
- `main` passes the `Tree Nat` to `leftDepth`. In a native build, `Tree Nat`
  and `Tree lcAny` have the same layout, so the tree goes as it is.

lean2rr generates two tree types:

```rust
enum Tree_Nat {                   // Tree Nat: the layout that build uses
    c_leaf(Nat),
    c_node(Tree_Nat, Tree_Nat)
}
enum Tree_Box {                   // Tree lcAny: the layout that leftDepth uses
    c_leaf(L2RBox),
    c_node(Tree_Box, Tree_Box)
}
```

The functions:

```rust
fn leaf7_init() -> Tree_Nat {             // the constant .leaf 7
    let seven : Nat = l2r_nat_small(7);
    Tree_Nat::c_leaf{seven}
}

fn build(n : Nat) -> Tree_Nat {
    let zero : Nat = l2r_nat_small(0);
    let isZero : bool = lean_nat_dec_eq(n, zero);
    if isZero {
        leaf7()                           // reads the constant from its once-cell
    } else {
        let one : Nat = l2r_nat_small(1);
        let n1 : Nat = lean_nat_sub(n, one);
        let t : Tree_Nat = build(n1);
        Tree_Nat::c_node{t, t}            // both children are the same t
    }
}

fn leftDepth_go(t : Tree_Box) -> Nat {
    match t {
        Tree_Box::c_leaf(x) => { l2r_nat_small(0) },
        Tree_Box::c_node(l, r) => {
            let one : Nat = l2r_nat_small(1);
            let d : Nat = leftDepth_go(l);
            lean_nat_add(one, d)
        }
    }
}

fn leftDepth(p : Tree_Box) -> Nat {
    leftDepth_go(p)
}

// in main:
let t : Tree_Nat = build(n);
let depth : Nat = leftDepth(conv_Tree_Nat_to_Tree_Box(t));
```

- `build` and `leftDepth` follow the LCNF line by line.
- `main` cannot pass a `Tree_Nat` where a `Tree_Box` is expected, so it
  calls a conversion.

The conversion. It keeps its own stack of nodes (`Conv_K`), so a deep tree
does not overflow the machine stack:

```rust
enum Conv_M {                     // the next step
    down(Tree_Nat),               // convert this node
    up(Tree_Box)                  // a node is converted: give it to the stack
}
enum Conv_K {                     // the stack of nodes in progress
    done,
    left(Tree_Nat, Conv_K),       // the left child is in progress
    right(Tree_Nat, Tree_Box, Conv_K)   // the right child is in progress; the left is done
}

fn conv_leaf(x : Tree_Nat) -> Tree_Box {
    match x {
        Tree_Nat::c_leaf(n) => { Tree_Box::c_leaf{L2RBox::b2{n}} },
        _ => { l2r_unreachable<Tree_Box>() }
    }
}

fn conv_node(x : Tree_Nat, l : Tree_Box, r : Tree_Box) -> Tree_Box {
    match x {
        Tree_Nat::c_node(_, _) => { Tree_Box::c_node{l, r} },
        _ => { l2r_unreachable<Tree_Box>() }
    }
}

fn conv_loop(m : Conv_M, k : Conv_K) -> Tree_Box {
    match m {
        Conv_M::down(x) => {
            match x {
                Tree_Nat::c_leaf(_) => { conv_loop(Conv_M::up{conv_leaf(x)}, k) },
                Tree_Nat::c_node(_, _) => { conv_loop(Conv_M::down{match x {
                    Tree_Nat::c_node(l, _) => { l },
                    _ => { l2r_unreachable<Tree_Nat>() }
                }}, Conv_K::left{x, k}) }
            }
        },
        Conv_M::up(d) => {
            match k {
                Conv_K::done => { d },
                Conv_K::left(x, k2) => { conv_loop(Conv_M::down{match x {
                    Tree_Nat::c_node(_, r) => { r },
                    _ => { l2r_unreachable<Tree_Nat>() }
                }}, Conv_K::right{x, d, k2}) },
                Conv_K::right(x, l, k2) => { conv_loop(Conv_M::up{conv_node(x, l, d)}, k2) }
            }
        }
    }
}

fn conv_Tree_Nat_to_Tree_Box(x : Tree_Nat) -> Tree_Box {
    conv_loop(Conv_M::down{x}, Conv_K::done{})
}
```

- `conv_loop` calls itself only in tail position, so LLVM turns these
  calls into a loop.
- At a node, it converts the left child, then the right child, then makes
  the new node (`conv_node`).
- It does not remember a node that it converted. `build` makes each node
  with two pointers to the same child, so the conversion converts that
  child two times. Each level doubles the work: `build n` (n + 1 nodes)
  gives 2<sup>n+1</sup> − 1 nodes.

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
