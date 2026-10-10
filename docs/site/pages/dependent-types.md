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
compiler does not know is one word, a *box* (`LAny`). The box holds a
small value itself, or it points to an object and records the type of
that object. The program takes the value out of the box at the type that
it needs.
</div>

A *dependent type* is a type that contains a value, such as the `n` in
`Vector String n`, or a type that a value selects, such as `t.denote` below.

All the Lean code on this page is one program (the runtime test
`RtDepSiteEx`). It type-checks, and its lean2rr build gives the same output
as its native build. The LCNF on this page is the output of Lean's compiler
for that program (mono phase, with the types of parameters and `let`
values). The Reussir code is the output of lean2rr for that program
(`--keep-rr`), with shorter, readable names.

## Types and values

Lean's compiler translates a program to LCNF, its intermediate code. In
LCNF, it replaces two kinds of items:

- **`◾`** replaces an item without data: a type, a type argument or a proof.
  In a type, LCNF writes it as `lcErased`. It carries no information, and
  lean2rr removes it: the Reussir code has no field, no parameter and no
  argument for it (rule 4 of
  [Layouts of generic types](#layouts-of-generic-types)).
- **`lcAny`** replaces the *type* of a value when the compiler does not know
  that type. The value itself has data. lean2rr stores the value in a box.

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
  type uses `LAny` for `x` and `y`.

Functions get a copy for each type argument. Data types do not: each
datatype has one layout (rule 1).

In Rust terms, a box is similar to an `Rc<dyn Any>` that stores small
values inside the word.

## The box `LAny`

{{svg:box}}

A box is one 64-bit word, as native Lean's `lean_object*`:

- **An odd word is an immediate**, `(v << 1) | 1`. The unit value `()` and
  Lean's `box(0)` are the word 1. A `Bool`, a `Char`, a `UInt8`, `UInt16`
  or `UInt32`, a `Float32`, an enumeration's index, a constructor without
  fields, a small `Nat` or `Int` (its own word) and a `UInt64` below
  2<sup>63</sup> are immediates. An immediate is never allocated.
- **An even word is a pointer** to a counted object. The low 48 bits are the
  address. The top 16 bits are the *type number* of the object.

The type numbers:

| Number | Object |
|---|---|
| 1, 2 | a big `Nat`, a big `Int` |
| 3 | a `String` |
| 4, 5 | a cell for a `Float`, a cell for a `UInt64` from 2<sup>63</sup> |
| 6, 7, 8 | an `Array`, a `ByteArray`, a `FloatArray` |
| 16 and up | a type of the program: a record, an enum, a function value, a reference, a thunk or task cell |

For the program on this page, lean2rr numbers seven types of its own. Two
of them occur below: `Sigma` is 21, `Prod` is 22.

To put a value into a box, the code calls `l2r_any_of<T>(x, num)`. To take
a value out, it calls `l2r_any_as<T>(b, num)`, or it splits the word
itself. Each read checks the word:

- a pointer with the expected number gives the object;
- `box(0)` gives the *zero* of the type: `0`, `""`, an empty array, or a
  value that lean2rr builds for the type (see
  [Placeholders](representations.html#placeholders));
- any other word is a panic (`unreachable`), never a wrong read. In a
  program that casts, a read also accepts the types that a cast can give.

This code, from `describe` below, takes a `String` out of the box `v`:

```rust
lean_string_append(prefix, l2r_any_as<LStr>(v, 3))     // 3: the number of String
```

The program releases its own types. For each type number, lean2rr
generates a release function (`l2r_any_rel_<n>`). The runtime keeps these
functions in a table. When the last reference to a boxed record goes, the
runtime calls the function of its number.

## Where lean2rr uses the box

Every position whose type is `lcAny` holds a box: a field, a parameter, a
result, a local value, or an argument of a function value. A type is
unknown in these cases:

- a type parameter (`x : α`);
- a type that another field holds (`val : α` in a structure with the field
  `α : Type`);
- a type that a value selects (`Sigma.snd`, `Array ty.denote`);
- a type function applied to an argument (`f Nat`, with `f` a parameter).

A field of a datatype whose type is a parameter is also a box, at every
type argument (rule 1). So are the elements of an array, the value of a
thunk or task, and the contents of a reference.

lean2rr puts a value into a box where the value goes into such a
position. It takes the value out where the value comes back to a known
type.

## Layouts of generic types

These are the layout rules:

1. **One layout for each datatype.** lean2rr computes the layout of each
   constructor one time, from the declared field types. A field whose type
   is a parameter is a box. `Tree Nat` and `Tree α` are one Reussir type.
   `Array α` is `RVec<LAny>` for every `α`. `Thunk α`, `Task α`,
   references and promises also have one type each, over the box. So no
   value is converted when it goes from typed code to generic code.
2. **A field with a concrete type keeps that type.** In
   `structure P where x : Float`, `x` is a raw `f64`.
3. **A structure with one relevant field is that field** (`Fin n`,
   `Subtype`).
4. **`lcErased` is removed.** It carries no information, and lean2rr does
   not need it. A function has no parameter for it, and a call has no
   argument for it. When the last parameters of a function are erased, the
   function keeps one unit parameter for that group. So its body runs at
   the same point as natively, and a function with only erased parameters
   stays a function. A function type keeps a unit domain only where a
   function value of that type runs its body right after that domain.
5. **Function values have one calling convention.** A function that is
   stored where its type is generic gets an entry that takes and returns
   boxes.
6. **Casts in Lean's library go through the box.** `Dynamic`,
   `Array.mapM` and `ShareCommon` use `NonScalar` with unsafe casts.
   lean2rr represents `NonScalar` as a box.
7. **Unsafe functions that read a representation** (`ptrAddrUnsafe`,
   `isExclusiveUnsafe`, `ptrEq`) can give other answers than in a native
   build (see [Known differences](differences.html#identity-and-sharing)).

Native Lean uses the same layout scheme. In a native build, a field of
unknown type is one `lean_object*` word.

### Rule 4: examples

| Lean | Reussir |
|---|---|
| `def f (x : Nat) (α : Type) (y : Nat) (β γ : Type)` | `f(x : Nat, y : Nat, u : L2RUnit)` |
| `def el {α : Type} : List α` | `el(u : L2RUnit)` |
| `pick (α : Type) (b : Bool) (x y : α)` | `pick_Nat(b : bool, x : Nat, y : Nat)` |
| the type `{α : Type} → List α → Nat` (`Op.run` below) | the function type `List -> Nat` |

- In `f`, the parameter `α` is removed. `β` and `γ` are the last parameters,
  so they become one unit parameter `u`. A call `f 1 Nat 2` runs the body
  only when the types `β` and `γ` are applied, as natively.
- `el` has only erased parameters. It keeps one unit parameter, so it stays
  a function.
- In the type of `Op.run`, the erased domain `{α : Type}` comes before a
  data domain, so it is removed.

### Memory

A box is one word. So a generic field or an array element takes 8 bytes,
as natively. A small value goes into the word: a `List Nat` cell or an
`Array Nat` element of a small number allocates nothing more. A `Float`
and a `UInt64` from 2<sup>63</sup> go into a cell of their own, as in a
native build. A `[value]` struct of several fields goes into a one-field
cell (`ElemBox`).

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
struct Column(RVec<LAny>, Ty)         // data, then ty
enum [value] Ty { c_nat, c_str }      // stored inline, never allocated

fn Column_push(c : Column, i : Nat) -> Column {
    let ty : Ty = c.1;
    let data : RVec<LAny> = c.0;
    match ty {
        Ty::c_nat => {
            let data2 : RVec<LAny> = lean_array_push<LAny>(data, l2r_any_of<Nat>(i, 1));
            Column{data2, Ty::c_nat{}}
        },
        Ty::c_str => {
            let s : LStr = l2r_nat_repr(i);
            let data2 : RVec<LAny> = lean_array_push<LAny>(data, l2r_any_of<LStr>(s, 3));
            Column{data2, Ty::c_str{}}
        }
    }
}
```

- `data` is an `RVec<LAny>`: an array of boxes. `Array Nat`,
  `Array String` and `Array lcAny` are all this type.
- `push` puts the new element into a box: number 1 for a `Nat`, 3 for a
  `String`. A small `Nat` is its own word, so its box allocates nothing.
  `push` changes the array in place when the array is unique.
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

lean2rr generates this code:

```rust
fn pickT(b : bool) -> LAny {
    if b {
        let n : Nat = l2r_nat_small(42);
        l2r_any_of<Nat>(n, 1)
    } else {
        let s : LStr = l2r_str_lit_cached(28);   // the constant "hello", made once
        l2r_any_of<LStr>(s, 3)
    }
}

fn describe(b : bool, v : LAny) -> LStr {
    if b {
        let prefix : LStr = l2r_str_lit_cached(29);  // the constant "nat "
        let one : Nat = l2r_nat_small(1);
        let m : Nat = lean_nat_add(l2r_any_as<Nat>(v, 1), one);
        let digits : LStr = l2r_nat_repr(m);
        lean_string_append(prefix, digits)
    } else {
        let prefix : LStr = l2r_str_lit_cached(30);  // the constant "str "
        lean_string_append(prefix, l2r_any_as<LStr>(v, 3))
    }
}
```

- `pickT` returns a box. The `true` branch puts 42 into it: the box is the
  word of the small `Nat` 42. The `false` branch puts `"hello"` into it:
  the box is the string's pointer, with the number 3.
- `describe` takes the value as a box (`v`). The `true` branch takes a
  `Nat` out of the box and adds 1. The `false` branch takes a `String` out
  of the box and appends it.
- `l2r_any_as<Nat>(v, 1)` gives the `Nat` of a small word or of a pointer
  with the number 1. For `box(0)`, it gives 0, as in a native build:
  `box(0)` is reached only with `unsafeCast`. For any other word, it
  panics.
- A string constant (`"hello"`, `"nat "`, `"str "`) is made once and kept
  in the runtime's literal cache; each use reads it (pass
  `literal-consts`). `28` is the number of the literal `"hello"` in the
  program's literal table. The function below serves every such read of
  the program:

```rust
fn l2r_str_lit_cached(id : u64) -> LStr {
    let r : u64 = if l2r_lit_ready(id) { 0 } else { l2r_str_lit_fill(id) };
    l2r_lit_get(id)                 // a new reference to the kept string
}
```

`l2r_lit_ready` loads the slot of the literal from a table at a fixed
address. At the first read the slot is empty, and `l2r_str_lit_fill`
makes the string and keeps it there. Other constants have a once-cell
each ([Pipeline](pipeline.html)).

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
struct Sigma(LAny, LAny)                     // fst, snd
enum List { c_nil, c_cons(LAny, List) }      // every List

fn entries(n : Nat) -> List {
    let t1 : Ty = Ty::c_nat{};
    let p1 : Sigma = Sigma{l2r_any_imm(Ty_index(t1)), l2r_any_of<Nat>(n, 1)};      // ⟨.nat, n⟩
    let t2 : Ty = Ty::c_str{};
    let s : LStr = l2r_nat_repr(n);
    let p2 : Sigma = Sigma{l2r_any_imm(Ty_index(t2)), l2r_any_of<LStr>(s, 3)};     // ⟨.str, toString n⟩
    let nil : List = List::c_nil{};
    let l2 : List = List::c_cons{l2r_any_of<Sigma>(p2, 21), nil};
    List::c_cons{l2r_any_of<Sigma>(p1, 21), l2}
}
```

- The code follows the LCNF line by line: two pairs, then the list.
- `Sigma` has one layout. Both of its fields have a parameter's type
  (`Sigma α β`), so both are boxes. The `Ty` goes into its box as the
  immediate of its index. `n` goes in as a `Nat` (number 1), the string as
  a `String` (number 3).
- `List` has one layout for every element type: each cell holds a box and
  the rest of the list. Each pair goes into the list as a box with the
  number of `Sigma`, 21.

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
- The field `val` is `lcAny`. It is a box.
- The field `fmt` takes an `lcAny`. It takes a box.

lean2rr generates this code:

```rust
struct Pkg(LAny, Fn_Box_Str)          // val, fmt; α has no field

enum Fn_Box_Str {                     // a function value: LAny -> LStr
    z,
    raw(LAny -> LStr),
    wrap_Prod(Fn_Prod_Str),           // wraps a Prod -> LStr function
    wrap_Nat(Fn_Nat_Str)              // wraps a Nat -> LStr function
}

fn Pkg_show(p : Pkg) -> LStr {
    let val : LAny = p.0;
    let fmt : Fn_Box_Str = p.1;
    apply_Fn_Box_Str(fmt, val)
}
```

- A `Pkg` has two fields: `val` is a box, and `fmt` is a function value
  that takes a box.
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
let p : Pkg = Pkg{l2r_any_of<Nat>(five, 1), Fn_Box_Str::wrap_Nat{f}};
let s : LStr = Pkg_show(p);
```

- `Pkg.mk ◾ _x.30 _f.29`: the `◾` is the type `Nat`. It has no field.
- `5` goes into a box: the word of the small `Nat` 5.
- `Nat.reprFast` takes a `Nat`, not a box, so lean2rr puts it into the
  variant `wrap_Nat`.
- These lines have no free variables, so Lean's compiler makes them a
  closed term of `main`: they run once.

`apply_Fn_Box_Str` applies a function value of the type
`Fn_Box_Str`:

```rust
fn apply_Fn_Box_Str(f : Fn_Box_Str, x : LAny) -> LStr {
    match f {
        Fn_Box_Str::z => { zero_String() },
        Fn_Box_Str::raw(c) => { c(x) },
        Fn_Box_Str::wrap_Prod(g) => { apply_Fn_Prod_Str(g, unbox_Prod(x)) },
        Fn_Box_Str::wrap_Nat(g) => { apply_Fn_Nat_Str(g, l2r_any_as<Nat>(x, 1)) }
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
- A function type has several representations (`Nat -> LStr` and
  `LAny -> LStr`). So lean2rr wraps a function value of one
  representation for another. The wrapper is one new cell around the
  function value. It does not copy the function.

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
one copy of `nest` for these calls. In that copy, `x` is a box, and the
`ToString` dictionary is a value that the copy receives:

```rust
struct Prod(LAny, LAny)               // every Prod

fn nest_Box(inst : Fn_Box_Str, n : Nat, x : LAny) -> LStr {
    let instPair : Fn_Prod_Str = Fn_Prod_Str::toStringPair{inst, inst};
    let zero : Nat = l2r_nat_small(0);
    let isZero : bool = lean_nat_dec_eq(n, zero);
    if isZero {
        apply_Fn_Box_Str(inst, x)
    } else {
        let one : Nat = l2r_nat_small(1);
        let n1 : Nat = lean_nat_sub(n, one);
        let pair : Prod = Prod{x, x};
        nest_Box(Fn_Box_Str::wrap_Prod{instPair}, n1, l2r_any_of<Prod>(pair, 22))
    }
}
```

- `instPair` is `_f.4`: the dictionary for pairs.
- At count 0, the copy applies `inst` to `x`.
- Else it builds the pair `(x, x)`, puts the pair into a box (the number of
  `Prod` is 22), and calls itself. `instPair` takes a `Prod`, and the copy
  needs a dictionary that takes a box, so lean2rr wraps it.

The dictionary for pairs:

```rust
enum Fn_Prod_Str {                    // a function value: Prod -> LStr
    z,
    raw(Prod -> LStr),
    toStringPairNat,                  // ToString (Nat × Nat)
    toStringPair(Fn_Box_Str, Fn_Box_Str)  // ToString (α × β), from the two dictionaries
}

fn toStringPair(fa : Fn_Box_Str, fb : Fn_Box_Str, p : Prod) -> LStr {
    let a : LAny = p.0;
    let b : LAny = p.1;
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

- A call through `wrap_Prod` takes the `Prod` out of the box, then calls
  `toStringPair`.

The program calls `nest 2 n` with `n : Nat`. lean2rr makes a copy of `nest`
at `Nat` for this call. It makes the first pair, then calls the copy at
the box:

```rust
fn nest_Nat(n : Nat, x : Nat) -> LStr {
    let zero : Nat = l2r_nat_small(0);
    let isZero : bool = lean_nat_dec_eq(n, zero);
    if isZero {
        l2r_nat_repr(x)
    } else {
        let instPair : Fn_Prod_Str = Fn_Prod_Str::toStringPairNat{};
        let one : Nat = l2r_nat_small(1);
        let n1 : Nat = lean_nat_sub(n, one);
        let pair : Prod = Prod{l2r_any_of<Nat>(x, 1), l2r_any_of<Nat>(x, 1)};
        nest_Box(Fn_Box_Str::wrap_Prod{instPair}, n1, l2r_any_of<Prod>(pair, 22))
    }
}
```

- The first pair is a `Prod` too: `Prod Nat Nat` and `Prod α α` have one
  layout. Its fields are the boxes of `x`.
- `nest_Box` makes the next pairs, with the same type.
- The arm `wrap_Prod` of `apply_Fn_Box_Str` takes the `Prod` out of the
  box in line. It splits the word, and it converts nothing. Here is that
  code as a function, `unbox_Prod`:

```rust
fn unbox_Prod(b : LAny) -> Prod {
    let w : u64 = l2r_any_raw(b);
    if l2r_any_raw_is_imm(w) {
        if w == 1 { zero_Prod() }                        // box(0): the zero of Prod
        else { l2r_unreachable<Prod>() }
    } else {
        if l2r_any_raw_num(w) == 22 { l2r_any_raw_take<Prod>(w) }   // the number of Prod
        else { l2r_unreachable<Prod>() }
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
fn ops_lam(xs : List) -> Nat {
    let len : Nat = List_length(xs);
    let two : Nat = l2r_nat_small(2);
    lean_nat_mul(len, two)
}
```

- The type argument `α.1` is `lcErased`, and it is not the last parameter.
  So `ops_lam` has no parameter for it (rule 4).
- `xs` is the list: each cell holds a box and the rest of the list.
- The function counts the cells and multiplies by 2:

```rust
fn List_length(xs : List) -> Nat {
    let zero : Nat = l2r_nat_small(0);
    List_length_aux(xs, zero)
}

fn List_length_aux(xs : List, acc : Nat) -> Nat {
    match xs {
        List::c_nil => { acc },
        List::c_cons(h, t) => {
            let one : Nat = l2r_nat_small(1);
            let acc1 : Nat = lean_nat_add(acc, one);
            List_length_aux(t, acc1)
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
enum Fn_Op {                          // a function value: List -> Nat
    z,
    raw(List -> Nat),
    ops_lam,                          // the function ops_lam
    List_length                       // the function List.lengthTR
}

fn ops_tail() -> List {               // the constant [ops_lam]
    let nil : List = List::c_nil{};
    let f : Fn_Op = Fn_Op::ops_lam{};
    List::c_cons{l2r_any_of_fn<Fn_Op>(f, 16), nil}
}

fn ops_init() -> List {
    let tail : List = ops_tail();
    let g : Fn_Op = Fn_Op::List_length{};
    List::c_cons{l2r_any_of_fn<Fn_Op>(g, 16), tail}
}
```

- The type of `run` has the erased domain `{α : Type}` before the list.
  So the function type is `List -> Nat`, without a unit (rule 4).
- `ops` is a constant: lean2rr computes `ops_init()` once and keeps the
  list in a once-cell. Lean's compiler also makes the tail `[ops_lam]` a
  constant of its own (`ops_tail`).
- Each element is a function value in a box. A function value without
  captured values is an immediate: its type number (16) and its variant.
  It allocates nothing.

## One layout for a shared tree

Rule 1 gives `Tree Nat` and `Tree α` one layout. So a tree goes from typed
code to generic code as it is, and its shared nodes stay shared:

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
  and `Tree lcAny` have the same layout, so the tree goes as it is. In the
  lean2rr build too.

lean2rr generates one tree type:

```rust
enum Tree {                       // Tree Nat, Tree lcAny and every other Tree
    c_leaf(LAny),
    c_node(Tree, Tree)
}
```

The functions:

```rust
fn leaf7_init() -> Tree {                 // the constant .leaf 7
    let seven : Nat = l2r_nat_small(7);
    Tree::c_leaf{l2r_any_of<Nat>(seven, 1)}
}

fn build(n : Nat) -> Tree {
    let zero : Nat = l2r_nat_small(0);
    let isZero : bool = lean_nat_dec_eq(n, zero);
    if isZero {
        leaf7()                           // reads the constant from its once-cell
    } else {
        let one : Nat = l2r_nat_small(1);
        let n1 : Nat = lean_nat_sub(n, one);
        let t : Tree = build(n1);
        Tree::c_node{t, t}                // both children are the same t
    }
}

fn leftDepth_go(t : Tree) -> Nat {
    match t {
        Tree::c_leaf(x) => { l2r_nat_small(0) },
        Tree::c_node(l, r) => {
            let one : Nat = l2r_nat_small(1);
            let d : Nat = leftDepth_go(l);
            lean_nat_add(one, d)
        }
    }
}

fn leftDepth(p : Tree) -> Nat {
    leftDepth_go(p)
}

// in main:
let t : Tree = build(n);
let depth : Nat = leftDepth(t);
```

- `build` and `leftDepth` follow the LCNF line by line.
- The leaf's field has the parameter's type, so it is a box. `build` puts
  7 into it: the word of the small `Nat` 7.
- `main` passes the tree to `leftDepth` as it is. No code copies the tree.
  `build n` makes n + 1 nodes, and they stay n + 1 nodes.

Peak memory (max RSS) of the whole program, with `build n`:

| n | Native | lean2rr |
|---|---|---|
| 16 | 8.1 MB | 7.1 MB |
| 20 | 8.0 MB | 7.3 MB |
| 24 | 8.0 MB | 7.2 MB |

A value is converted only for a cast between two different inductives
whose layouts differ (a field that holds an `Int` where the source's field
holds a `Nat`). Plan
[§10](repo:docs/translation-plan.md#10-known-divergences-and-unsupported-features)
lists this cost.

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
