# Dependent types

<p class="lead">How lean2rr compiles a type that depends on a run-time value.
Sources: translation plan
<a href="repo:docs/translation-plan.md#26-when-a-type-is-not-statically-known">§2.6</a>,
<a href="repo:docs/translation-plan.md#3-stage-2--leans-mono-pipeline-leans-passes-driven-by-us">§3</a>,
<a href="repo:docs/translation-plan.md#4-stage-3--check-and-recover-lost-types">§4</a> and
<a href="repo:docs/translation-plan.md#10-known-divergences-and-unsupported-features">§10</a>,
and the implementation notes on
<a href="repo:docs/implementation/types/uniform-types.md">unknown types</a>,
<a href="repo:docs/implementation/types/type-recovery.md">type recovery</a>,
<a href="repo:docs/implementation/types/polymorphic-recursion.md">polymorphic recursion</a> and
<a href="repo:docs/implementation/representations/box-and-uniform.md">the uniform type</a>.</p>

<div class="rule" markdown="1">
**Nothing is rejected.** lean2rr compiles every program with dependent
types that Lean compiles, and the program gives the same results as its
native build. Where a type is known only at run time, lean2rr uses a uniform
representation. That is always correct. It can be slower.
</div>

A *dependent type* is a type that mentions a value. Often the value is a
proof or a length, such as the `n` in `Vector String n`. Lean's compiler
erases such values, so these types need nothing special. This page is about
the other case: the type itself changes with a value that is known only at
run time.

## Specialization first

lean2rr makes a separate copy of each generic type and each generic
function for each list of type arguments. Each copy is an *instance*. This
is *monomorphization*: the specialization that `rustc` does for generics
(Stage 1 of the [pipeline](pipeline.html#stage-1-collect-and-monomorphize)).
Native Lean does not do it: it has one copy, and each field of a generic
type holds a pointer.

```lean
inductive Tree (α : Type) where
  | leaf (x : α)
  | node (left right : Tree α)

@[noinline] def Tree.size {α : Type} : Tree α → Nat
  | .leaf _ => 1
  | .node l r => l.size + r.size

def main : IO Unit := do
  let a : Tree Float := .node (.leaf 1.5) (.leaf 2.5)
  let b : Tree String := .node (.leaf "x") (.leaf "y")
  IO.println (a.size + b.size)
```

- Line 1: `Tree` is a generic type. `α` is its type parameter, as `T` in
  the Rust type `Tree<T>`.
- Line 2: a `leaf` holds one value of the type `α`.
- Line 3: a `node` holds two subtrees.
- Line 5: `Tree.size` is a generic function. `{α : Type}` is its type
  parameter. `@[noinline]` keeps it a separate function.
- Lines 6 and 7: a leaf counts 1. A node adds the sizes of its two
  subtrees.
- Lines 10 and 11: `main` makes a tree of `Float`s and a tree of
  `String`s.
- Line 12: it prints the sum of the two sizes: 4.

In Rust terms: `enum Tree<T> { Leaf(T), Node(Rc<Tree<T>>, Rc<Tree<T>>) }`
and `fn size<T>(t: Rc<Tree<T>>) -> Nat`.

lean2rr generates two types and two functions (checked with
`lean2rr --emit rr`, abridged):

```rust
enum T_Tree_1236 {                    // Tree Float
    c_leaf(f64),                      // the number is in the leaf
    c_node(T_Tree_1236, T_Tree_1236)
}
enum T_Tree_1248 {                    // Tree String
    c_leaf(LStr),
    c_node(T_Tree_1248, T_Tree_1248)
}

fn l_Tree_size___l2r_0____redArg(a : T_Tree_1236) -> Nat { … }  // size at Float
fn l_Tree_size___l2r_1____redArg(a : T_Tree_1248) -> Nat { … }  // size at String
```

- Each instance has its own name. The numbers in the names only make the
  names unique.
- A leaf of `Tree Float` holds the `f64` itself. Native Lean allocates a
  separate cell for each `Float` in a generic field (`lean_box_float`). So
  natively, each leaf costs two cells.
- `main` calls the instance at `Float` for `a`, and the instance at
  `String` for `b`.

{{svg:spec}}

Monomorphization is the reason why most lean2rr code has no boxes.
lean2rr makes an instance only for the type arguments that the program
uses. A type
parameter that no data field uses (a *phantom*) does not make a new type.

**When monomorphization stops.** Sometimes the type argument is not known
at compile time. Then lean2rr uses Lean's unknown type, `lcAny`, and makes
the *uniform instance*: the instance at `lcAny`. In the uniform instance, a
field of the type `α` is an `L2RBox`: a pointer to a cell with a tag (see
[Representations](representations.html#the-uniform-type-l2rbox)).
Natively, all code works in this way. The rest of this page shows where
a type is not known at compile time, what lean2rr does there, and what a
value costs when it goes from one layout to the other.

## The mechanism

1. **Lean marks the position.** Lean's compiler cannot compute a type such
   as `t.denote` when `t` is a variable. In the base code that lean2rr
   reads, it writes `lcAny` there: Lean's "unknown type". For example, a
   field `data : Array t.denote` has the type `Array lcAny`.
2. **lean2rr keeps the mark.**
    - Stage 1 also makes a type argument `lcAny` when the argument is not
      statically known.
    - Stage 2 keeps a *type family* (a function that gives a type) only
      when it is a constant function (`fun _ => Nat`) or a type
      constructor (`Vector String`). A family whose body uses its variable
      (`fun t => t.denote`) becomes `lcAny`.
    - Stage 3 never takes a type from a use. A use of `data` as
      `Array Nat` is correct only in the branch where `t = .nat`.
3. **Stage 4 boxes the value.** It stores each value of type `lcAny` in
   `L2RBox`.

`L2RBox` is a closed tagged union that lean2rr generates for each program:

- It has one variant per concrete type that the program boxes, plus a unit
  variant (Lean's `box(0)` placeholder).
- Stage 4 adds the variants as it needs them. At the end of Stage 4, the
  set is complete.
- Code that needs the concrete type checks the tag with a `match`.

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
variants have numbers, in the order in which Stage 4 needed them.

Native Lean stores every value in a uniform way: a pointer to an object
(`lean_object*`), or a small number inside the pointer. lean2rr uses the
uniform `L2RBox` only where the type is truly unknown. Everywhere else, a
value has its precise type.

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

Code that uses a column matches on `ty` first:

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

In Rust, with the enum above:

```rust
match c {
    Column::Nat(mut d) => { d.push(i); Column::Nat(d) }
    Column::Str(mut d) => { d.push(i.to_string()); Column::Str(d) }
}
```

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
- `push` boxes only the new element (`L2RBox::b2{i}`). It updates the array
  in place when the array is unique. The optional pass `uniform-updates`
  makes this possible (see [Costs](#costs)).
- `ty` is a `[value]` enum. So a `Column` is one cell, plus its array.

A read checks the tag. This is a read of one element of a `.str` column
(abridged):

```rust
let s : LStr = match lean_array_uget<L2RBox>(d, i) {
    L2RBox::b1(s) => { s },                // the String variant
    L2RBox::b0(_) => { l2r_zero_LStr() },  // Lean's box(0): the zero String
    _ => { l2r_unreachable<LStr>() }       // no other variant holds a String
};
```

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
- Line 7: if the Boolean is true, the value is a `Nat`. `let m : Nat := n`
  names it at the type `Nat`. `s!"…"` builds a string.
- Line 8: if the Boolean is false, the value is a `String`.

A Rust function cannot return two different types. The Rust version returns
an enum: `fn pick(b: bool) -> NatOrStr`.

lean2rr gives that position the uniform type in both functions:

```rust
fn pick(b : bool) -> L2RBox                 // L2RBox::b2{42} or L2RBox::b1{"hello"}
fn describe(b : bool, v : L2RBox) -> LStr   // each branch checks the tag of v
```

### Sigma types

A Sigma type `(x : A) × B x` is a pair. The type of its second component
depends on the value of its first component. Rust has no direct equivalent.
The nearest Rust type is a pair whose second part is an enum:
`(Ty, NatOrStr)`.

```lean
def entries : List ((t : Ty) × t.denote) :=
  [⟨.nat, (5 : Nat)⟩, ⟨.str, "five"⟩]

def vecs : List ((n : Nat) × Vector String n) :=
  [⟨2, ⟨#["a", "b"], rfl⟩⟩, ⟨0, ⟨#[], rfl⟩⟩]
```

- Line 1: `entries` is a list of pairs. In each pair, the first component
  `t` is a `Ty`, and the second component has the type `t.denote`.
- Line 2: the first pair holds `.nat` and the `Nat` 5. The second pair
  holds `.str` and the `String` `"five"`. `⟨…⟩` builds a pair.
- Line 4: `vecs` is a list of pairs. The first component `n` is a `Nat`.
  The second is a `Vector String n`: an array of exactly `n` strings.
- Line 5: `⟨#["a", "b"], rfl⟩` builds a vector from an array and a proof
  (`rfl`) that the size of the array is 2.

`Vector String n` is a structure with two fields: `toArray : Array String`,
and a proof that `toArray.size = n`. In Rust terms, it is
`struct Vector { to_array: Vec<String> }`, plus a fact that the compiler
checks and then forgets.

| Lean type | lean2rr build (checked with `--emit rr`) | Boxed |
|---|---|---|
| `(t : Ty) × t.denote` | `struct T_Sigma(L2RBox, T_Ty)`: the second component, then the first | the second component |
| `(n : Nat) × Vector String n` | `struct T_Sigma(Nat, RVec<LStr>)` | nothing |

Why the two pairs differ:

- `t.denote` is a different type for each `t`, so no single representation
  fits. The second component is `lcAny`, so it is an `L2RBox`.
- `Vector String n` has the same data for every `n`: an `Array String`.
  `n` occurs only in the type and in the proof field. The family
  `fun n => Vector String n` is the type constructor `Vector String`, so
  Stage 2 keeps it. Lean's compiler erases the proof, and it stores a
  structure with one data field as that field. So the second component is
  an `RVec<LStr>`, and nothing is boxed.
- The same holds for `Vector String (n + 1)` and `Fin (n + 1)`. In the base
  code, Lean has already replaced the value `n + 1` by `lcAny`, so the
  family is a constant function. lean2rr stores those pairs as
  `(Nat, RVec<LStr>)` and `(Nat, Nat)`.

### At run time

{{svg:depvalues}}

## Other types known only at run time

Three more cases give a type that is known only at run time. lean2rr uses
`lcAny` for them too: a value of that type is an `L2RBox`, and a generic
function called at that type runs its instance at `lcAny`. When every type
argument is `lcAny`, that instance is the *uniform instance*. Native Lean
treats every value in this way, so this is always correct, only slower.

### A type unpacked from an existential

```lean
structure Pkg where
  α : Type
  val : α
  fmt : α → String
```

- Line 1: `Pkg` is a structure: a package of a type and a value.
- Line 2: the field `α` is a type. A type has no run-time value, so the
  compiler erases this field.
- Line 3: the field `val` is a value of the type `α`.
- Line 4: the field `fmt` is a function that turns an `α` into a string.

In Rust terms, a `Pkg` is like a `Box<dyn Display>`: a value of a hidden
type, with a function for it. lean2rr generates `struct T_Pkg(L2RBox, …)`:
`val` is an `L2RBox`, and `fmt` is a function value from `L2RBox` to `LStr`.
A generic function called on `p.val`, such as `List.replicate 2 p.val`,
runs its instance at `lcAny`.

### Polymorphic recursion

```lean
def nest {α : Type} [ToString α] : Nat → α → String
  | 0, x => toString x
  | n + 1, x => nest n (x, x)
```

- Line 1: `nest` is generic over a type `α` that can be printed:
  `[ToString α]` is a type class, like a Rust trait bound. `nest` takes a
  count and an `α`.
- Line 2: at count 0, it prints `x`.
- Line 3: otherwise, it calls itself with the pair `(x, x)`. That call is at
  the type `α × α`.

Rust rejects this function: monomorphization would need `nest::<Nat>`,
`nest::<(Nat, Nat)>`, and so on without end. lean2rr makes the instance at
`Nat`. The next request, at `Nat × Nat`, strictly contains the type
argument of an instance of `nest` on the same path (`Nat`). So lean2rr
sends that call to the uniform instance. In that one copy, `x` is an `L2RBox`, and the `ToString` dictionary is a
run-time value. Bounds stop growth that no path shows: a type argument
deeper than 64 or larger than 256 nodes becomes `lcAny`, and past 1024
instances of one declaration, every new instance is the uniform instance.

### A partial application that leaves a type open

```lean
structure Op where
  run : {α : Type} → List α → Nat

def ops : List Op := [⟨List.length⟩, ⟨fun xs => xs.length * 2⟩]
```

- Line 1: `Op` is a structure.
- Line 2: its one field, `run`, is a generic function: it takes a list of
  any element type `α` and returns a `Nat`.
- Line 4: `ops` holds two such functions: `List.length`, and a function
  that doubles the length.

Rust cannot store a generic function in a field. The nearest form takes a
type-erased list: `fn(&[Box<dyn Any>]) -> usize`. lean2rr does the same.
`List.length` is used here without its type argument, so its instance is at
`lcAny`: it takes a list of `L2RBox`es. A call `o.run [1, 2, 3]` first
converts the `List Nat` to that representation.

## When a value changes layout

One Lean type can have two layouts in one program: the *specialized
layout* of its instance at a precise type, and the uniform layout. When a value goes from one to the
other, lean2rr *converts* it: it makes a new value in the other layout.

```lean
@[noinline] def build : Nat → Tree Nat
  | 0 => .leaf 7
  | n + 1 => let t := build n; .node t t

structure Packed where
  α : Type
  tree : Tree α

@[noinline] def leftDepth (p : Packed) : Nat := go p.tree
where
  go {α : Type} : Tree α → Nat
    | .leaf _ => 0
    | .node l _ => 1 + go l

def main (args : List String) : IO Unit := do
  let n := (args.headD "4").toNat!
  IO.println (leftDepth ⟨Nat, build n⟩)
```

`Tree` is the type from [Specialization first](#specialization-first).

- Line 1: `build` takes a number and returns a `Tree Nat`.
- Line 2: `build 0` is a leaf that holds 7.
- Line 3: `build (n + 1)` calculates `t := build n` once. Then it makes a
  node whose two subtrees are both `t`.
- So `build n` has only n + 1 nodes, and each node points two times to the
  same child. This value is *shared*: it is a directed acyclic graph (DAG),
  not a tree.
- Lines 5 to 7: a `Packed` holds a type `α` and a `Tree α`. The type is a
  field, so a `Packed` can hold a tree of each element type. This is an
  *existential* type, similar to `Box<dyn Any>` in Rust.
- Line 9: `leftDepth` takes a `Packed` and calls `go` on its tree.
- Lines 10 to 13: `go` counts the nodes on the leftmost path. It works for
  each `α`.
- Lines 16 and 17: `main` reads `n` from the command line. It builds the
  tree, packs it with `α := Nat`, and prints the left depth, which is `n`.

In Rust terms, `build` returns an `Rc<Tree<Nat>>`, and the two children of
each node are two clones of one `Rc`.

In `leftDepth`, the element type of the tree is the value of a field. So
lean2rr cannot know it at compile time, and `go` is the uniform instance.
lean2rr generates (abridged):

```rust
enum T_Tree_763 {                 // Tree Nat: the instance that build uses
    c_leaf(Nat),
    c_node(T_Tree_763, T_Tree_763)
}
enum T_Tree_774 {                 // Tree lcAny: the instance that go uses
    c_leaf(L2RBox),
    c_node(T_Tree_774, T_Tree_774)
}

fn l_leftDepth___l2r_0_(a : T_Tree_774) -> Nat { … }

// in main:
let x822 : T_Tree_763 = l_build___l2r_0_(x821);
let x830 : Nat = l_leftDepth___l2r_0_(l2r_conv_T_Tree_763_T_Tree_774(x822));
```

- `Packed` has no cell. The field `α` is a type, so the compiler erases it.
  A structure with one data field is stored as that field (pass
  `value-structs`). So `leftDepth` takes the tree.
- `l2r_conv_T_Tree_763_T_Tree_774` is the *conversion*. lean2rr generates
  it for this pair of layouts. It reads the `Tree Nat` and makes a
  `Tree lcAny` with the same shape. Each leaf's `Nat` goes into an `L2RBox`
  (`L2RBox::b2{7}`).
- The conversion uses a loop and an explicit stack, not recursion. So a
  deep value does not overflow the stack.
- Natively, there is no conversion: `Tree Nat` and `Tree α` have the same
  layout.

### Shared values and conversions

{{svg:dagconv}}

On the current version, a conversion follows each pointer separately. It
does not see that two pointers go to the same cell. So it converts a shared
cell one time for each pointer to it, and the result is a tree. `build n`
has n + 1 nodes, but its conversion has 2<sup>n+1</sup> − 1 nodes. Thus the
time and the memory increase exponentially (plan §10, "Structural
conversions"). The peak memory (resident set size) of the example:

| n | Nodes in `build n` | native Lean | lean2rr |
|---|---|---|---|
| 16 | 17 | 7.9 MB | 11 MB |
| 20 | 21 | 7.9 MB | 65 MB |
| 22 | 23 | 7.9 MB | 237 MB |
| 24 | 25 | 7.9 MB | 927 MB |

The output is correct. But each +2 in `n` multiplies the memory by 4, so
`n` = 30 would need approximately 60 GB, and the program would stop.

**The fix (in progress): convert each cell once.** For one conversion,
lean2rr keeps a table from each shared source cell to its converted cell.
When a second pointer goes to the same cell, the conversion uses the
converted cell from the table. Thus a conversion makes at most one cell for
each source cell, and its memory is linear in the size of the value (the
right part of the figure).

- A cell with only one reference cannot be reached two times. So it does
  not go into the table, and a tree without sharing has no table cost.
- The table belongs to lean2rr's generated code and runtime glue, and it
  lives for one conversion. The shared runtime crate does not change.

Two limits stay after this fix:

- A conversion is a copy. While it runs, the source and the copy both
  exist: at most two times the memory. If nothing else uses the source, the
  source is freed after the conversion.
- A value that goes into a uniform position many times is converted each
  time. Each conversion takes time in proportion to the size of the value.
  So a loop of such conversions can be quadratic.
  [Possible future work](#possible-future-work) removes the conversion.

## Costs

These costs are time and memory, never results. Plan
[§2.6](repo:docs/translation-plan.md#26-when-a-type-is-not-statically-known),
[§4](repo:docs/translation-plan.md#4-stage-3--check-and-recover-lost-types)
and [§10](repo:docs/translation-plan.md#10-known-divergences-and-unsupported-features)
("Structural conversions") give the details.

**Boxing allocates.** Each boxed value is one `L2RBox` cell. Natively, a
small number in a uniform position costs nothing, because it is inside the
pointer. A read of a boxed value checks one tag.

**Typed code converts a boxed container.** Suppose that a function takes an
`Array Nat`, and the `.nat` branch passes it the column's `data`. If the
parameter stays typed (see below), lean2rr converts the `RVec<L2RBox>` into
a new `Array Nat` (an `LNatArr`), element by element. That costs O(n) per
call. Natively, the cast is free. A conversion also loses sharing (see
[Shared values and conversions](#shared-values-and-conversions)).

**`uniform-updates` keeps update loops linear.** In the `.nat` branch of
`Column.push`, Lean pushes onto `d` at the type `Array Nat`. Without the
optional pass `uniform-updates`, each update converts the whole array to
`Array Nat`, pushes, and converts the result back to store it in the
column: two copies per update. A loop of updates is then quadratic (review
RV9C-02, before the pass: 40 000 pushes took 7.7 s, natively 0.00 s). The
pass runs such an update on the uniform array instead (plan §4):

- An `Array` extern (`push`, `set!`, `pop`, `swap`, `get`, `size`, …) does
  not depend on its type argument. So the pass calls its instance at
  `lcAny`, and only the one element is boxed or unboxed.
- A cons that goes back into a `List lcAny` field is built at that type.
- A parameter becomes uniform when every call site passes a uniform array
  and the body uses it only uniformly.

The `Column.push` code above shows the result. The tests are
`RtUniformUpdates` and its variants, and `tests/runtime/conv-count-check.sh`,
which counts the converted elements at two sizes.

**A helper that stays typed converts at each call (review C03R-01).** A
helper takes an `Array Nat`, and another caller passes it a typed array:

```lean
@[noinline] def firstPlusSize (a : Array Nat) : Nat := a.size + a[0]!

def Column.step (c : Column) (i : Nat) : Column × Nat :=
  match c with
  | ⟨.nat, d⟩ =>
    let d' := d.push i
    (⟨.nat, d'⟩, firstPlusSize d')
  | c => (c, 0)
```

- Line 1: `firstPlusSize` takes an `Array Nat` and returns its size plus
  its first element. `@[noinline]` keeps it a separate function. `main`
  also calls it with a typed array.
- Line 3: `step` takes a column and a number. It returns a new column and a
  number.
- Lines 5 to 7: for a `.nat` column, it pushes `i` onto the array, and calls
  `firstPlusSize` on the new array.
- Line 8: for another column, it returns the column and 0.

The pass makes a parameter uniform only when every call site passes a
uniform array. Here `main` passes a typed array, so the parameter stays
`Array Nat`. lean2rr generates `firstPlusSize(l2r_vconv(d2))`: each `step`
converts the whole column. In a loop, that is quadratic (in the review,
20 000 steps took 0.79 s, natively 0.00 s). The test is
`RtUniformUpdatesShared`. The helper also stays typed when it is used as a
function value, or when it calls itself with a typed array. A possible fix: a copy of the helper with a
uniform parameter, for the call sites that pass a uniform array, as Stage 1
makes instances.

Plan §10 lists two more shapes that convert at each execution:

- a function that passes its parameter on at a precise type;
- an update whose result is used only at precise types, and never goes
  back to a uniform position.

## Possible future work

**A uniform layout from the start, for the types that cross.** The
conversion in [When a value changes layout](#when-a-value-changes-layout)
exists because `Tree Nat` has two layouts in one program. lean2rr sees the
whole program after specialization. So it can find each type whose values
go into a uniform position. In the example, `Tree Nat` goes to `go` at
`lcAny`. For such a type, lean2rr could use the uniform layout from the
start (not implemented):

- `build` would make leaves that hold an `L2RBox`. The call of `leftDepth`
  would then give the tree as it is: no conversion, no copy, and the same
  memory as native Lean.
- The types inside such a type get the same rule. If a `List (Tree Nat)`
  goes into a uniform position, `Tree Nat` also gets the uniform layout.
- The cost is one `L2RBox` cell for each leaf, but only for the types that
  cross. All other types keep their specialized layouts.

Another design gives each generic type one layout for all type arguments,
as native Lean does. Then no value changes its layout. But each program
pays for the boxes, also a program that never uses an unknown type.

**A typed union per dependent position.** Today one `L2RBox` per program
holds every boxed value, and each element of a dependent array is boxed by
itself. lean2rr could instead generate one union for each dependent
position, with one variant per type that the position can have. For
`Column.data`, a possible design (not implemented):

```rust
enum Column_data {
    nat(LNatArr),       // ty = .nat: an Array Nat
    str(RVec<LStr>)     // ty = .str: an Array String
}
```

- The whole array is in one variant, so its elements are not boxed one by
  one.
- A use at `Array Nat` checks one tag and takes the array. No conversion is
  necessary, so the C03R-01 shape would cost nothing.
- A `match` has only the variants of its position, not every boxed type of
  the program.

This needs the set of types that a family can give: `Ty.denote` gives
`Nat` or `String`. A family with an unbounded set of types (a type built by
recursion on a `Nat`) would keep `L2RBox`.
