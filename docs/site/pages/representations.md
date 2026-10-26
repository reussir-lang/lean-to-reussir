# Representations

<p class="lead">How each Lean value is stored in a lean2rr build. Sources:
translation plan §5.1, the <a href="repo:runtime/README.md">runtime
README</a> ("Representations") and the implementation notes'
<a href="repo:docs/implementation/representations/README.md">representations</a> area.</p>

## The principle

Think of each Lean type as a Rust type. lean2rr gives every value a precise
type where the program determines it. Lean itself stores almost every value
as a pointer to a boxed object. lean2rr does that only in a generic
position: where the type is not statically known, and in a field, an array
element or a cell whose type is a parameter. There a value is a *box*
(`LAny`): one word, as Lean's `lean_object*`.

Reussir does the reference counting. A *shared* type lives in a counted
heap cell. A *`[value]`* type is stored inline and is never allocated.

## The table

| Lean | lean2rr build | Notes |
|---|---|---|
| `Nat` | `Nat`: one word, Reussir's built-in integer | a value in [-2^61, 2^61) is in the word; a bigger value is a pointer to a counted big integer. With `--int-backend leanrt`: a *tagged handle*, a small value `n` (below 2^63) is the word `2n+1` ([numbers](#numbers)) |
| `Int` | `Int`: one word, Reussir's built-in integer | the same scheme. With `--int-backend leanrt`: small in the `int32` range |
| `UInt8/16/32/64`, `USize` | `u8/u16/u32/u64`, `u64` | 64-bit targets only |
| `Int8…Int64`, `ISize` | the unsigned words | signed operations on the bit pattern, as `lean.h` |
| `Float`, `Float32` | `f64`, `f32` | |
| `Char`, `Bool` | `u32`, `bool` | |
| `Unit`, `PUnit`, erased values, the IO world | `L2RUnit` | a one-variant `[value]` enum |
| `String` | `LStr`: one block | header (count, byte size, capacity, character count), then UTF-8 bytes |
| `Array α` | `RVec<LAny>`: one block | for every `α` without a storage kind: each element is a box |
| `Array S`, `S` a scalar | `RVec<u8>`, `RVec<u16>`, `RVec<u32>`, `RVec<u64>`, `RVec<f32>`, `RVec<f64>`: one block | the scalars inline ([compact arrays](#compact-arrays)) |
| `Array X`, `X` a record, an enum with fields, `Nat`, `Int`, `String` or an array | `RVec<T>` of `X`'s own type: one block | the pointers without boxes ([typed arrays](#typed-arrays)) |
| `ByteArray`, `FloatArray` | `RVec<u8>`, `RVec<f64>` | `ByteArray.mk` and `.data` are the identity with a compact `Array UInt8`; with an array of boxes they copy the elements in one loop |
| `ST.Ref`, `IO.Ref` | a generated record around a Reussir `Cell`: of the element's own type, or of a box | updates seen through every alias ([typed references](#typed-references)) |
| `Thunk α`, `Task α` | `LCell<S>` holding a generated state | for every `α`: the value is a box; memoized thunks, deferred tasks |
| `IO.Promise α` | `LPromise`, a runtime object | holds the cell of its task |
| handles, processes, mutexes, sockets | `LHandle`, a runtime object | closed with the last reference |
| inductive types, structures | one generated Reussir type per datatype | a field whose type is a parameter is a box; rules below ([dependent types](dependent-types.html#layouts-of-generic-types)) |
| function types | one generated enum per function type | [function values](#function-values) |
| a type not statically known (`lcAny`) | `LAny`, the box: one word | [the box](#the-box-lany); [dependent types](dependent-types.html) |

## Numbers

`Nat` and `Int` have two representations. The option `--int-backend`
selects one (the scripts read `L2R_INT_BACKEND`):

- `rcgmp`, the default since 2026-10-25: Reussir's built-in integers.
- `leanrt`, the default until 2026-10-25: Lean's own one-word encoding,
  with lean2rr's runtime for the big values.

Both representations give the same results. The prelude keeps the code of
the two representations in marked blocks, and lean2rr keeps only the
blocks of the selected one. Each function has the same name and signature
in the two blocks, so the generated code calls the same functions.

### Reussir's built-in integers (`rcgmp`)

A `Nat` or `Int` is one word. A value in [-2^61, 2^61) is stored in the
word itself. Any other value is a pointer to a counted big integer of
Reussir's runtime, which uses GMP. Reussir does the reference counting.
An operation on two small values is inline code, and LLVM can fold it.
Only a big operand or an overflow calls the runtime. The prelude composes
Lean's rules (for example `n - m = 0` when `m > n`, and `n / 0 = 0`) from
Reussir's operators.

- **Case splits.** A case split on a `Nat` or `Int` (`0` and `n+1`,
  `ofNat` and `negSucc`, a chain of tests against literals) becomes one
  Reussir `match` on the integer (pass `int-match`).
- **Literals.** A literal of any size is a constant of the program, with
  no cell to fill at startup.
- **Boxes.** In a box, a `Nat` or `Int` keeps Lean's words: a `Nat`
  below 2^63 is the word `2n+1`. A bigger value is a runtime cell that
  holds the integer.
- **Indices.** A read at a `Nat` index (an array, a byte array, a string
  position) first makes the index a 64-bit word, and then reads at that
  word.

### Lean's one-word encoding (`leanrt`)

Status: planned: the removal of this representation.

{{svg:natword}}

`Nat` and `Int` use Lean's own encoding of small values. Reussir inserts the
reference counting, and normally it counts every handle at its address. A
small `Nat` has no address. So `Nat` and `Int` are *tagged opaque
handles*: Reussir counts such a handle only when its low bit is 0. Copying
or dropping a small value costs one bit test, as natively.

The prelude's functions take each argument as its raw word once
(`l2r_nat_raw`). Small values are computed inline; a big value or an
overflow calls the runtime, which uses GMP. Every value has exactly one
form: a value in the small range is always small. So two small words are
equal exactly when their values are equal, and a small `Int` is never
equal to a big one. So the equality of a small and a big `Int` does not
call the runtime. Builds with debug assertions check the rule where the
runtime makes a big `Int` and where it reads one.

One small set of prelude helpers knows the encoding. They test a word
(`l2r_nat_word_is_small`), read the value of a small word
(`l2r_nat_word_val`) and make a small value (`l2r_nat_small`), with the
same helpers for `Int`. The other prelude functions and the generated code
use only these helpers. They never use bit operations on a `Nat` or `Int`
word. Only the prelude's `Nat` and `Int` functions also calculate on the
words, for speed. The runtime has its own copy of the helpers. The
translator knows only which values are small (a `Nat` below 2^63, an
`Int` in the `int32` range). A different representation of numbers
changes only these places.

{{svg:bigblock}}

A two-limb number takes 32 bytes here, and 56 bytes natively. A million
live two-limb numbers take 49.5 MB, 0.67× native. The capacity of a block is
the whole mimalloc block. Up to 64 bytes (six limbs) the runtime knows that
size without asking mimalloc: there, mimalloc's sizes are all multiples of 8.

## Strings and arrays

{{svg:lstr}}

{{svg:rvec}}

- **Copy-on-write.** A unique block is updated in place and grows with
  `mi_realloc`. A shared block is copied once, with room for the update.
- **Elements.** An `Array α` holds boxes, as Lean's array holds
  `lean_object*` words. A small `Nat` is the word itself. A `Float` in a
  box is a cell, as natively. An array of scalars is compact, and an
  array of records, numbers, strings or arrays can be typed (next
  sections). `ByteArray` and `FloatArray` hold raw bytes and floats.
- **Reads.** Reussir has no borrowed parameters, so each read of an array
  or string takes the container owned: an increment by the caller and a
  release in the runtime function. LLVM cancels the pair when nothing lies
  between them. Thus a read releases the container first: it gets a
  *view* of the container, then it checks the index, then it takes the
  element from the view. The last reference frees the container after
  the read.
- **Sets.** A set (or a pop) releases the element that it removes. For a
  boxed record, only the decrement is inline, so LLVM inlines the set into
  the loop. When the set frees the last reference to a boxed record, a
  call puts the record on the pending stack as one cell, and the free
  releases the record's fields last first, as Lean does. This costs about
  74 instructions per freed record. A record in a typed array is released
  by its own drop, through a call out of line.
- **String equality.** Strings of different lengths are not equal. Two
  references to the same string are equal. Other strings compare their
  bytes.

## Compact arrays

An array whose element type is a scalar holds the scalars inline. The
element type gives the *storage kind*:

| Element type | Storage kind | Bytes per element |
|---|---|---|
| `UInt8`, `Bool` (0 or 1), an enumeration with at most 256 constructors (its index) | `u8` | 1 |
| `UInt16` | `u16` | 2 |
| `UInt32`, `Char` | `u32` | 4 |
| `UInt64`, `USize` | `u64` | 8 |
| `Float32` | `f32` | 4 |
| `Float` | `f64` | 8 |

The figure above shows an `Array UInt64` as `RVec<u64>`.

- **The rule.** One check looks at the whole program, once for each
  storage kind. A kind is compact when no value of an array of that kind
  can reach code that reads the array as an array of boxes. Generic code
  reads arrays so: an `Array α` whose `α` is not statically known. A
  program that casts has no compact arrays. A program casts when code
  that it reaches outside Lean's library is `unsafe`, or uses `sorry` or
  an axiom. An axiom that Lean adds for a proof by native evaluation
  (`native_decide`, `bv_decide`) is not a cast when the code that Lean
  ran for it is the code of the definitions. An extern of the program is not a cast: lean2rr examines the
  Lean code that runs for it, as all other code (see
  [the extern rule](index.html#the-extern-rule)). In other programs, an
  array of a kind that fails the check holds boxes, as natively. The other
  kinds stay compact.
- **`Array.map`.** Lean's library maps an array in place through an
  array of boxes. lean2rr gives each such loop a typed copy at the element
  types of its call. When the two types are equal, the loop runs in place.
  Otherwise it writes a new array of the result's kind.
- **A `match` on an array.** `match a with | ⟨l⟩ => …` takes the array
  at its own kind: `l` is a `List α`, and the call that makes it reads the
  compact array. A list holds boxes, so each `Float` of `l` is a new box,
  as with `a.toList`. For a byte array or a float array, `⟨arr⟩` is the
  compact `Array UInt8` or `Array Float` itself, with no copy.
- **Fields.** A structure field `Array α` (`Subarray.array`) holds a box
  when the program uses that structure with a compact array. The box holds
  the compact array or an array of boxes. A field that holds arrays inside
  another type (`rows : Array (Array α)`, `xs : List (Array α)`) holds
  them in boxes already. Its arrays can be compact with no change.
- **Values without arrays.** An empty list or `none` holds no array. One
  such value can go where lists of arrays of different kinds are expected.
- **Boxes.** A compact array in a box is one word with the kind's number
  (7 to 12). If generic code ever unboxes it as an array of boxes, the
  runtime converts it (a copy). The check makes this unreachable.
- **Example.** `def f (a : Array UInt64) := a.push 1` stores 8 bytes per
  element in `RVec<u64>`, and `1` is the word itself. A generic
  `List.foldl` that gets the array as an `α` passes one box.

Status: a tag for the arrays that reach generic code is a possible later
extension.

## Typed arrays

An array whose element type is a one-word counted type holds the
elements themselves, without boxes: `RVec<T_Body>` for an `Array Body`,
`RVec<Nat>`, `RVec<LStr>`, `RVec<RVec<Nat>>`. A read gives the element
without a test of a box's type, and a write stores it without a tag
(pass `typed-arrays`, which extends `compact-arrays`).

- **Kinds.** All instances of one inductive type have one kind
  (`List Nat` and `List String` are both `T_List`). `Nat`, `Int` and
  `String` have a kind each. An array of arrays has the kind of its
  element's kind.
- **The rule.** The same whole-program check as for compact arrays,
  once for each kind: a kind is typed when no array of that kind can
  reach code that reads it as an array of boxes. Function types, thunks,
  tasks, handles and references have no kind.
- **Releases.** The runtime releases the elements of a typed array in
  another order than Lean when elements are shared. Thus a kind is typed
  only when its elements can hold nothing whose release the program can
  see: no closure, no box, no handle, no task, no reference.
- **Example.** In n-body, `Array Body` is `RVec<T_Body>`. The program
  runs about 18% fewer instructions than with boxes.

Status: a conversion for a typed array that generic code unboxes as an
array of boxes (now a stop with a message) is a possible later extension.

## Typed references

The cell of a reference holds the element itself when the element type
has a *cell kind*: `L2RRef_N(Cell<T_Pt>)` for an `IO.Ref Pt`,
`Cell<Nat>`, `Cell<LStr>`, `Cell<RVec<Nat>>`. A `set` stores the value
without a box, and a `take` (in `modify`) gives it back without a test of
a box's type (pass `typed-cells`). Each cell type has its own record
type. Other references keep one record type whose cell holds a box.

- **Kinds.** A record or an enum with fields (all instances of one
  inductive type have one kind), `Nat`, `Int`, `String`, an array (its
  kind follows how the program stores the array's elements), and the
  scalars that a box holds in its word: `Bool`, `UInt8`, `UInt16`,
  `UInt32`, `Char`, `Float32`. `UInt64` and `Float` have no kind: their
  box can need a heap cell, and `get` gives the value in the box field of
  the IO result.
- **The rule.** Mono code gives every reference the type `lcAny`, so a
  reference always goes in a box, and each operation takes the reference
  out of the box at its own record type. The check compares the six
  primitives: `mkRef` (a *make*) and `get`, `set`, `swap`, `take`,
  `ptrEq` (the *operations*), each at the element type of its instance.
  When a make and an operation can have the same type (`lcAny` can be
  every type), they must use the same representation. Otherwise both kinds
  use boxes. So an operation at `lcAny` (the reference of an existential
  package) makes every kind use boxes. In a program that casts, every
  kind uses boxes.
- **Releases.** When the reference goes, Reussir releases the value in
  the cell in its own field order. Thus a kind is typed only when its
  values can hold nothing whose release the program can see: no closure,
  no box, no handle, no task, no reference.
- **`take`.** A typed cell gets the zero of its type (a constant, or a
  value built once), where a cell of boxes gets `box(0)`. The value taken
  out is not shared, so `modify` changes an array or a string in place.
- **Example.** In `r.modify fun p => { p with n := p.n + 1 }` with
  `r : IO.Ref Pt`, the record goes out of the cell and back into it with
  no box.

Status: typed cells for thunks, tasks and promises are a possible later step.

## Records and enums

lean2rr chooses the shape of each inductive type from its constructors:

| Shape of the Lean type | Reussir type | Allocation |
|---|---|---|
| no relevant fields in any constructor (`Ordering`) | `enum [value]` | none |
| one constructor with one relevant field (`ST.Out`) | `[value]` struct: the field itself | none (pass `value-structs`) |
| one constructor | shared `struct` | one cell |
| several constructors | shared `enum` | one cell per value; none for a constructor without fields |

{{svg:records}}

Other rules:

- **One type for each datatype.** A field whose type is a parameter is a
  box. `Option Nat` and `Option α` are one type, and a value goes from one
  to the other as it is.
- **Field order.** Fields are sorted by decreasing alignment, so records
  have no padding (pass `field-order`). The tuples that lean2rr makes
  (the arguments of a join point, the fields of a flattened result) are
  sorted the same way. The tuple of a flattened result also keeps a
  narrow value (a `Bool`, `UInt8`, `UInt16`, `UInt32` or `Char`) in a
  64-bit word and has no member for a `Unit` value, so it has no padding.
  Reussir's own member packing is off. A value struct is stored in place, so its
  alignment is the largest alignment of its fields: a value struct of a
  `UInt8` has alignment 1, and goes after the 8-byte fields.
- **Recursive and mutual types** refer to each other's types.
- **Computed fields** (`Lean.Name`): the implementation type `T._impl`, as
  in Lean's runtime.
- **Proofs** have no representation.

### An example

The [implementation status](repo:docs/implementation-status.md) ("An example")
shows a full program and its output. Its type:

```lean
inductive Tree where
  | leaf
  | node (l : Tree) (key : Nat) (r : Tree)
```

- Line 1: `Tree` is a new inductive type.
- Line 2: the constructor `leaf` has no fields.
- Line 3: the constructor `node` has a left subtree, a `Nat` key and a right subtree.

In Rust terms: `enum Tree { Leaf, Node(Rc<Tree>, Nat, Rc<Tree>) }`. lean2rr
generates:

```rust
enum T_Tree_346 {                 // shared: one counted cell per node
    c_leaf,                       // no fields: an immediate, never allocated
    c_node(T_Tree_346, Nat, T_Tree_346)
}
```

## The box `LAny`

{{svg:box}}

[Dependent types](dependent-types.html) shows where the box comes from,
with examples, and what it costs.

- A box is one word. An odd word is an immediate: a small scalar, an
  enumeration's index, a constructor without fields, a small `Nat` or
  `Int`. An even word is a pointer to a counted object, with the object's
  type number in its top 16 bits.
- A `Float` and a `UInt64` from 2<sup>63</sup> go into a cell, as natively.
  A `[value]` struct of several fields goes into a one-field cell
  (`ElemBox`).
- To unbox, the code checks the word against the type number of the
  target. A wrong word is a panic, never a wrong read. At a program type,
  the test for a pointer of the target's number and the take are in line;
  the rest (an immediate, another number) is a call of one function per
  target type, `l2r_unbox_rest_T`, which rrc puts back in line. With the optional pass `conv-liveness`,
  an unboxing function has arms only for the types that live code boxes.
- In a program that casts, a box can hold any word. The unboxing then
  reads an immediate as native Lean reads that word: a `Bool` is its low
  byte, nonzero (256 is `false`); an enumeration's index is masked to the
  enumeration's storage width; an index past the last constructor gives
  the last constructor when that one has no fields. At a `[value]` struct,
  a box that holds another inductive's object goes to the struct's cast
  function.
- No value of a datatype, array, thunk, task or reference is converted: each
  has one type. A function type has several representations (`Nat -> Nat`
  and `LAny -> LAny`), so a function value can be wrapped for another
  representation. A cast between two different inductives whose layouts
  differ rebuilds the value.
- The unit and Lean's `box(0)` are the word 1. `box(0)` unboxes to the
  *zero* of the target type.
- The program releases its own types: lean2rr generates a release function
  for each type number, and the runtime calls it for the last reference.

## Placeholders

Lean's library code sometimes stores `box(0)` into a slot that nobody reads
(for example `Array.modify`, so that the element stays unshared). lean2rr
gives such a placeholder the *zero* of the expected type: `0`, `false`, a
constructor without fields, else the first constructor whose fields have
zeros, an empty array or string. A type without a finite value (`Empty`) gets
`unreachable`, which never runs. A zero that would allocate is built once and
kept in a once-cell (pass `placeholder-cache`). A placeholder that goes into
a box is `box(0)` itself, as natively: the box does not hold a zero.

A constant that goes into a box, where the box needs a heap cell (a `Float`,
a `UInt64` from 2^63), is boxed once and kept in a once-cell, as native
Lean's `_boxed_const` (pass `boxed-consts`). For example, the default of
`a[i]!` on an `Array Float` is the constant `instInhabitedFloat`: no read
allocates.

## Function values

{{svg:fnvalues}}

A function value is data, not a Reussir closure. Applying a shared Reussir
closure copies it, and curried application allocates per argument. With
generated enums, applying a known target is a direct call, and the dispatch
is a `match` that LLVM can inline. In a prototype, 10⁸ calls of shared
function values took 0.09 s this way and 0.55 s with Reussir closures.

## Thunks, tasks and references

{{svg:lazy}}

{{svg:refs}}

## Identity

lean2rr does not copy native pointer identity. `ptrAddrUnsafe x` answers:

- for a heap value: the address of its cell;
- for a `Nat` or `Int`: its own word, which is native Lean's;
- for `UInt8/16/32`, `Char`, `Bool`, an enumeration: the word `2n+1`;
- for `UInt64`, `Float`, `Float32`: their bits;
- for a `[value]` struct: its field's answer.

For two values alive at the same time, equal answers mean the same cell or
equal values. So `ptrEq` answering `true` still means equal values, which
code that uses it as a shortcut needs. `ST.Ref.ptrEq` is exact. See
[Known differences](differences.html#identity-and-sharing).
