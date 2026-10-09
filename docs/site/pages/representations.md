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
| `Nat` | `Nat`: one word, a *tagged handle* | small value `n` (below 2^63) is the word `2n+1`; a big value is a pointer to a big-number block |
| `Int` | `Int`: one word, the same scheme | small in the `int32` range |
| `UInt8/16/32/64`, `USize` | `u8/u16/u32/u64`, `u64` | 64-bit targets only |
| `Int8…Int64`, `ISize` | the unsigned words | signed operations on the bit pattern, as `lean.h` |
| `Float`, `Float32` | `f64`, `f32` | |
| `Char`, `Bool` | `u32`, `bool` | |
| `Unit`, `PUnit`, erased values, the IO world | `L2RUnit` | a one-variant `[value]` enum |
| `String` | `LStr`: one block | header (count, byte size, capacity, character count), then UTF-8 bytes |
| `Array α` | `RVec<LAny>`: one block | for every `α` without a storage kind: each element is a box |
| `Array S`, `S` a scalar | `RVec<u8>`, `RVec<u16>`, `RVec<u32>`, `RVec<u64>`, `RVec<f32>`, `RVec<f64>`: one block | the scalars inline ([compact arrays](#compact-arrays)) |
| `ByteArray`, `FloatArray` | `RVec<u8>`, `RVec<f64>` | `ByteArray.mk` and `.data` are the identity with a compact `Array UInt8`; with an array of boxes they copy the elements in one loop |
| `ST.Ref`, `IO.Ref` | one generated record around a Reussir `Cell` of a box | for every element type; updates seen through every alias |
| `Thunk α`, `Task α` | `LCell<S>` holding a generated state | for every `α`: the value is a box; memoized thunks, deferred tasks |
| `IO.Promise α` | `LPromise`, a runtime object | holds the cell of its task |
| handles, processes, mutexes, sockets | `LHandle`, a runtime object | closed with the last reference |
| inductive types, structures | one generated Reussir type per datatype | a field whose type is a parameter is a box; rules below ([dependent types](dependent-types.html#layouts-of-generic-types)) |
| function types | one generated enum per function type | [function values](#function-values) |
| a type not statically known (`lcAny`) | `LAny`, the box: one word | [the box](#the-box-lany); [dependent types](dependent-types.html) |

## Numbers

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
  box is a cell, as natively. An array of scalars is compact (next
  section). `ByteArray` and `FloatArray` hold raw bytes and floats.
- **Reads.** Reussir has no borrowed parameters, so each read of an array
  or string takes the container owned: an increment by the caller and a
  release in the runtime function. LLVM cancels the pair when nothing lies
  between them. Thus a read releases the container first: it gets a
  *view* of the container, then it checks the index, then it takes the
  element from the view. The last reference frees the container after
  the read.
- **Sets.** A set (or a pop) releases the element that it removes. For a
  record, only the decrement is inline, so LLVM inlines the set into the
  loop. When the set frees the last reference to a record, a call puts the
  record on the pending stack as one cell, and the free releases the record's
  fields last first, as Lean does. This costs about 74 instructions per
  freed record.
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
  program that casts has no compact arrays. In other programs, an array
  of a kind that fails the check holds boxes, as natively. The other kinds
  stay compact.
- **`Array.map`.** Lean's library maps an array in place through an
  array of boxes. lean2rr gives each such loop a typed copy at the element
  types of its call. When the two types are equal, the loop runs in place.
  Otherwise it writes a new array of the result's kind.
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
  have no padding (pass `field-order`). Reussir's own member packing is
  off.
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
  target. A wrong word is a panic, never a wrong read. With the optional
  pass `conv-liveness`, an unboxing function has arms only for the types
  that live code boxes.
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
