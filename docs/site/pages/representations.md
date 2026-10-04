# Representations

<p class="lead">How each Lean value is stored in a lean2rr build. Sources:
translation plan §5.1, the <a href="repo:runtime/README.md">runtime
README</a> ("Representations") and the implementation notes'
<a href="repo:docs/implementation/representations/README.md">representations</a> area.</p>

## The principle

Think of each Lean type as a Rust type. lean2rr gives every value a precise
type where the program determines it. Lean itself stores almost every value
as a pointer to a boxed object; lean2rr does that only where the type is not
statically known (the uniform type `L2RBox`).

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
| `Array α` | `RVec<S>`: one block | `S` is the *storage type* of `α` |
| `Array Nat`, `Array Int` | `LNatArr`, `LIntArr` (`TagVec`) | each element is the number's own word (pass `nat-arrays`) |
| `ByteArray`, `FloatArray` | `RVec<u8>`, `RVec<f64>` | `ByteArray.mk` and `.data` cost nothing |
| `ST.Ref`, `IO.Ref` | a generated record around a Reussir `Cell` | updates seen through every alias |
| `Thunk α`, `Task α` | `LCell<S>` holding a generated state | memoized thunks, deferred tasks |
| `IO.Promise α` | `LPromise`, a runtime object | holds the cell of its task |
| handles, processes, mutexes, sockets | `LHandle`, a runtime object | closed with the last reference |
| inductive types, structures | one generated Reussir type per instantiation | rules below |
| function types | one generated enum per function type | [function values](#function-values) |
| a type not statically known (`lcAny`) | `L2RBox` | [the uniform type](#the-uniform-type-l2rbox) |

## Numbers

{{svg:natword}}

`Nat` and `Int` use Lean's own encoding of small values. Reussir inserts the
reference counting, and normally it counts every handle at its address. A
small `Nat` has no address. Local Reussir patch 0050 adds *tagged opaque
handles*: Reussir counts such a handle only when its low bit is 0. So copying
or dropping a small value costs one bit test, as natively.

The prelude's functions take each argument as its raw word once
(`l2r_nat_raw`). Small values are computed inline; a big value or an
overflow calls the runtime, which uses GMP. Every value has exactly one
form: a value in the small range is always small. So two small words are
equal exactly when their values are equal.

{{svg:bigblock}}

A two-limb number takes 32 bytes here, and 56 bytes natively. A million
live two-limb numbers take 49.5 MB, 0.67× native.

## Strings and arrays

{{svg:lstr}}

{{svg:rvec}}

- **Copy-on-write.** A unique block is updated in place and grows with
  `mi_realloc`. A shared block is copied once, with room for the update.
- **Storage type.** An array element is stored in its own type when that
  type can cross Reussir's FFI boundary (integers, floats, `bool`, runtime
  handles, `Nat`, `Int`, shared records, function values). An enumeration
  is stored as its index (`u8`, `u16` or `u32`). Other values (`[value]`
  structs, Reussir closures) go in a one-field shared struct, `ElemBox`.
  Lean boxes array elements too.
- **Reads.** Reussir has no borrowed parameters, so each read of an array
  or string takes the container owned: an increment by the caller and a
  release in the runtime function. LLVM cancels the pair when nothing lies
  between them.

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

- **Relevant parameters only.** A type parameter that appears in no data
  field (a phantom, such as `EST.Out`'s world type) does not make a new type.
- **Field order.** Fields are sorted by decreasing alignment, so records
  have no padding (pass `field-order`). Reussir's own member packing is off,
  because its in-place reuse mishandled packed fields (Reussir bug 2).
- **Recursive and mutual types** refer to each other's instances.
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

## The uniform type `L2RBox`

{{svg:box}}

- `L2RBox` has one variant per concrete type that the program boxes, plus a
  unit variant. Stage 4 adds variants as it needs them.
- Unboxing is a generated function that accepts every variant that can hold
  a value of the target's Lean type. One Lean type can have several
  representations: `List Nat` and the uniform `List L2RBox`, or `LNatArr` and
  `RVec<L2RBox>` for an `Array Nat`.
- A conversion between two representations is structural: element by
  element for arrays and lists. Deep values convert with a loop and an
  explicit stack, not recursion.
- A converted value is a new, unshared object. Converting it back rebuilds
  it again. Only identity and sharing can tell the difference, and neither
  is preserved.
- A boxed unit unboxes to the *zero* of the target type. It is Lean's
  `box(0)` placeholder.

## Placeholders

Lean's library code sometimes stores `box(0)` into a slot that nobody reads
(for example `Array.modify`, so that the element stays unshared). lean2rr
gives such a placeholder the *zero* of the expected type: `0`, `false`, a
constructor without fields, else the first constructor whose fields have
zeros, an empty array or string. A type without a finite value (`Empty`) gets
`unreachable`, which never runs. A zero that would allocate is built once and
kept in a once-cell (pass `placeholder-cache`).

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
