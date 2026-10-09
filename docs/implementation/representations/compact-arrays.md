# Compact arrays

An `Array S` of a scalar `S` is stored compactly, `RVec<k>` of `S`'s
storage kind `k`, when the whole program allows it: optimization
`compact-arrays` (on by default; `--disable-opt compact-arrays` gives every
`Array α` the array of boxes of [arrays.md](arrays.md#an-array-holds-boxes-whatever-its-element-type)).
An array whose element type is not statically known stays an array of
boxes, as natively. Paths: `lean2rr/LeanToReussir/` for lean2rr's files,
`runtime/` for the runtime. Plan
[§5.1](../../translation-plan.md#51-type-translation).

Example. In `def f (a : Array UInt64) := a.push 1`, `a` is `RVec<u64>`:
8 bytes per element, no box, no cell for a value from 2^63. The same
program's `List.foldl` at an unknown `α` still sees boxes: a compact array
that it gets as an `α` is one box (kind 11), which it passes on unread.

### The storage kinds

- **What:** `scalarKind?` (Stage 3, the whole-program check) and
  `arrayKindOf` (the lowering) give an element type its storage kind:
  - `u8`: `UInt8`, `Bool` (its byte 0 or 1), and an enumeration with 1 to
    256 constructors (a `[value]` enum without fields; its constructor
    index);
  - `u16`: `UInt16`; `u32`: `UInt32`, `Char` (mono `UInt32`);
  - `u64`: `UInt64`, `USize`; `f32`: `Float32`; `f64`: `Float`.

  `lowerType` gives `Array S` the type `RVec<arrayStorage S>`: the kind
  when the program stores it compactly (`LowerCtx.compactKindsOn`), else
  `Box`. An extern over arrays takes the kind as its type argument
  (`lowerExternCall`: `lean_array_push<u64>`); a `Bool` goes into a byte by
  `lean_bool_to_uint8` and out by the generated `l2r_bool_of_u8`, an
  enumeration by `l2r_enum_index_T` and `l2r_enum_of_index_T`
  (`elemToStorage?`, `elemOfStorage?`). A box needs no conversion: its
  immediate is the byte, so `Array.mk` (from the list's boxes) and
  `Array.toList` unbox and box at the kind. A compact array in a box is
  leanrt's kind 7 to 12 (`boxKind`; [box-and-uniform.md](box-and-uniform.md#a-box-is-one-word-an-immediate-or-a-numbered-pointer)).
  `ByteArray.mk`/`data` and `FloatArray.mk`/`data` are the identity between
  a compact `Array UInt8` or `Array Float` and the runtime's bytes or floats
  (`customExtern`).
- **Why:** With rule 1 every `Array α` was an array of boxes: a `UInt64`
  from 2^63 and every `Float` was a cell, and a byte took 8 bytes. matrix
  (`Array UInt64`) ran 3.62x native's wall time (1.18x with the old
  per-type arrays), lean-zip's compression of the Silesia corpus peaked at
  1.9 GB (0.5 GB before rule 1, native 2.17 GB), the sieve of the classic
  programs at 485 MB. With compact arrays: lean-zip 512 MB (outputs equal
  native). Natively Lean's `Array UInt64` is an array of boxed objects; a
  scalar array of lean2rr is smaller.
- **Where:** `ArrayKinds.lean`: `scalarKind?`, `enumCtorCount?`;
  `LowerBase.lean`: `arrayKindOf`, `arrayStorage`, `lowerType`, `boxKind`,
  `elemToStorage?`, `elemOfStorage?`, `boolOfU8Fn`;
  `Lower/ExternCall.lean`: `lowerExternCall`, `customExtern`;
  `Lower/BoxedUses.lean`: `boxedArgMask`, `letValueBoxed` (an argument at
  an array's type parameter is a boxed position only when the array holds
  boxes).
- **Remove only if:** never (the optimization off removes it).

### The whole-program check turns a kind off

- **What:** `compactArrayKinds` (`CompactArrays.lean`) runs on the program
  the lowering gets. A value must keep one representation on its way, so a
  kind is turned off for the whole program (all its arrays are arrays of
  boxes, as without the optimization) when:
  - **a crossing:** at an argument and its parameter, a result and its
    binder, a jump, a return, a constructor argument and its field (as the
    layout has it), a field and its binder, or an extern's argument,
    `Array S` meets `Array T` of another kind or of none (`Array lcAny`,
    `Array Nat`), at any position of the two types (through function types
    and the arguments of one inductive; `alignArr`). `Array S` against a
    box (`lcAny`) is allowed: the box holds the compact array. In a box,
    `Array S` against `Array lcAny` (or an array of another type `Box`
    represents) is allowed too, for the same reason: in an inductive's
    type argument (rule 1 gives the inductive one layout, its type
    arguments in boxes) and in the element of an array of boxes, not under
    a function type (a function takes its arguments at their own
    representations) and not in a `flatten-structs` tuple (its fields are
    at their own types). The flow class (below) then turns the kind off if
    generic code can unbox the array as an array of boxes. Example (hunt
    HCA-02): `structure Matrix (α) where rows : Array (Array α)` has the
    field `Array (Array lcAny)` in its layout, and a `Matrix Float` stores
    an `Array (Array Float)` there; before, this turned `f64` off
    (`List (Array α)` at `UInt8`: `u8`, `Option (Array α)` at `UInt64`:
    `u64`). An extern's parameters and result keep the strict comparison
    (`alignArr`'s `strict`);
  - **a value without an array:** a binder bound to a constructor of
    Lean's applied to all its fields, each field erased or a binder that
    holds no array (`List.nil ◾`, `Option.none ◾`, `Except.error e` with
    `e : String`; `CAM.holdsNoArray`), is aligned nowhere and joins no
    class: no code can read an array from it, and its type has the one
    layout of its inductive, whatever the type arguments. Example (hunt
    HCA-01): mono CSE shares `let _x : List (Array UInt8) := List.nil ◾`
    (typed at its first use) with a use where `List (Array Float)` is
    expected; before, this turned `u8` and `f64` off. A constructor that
    the runtime implements (`Array.mk`: the kind decides its
    representation) and a `flatten-structs` tuple do not count;
  - **a flow class:** the places above join binders into classes
    (union-find, as rule 4's `flowAnalysis`), also through containers (a
    constructor's arguments and its value, a field and the value read),
    externs (all their arguments and their result: references, thunks,
    tasks, arrays of arrays) and function values (their arguments, their
    results, the parameters and results of their code). A class with a
    binder whose type mentions `Array lcAny` turns off every kind that its
    types mention: generic code may read its arrays as arrays of boxes. A
    position that is no binder, an extern's parameter or result (a
    constructor the runtime implements, `ByteArray.mk`, included) or a
    field as the layout has it, gets a node of its own in the class of the
    value there when its type mentions a storage kind (`posNode`): a box
    unboxed there at `Array UInt64` makes the class mention `u64` (review
    F1: an array of boxes from a type-code universe, `Ty.denote`, read by
    `Array.size` at `UInt64` was unboxed as a compact array; test
    `RtCArrDepUniverse`). Such a position also gets a node when its type
    is an array of boxes (`Array lcAny`) and a box arrives there (an
    argument of type `lcAny`): the box is unboxed there as an array of
    boxes, so the class mentions `Array lcAny` (test `RtCArrBoxedAny`: a
    `T b` that is an `Array UInt64`, read through a proved cast by
    `Array.size` at `lcAny`; before, `u64` stayed on and leanrt converted
    the array at each read);
  - **a cast:** the program can read a value as another type
    (`programCasts`): every kind is off. An axiom that states a `Bool`
    equation does not count (`isBoolEqAxiom`): `native_decide` and
    `bv_decide` add such axioms (lean-zip has them), and they prove no
    equation between types. An extern of the program does not count by
    itself: the Lean code that runs for it is walked as the rest of the
    program ([../externs-ffi/program-externs.md](../externs-ffi/program-externs.md#an-extern-of-the-program-is-not-a-cast-by-itself)).
    lean-zip's 12 externs turned every kind off until 2026-10-09 (test
    `RtCArrExtern`; `RtCastExternBody`: an extern whose definition casts).

  Only binders whose type can hold such an array are joined
  (`mayHoldArr`). `L2R_DEBUG=1` prints the kinds that stay on and, for each
  kind turned off, the first reason.
- **Why:** The lowering chooses the representation by type; nothing
  converts an array between `RVec<u64>` and `RVec<Box>` (that was rule 1's
  point: a conversion copies the array and loses its sharing and its
  in-place updates, review RV9C-02). A crossing would need such a
  conversion; a class that reaches `Array lcAny` would unbox a compact array
  as an array of boxes (the safety net, below) or the reverse (a panic).
  Examples: `RtCArrColumn` (a column whose element type depends on a value)
  and `RtCArrGeneric` (arrays through a generic function) stay boxed;
  `RtCArrCast` casts. A box needs no crossing: the value in it has one
  representation (the box) whatever its element type. Only the code that
  unboxes it chooses one, and that code is a binder or a position of the
  value's class. `RtCArrGenericFields` keeps every kind on (fields
  `Array (Array α)`, `List (Array α)`, `Option (Array α)`,
  `Array (List (Array α))`); in `RtCArrGenericFieldsDep`, generic code
  builds or reads such fields (type-code universes, an existential
  payload), and the classes turn those kinds off; `RtCArrSharedNil` keeps
  every kind on.
- **Where:** `CompactArrays.lean`: `compactArrayKinds`, `caCode`,
  `alignArr`, `boxArrayElem`, `CAM.holdsNoArray`, `mentions`,
  `mayHoldArr`; `Lower/Conv.lean`: `programCasts` (`ignoreAxiom`),
  `isBoolEqAxiom`; `Emit/Program.lean`: `lowerProgram`.
- **Remove only if:** never while arrays have two representations.

### A field `Array α` of an inductive used with a compact array is a box

- **What:** Rule 1 gives an inductive one layout, its fields at `lcAny`
  parameters: `Subarray.array`, `Vector.toArray` and a user's `structure
  Column (α) where data : Array α` are `Array lcAny` there, an array of
  boxes. When some binder type of the program instantiates such a field
  with a scalar array (`Subarray UInt64`, from `a[1:4]` on an
  `Array UInt64`; in any declaration, reached or not), the field is a `Box` instead (`arrayFieldInductives`,
  `LowerCtx.boxedArrayFields`, `nominalType`): the box holds the compact
  array (kind 11) or an array of boxes (kind 6), and a read unboxes it at
  the binder's type. The check (`caFieldTypes`) sees the field as `lcAny`.
- **Why:** The field `Array lcAny` meets every compact array stored in it
  (a crossing): `RtCArrKinds` turned every kind off through
  `Array.toSubarray` before. A box costs a tagged pointer at the store and
  a number test at the read (no allocation), only in such inductives. A
  field that holds arrays inside another type (`Array (Array α)`,
  `List (Array α)`) needs no change: its arrays are in boxes already (see
  "a crossing" above).
- **Where:** `CompactArrays.lean`: `arrayFieldInductives`,
  `isArrayAnyField`, `caFieldTypes`; `LowerBase.lean`: `nominalType`.
- **Remove only if:** the layouts of generic types change.

### The loops of `Array.map` are typed (`Opt/SplitMapLoops.lean`)

- **What:** Stage 3 gives each loop of `Array.mapMUnsafe` and
  `Array.mapFinIdxMUnsafe` (`isMapLoop`) a typed instance at the element
  types of its entry call, when one of them has a storage kind or holds a
  scalar array (`holdsCompactKind`: `Array (Array UInt8)`): in place
  (`α = β`: the loop with its array typed `Array α`, entered at any index)
  or split (`α ≠ β`, entered at index 0: the source `Array α` is read,
  each value pushed onto a new `Array β` made at the source's size; a
  source of scalars gets no placeholders, so a shared source is not
  copied). The externs of the instance are instances at `α` and `β`
  (`externInstance`). The stored type `β` is the type Stage 3 gives the
  stored values, or `Array γ` for the result of an inner typed `map`
  (`a.map (·.map f)`), or else `α` (the identity map stores the values it
  reads at `lcAny`); a value whose type was unknown is checked once the
  instance is typed (`typedStoresOk`), after the `map` loops entered in
  its body are typed too. Rounds of Stage 3's fixpoint and the typing
  alternate until a round types no new loop (`retypeMono`, at most 12): the
  result of one `map` can be the source of the next, and a loop that could
  not be typed in one round is tried again in the next.
- **Why:** These loops cast the array to `Array NonScalar` (mono
  `Array lcAny`), a crossing at every `map` of a scalar array. They are the
  only code of Lean's library that reads an array at another element type
  (the research behind this design counted every crossing in matrix,
  lean-zip and the classic programs). The split loop was lean2rr's before
  rule 1 (74ad8b5). `L2R_DEBUG_MAPLOOPS=1` prints each loop that stays
  untyped and why.
- **Where:** `Opt/SplitMapLoops.lean`: `loopShape?`, `letCalls`,
  `ensureSplit`, `buildSplit`, `splitCode`, `splitEntries`, `usizeZeros`
  (a zero passed through chains of join points, to a fixpoint),
  `typedStoresOk`, `splitMapLoops`; `MonoRetype.lean`: `Stage3Config`,
  `retypeMono`, `externInstance`; `ArrayKinds.lean`: `holdsCompactKind`.
  Tests `RtCArrMaps`, `RtCArrInPlace`, `RtCArrContainers`.
- **Remove only if:** the optimization is off (the loops stay over boxes,
  and the check keeps their kinds boxed).

### Parameters typed `Array lcAny` are typed from their callers

- **What:** In each round of Stage 3's fixpoint, a parameter whose type
  holds `Array lcAny` gets the type every live caller passes there, when
  that type holds a compact array (`holdsCompactKind`) and the callers
  agree (a partial application that supplies the argument counts; one that
  leaves the parameter open, or a reference to the declaration as a value,
  blocks it). The body is retyped with the assumption, which stays only if
  the declaration's own calls pass that type too (`selfCallsAgree`). A
  `map` loop's own array is left to the typed loops; another `Array lcAny`
  parameter of a `map` loop (an array its function captured) is typed here.
- **Why:** Lean types such a parameter `Array lcAny` when the array comes
  from `Array.map` (`NonScalar`): a continuation lifted out of the code
  that maps (`IO.asTask (return a.map f)`), or a captured array. Stage 3
  types a binder only from what flows into it, which for a parameter is
  every caller; without this, the parameter is a crossing (`RtCArrContainers`,
  `RtCArrAttach`). It was Stage 3's `paramsFromCallers` before rule 1.
- **Where:** `Opt/SplitMapLoops.lean`: `arrayParamsFromCallers`,
  `arraySites`, `selfCallsAgree`; `MonoRetype.lean`:
  `Stage3Config.paramsFromCallers`, `retypeMono`.
- **Remove only if:** the optimization is off.

### The check sees only the reachable code

- **What:** `compactArrayKinds` walks the declarations the entry point
  reaches (`roots`, the initializers; through every constant a body
  names). A declaration nothing reaches can keep a crossing (a wrapper
  whose worker's parameter Stage 3 typed from the worker's callers): the
  lowering prints `no representation conversion` for it and gives it a
  panic that never runs (`conv-liveness` drops the function).
- **Why:** Dead wrappers would otherwise turn kinds off (`RtCArrKinds`,
  `RtCArrAttach`).
- **Where:** `CompactArrays.lean`: `compactArrayKinds`.
- **Remove only if:** never.

### The safety net: an array of scalars unboxed as an array of boxes is converted

- **What:** leanrt converts a box of kind 7 to 12 unboxed at `RVec<LAny>`
  into a new array of boxes ([box-and-uniform.md](box-and-uniform.md#an-array-of-scalars-unboxed-as-an-array-of-boxes-is-converted-the-safety-net-of-compact-arrays)).
  With `L2R_DEBUG_ARRAY_CONVERT` set, each conversion writes `leanrt:
  compact array of kind N converted to boxes (L elements)` to standard
  error. The reverse (an array of boxes unboxed at a compact kind) stays a
  panic.
- **Why:** The whole-program check should make it unreachable; the net
  keeps a miss correct (a copy) instead of a panic. The compact-array tests
  run with the variable set and compare standard error with native's, so
  a conversion fails them.
- **Where:** `runtime/leanrt/src/any.rs`: `boxes_of_compact`;
  `runtime/leanrt/src/array.rs`: `boxes_of_scalars`.
- **Remove only if:** never.

### Alternatives considered

- **A run-time element tag.** OCaml's float arrays carry a tag
  (`Double_array_tag`) that polymorphic code tests at each access
  ([OCaml manual, "Interfacing C with OCaml"](https://ocaml.org/manual/intfc.html));
  V8 and JavaScriptCore keep an element kind per array and change it when
  a value of another kind is stored ([V8: "Elements kinds"](https://v8.dev/blog/elements-kinds));
  PyPy's storage strategies do the same for lists ([Bolz, Diekmann,
  Tratt, OOPSLA 2013](https://doi.org/10.1145/2509136.2509531)). Not
  chosen: the tag test costs every access in every program, and lean2rr
  knows the element types statically.
- **Separate types with conversions.** GHC's unboxed vectors
  (`Data.Vector.Unboxed`, [vector](https://hackage.haskell.org/package/vector))
  and .NET's generics, which instantiate each value type apart (Kennedy and
  Syme, PLDI 2001), keep a scalar container a type of its own. lean2rr did
  this before rule 1: an array read at another element type was converted,
  which copies it and loses its sharing (quadratic in a loop of updates,
  RV9C-02).
- **Type metadata.** Swift passes type metadata to generic code, which then
  reads values of any layout ([Swift ABI: type metadata](https://github.com/swiftlang/swift/blob/main/docs/ABI/TypeMetadata.rst)).
  Not chosen: generic code would need a size or layout parameter at run
  time, a change of Reussir's code generation.
- **Possible extension:** a tag only on the arrays that reach generic code
  (a kind turned off today), if a program ever needs compact arrays there.
