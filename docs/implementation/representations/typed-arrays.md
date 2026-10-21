# Typed arrays

An `Array X` of a one-word counted type `X` (a shared record or enum,
`Nat`, `Int`, `String`, another array) is stored typed, `RVec<T>` of `X`'s
own Reussir type `T`, when the whole program allows it: optimization
`typed-arrays` (on by default; it extends `compact-arrays` and needs it;
`--disable-opt typed-arrays` gives such arrays boxes again, as in
[arrays.md](arrays.md#an-array-holds-boxes-whatever-its-element-type-unless-it-is-compact)).
This is clean step B1 of the plan to use only Reussir's interface. Paths:
`lean2rr/LeanToReussir/` for lean2rr's files, `runtime/` for the runtime.

Example. In n-body (`structure Body` of seven `Float`s, `Array Body`
updated by `set!` and `modify`), the array is `RVec<T_Body>`: a read gives
the record without a test of a box's type number, a write stores it
without a tag. With the runtime's release of a replaced record by its own
drop (below), the program runs 493 M instructions instead of 602 M
(cachegrind, SVE-free build).

### The pointer kinds

- **What:** A pointer kind names the Reussir type that the lowering gives
  an element type, so that two element types of one kind have one
  representation (`ArrayKinds.lean`: `ptrKind?`, `elemKind?`,
  `sharedInductive?`):
  - `Nat`, `Int`: `Nat`, `Int` (their words, `RVec<Nat>`);
  - `LStr`: `String`;
  - `I:<name>`: an inductive that the lowering makes a shared record or
    enum (rule 1 gives `List Nat` and `List String` the one type
    `T_List`): not a proposition, a relevant field in some constructor
    (else it is an enumeration, the storage kind `u8`), and not one
    constructor with exactly one relevant field (a `[value]` struct under
    `value-structs`; such a structure is never typed);
  - `A(<k>)`: an `Array Y`, where `k` is `Y`'s kind (a storage kind or a
    pointer kind), or `box` when `Y` has none (`RVec<RVec<…>>`).

  Function types, `ByteArray`, `FloatArray`, thunks, tasks, handles,
  references, `lcAny` and the types that are no inductive (runtime
  objects, promises) have no pointer kind (`noPtrKindTypes`), and neither
  has an enumeration of more than 256 constructors (no storage kind
  either: it is a `[value]` enum of a 16- or 32-bit index). The lowering
  gives `Array X` the type `RVec<T>` when `X`'s pointer kind is on
  (`LowerCtx.typedKindsOn`, `arrayStorage`, `arrayPtrKindOf`). An extern
  over arrays takes `T` as its type argument (`lean_array_push<T_Body>`),
  so its values pass as they are: no box, no conversion. `Array.mk` and
  `Array.toList` unbox and box the list's heads at `T`.
- **Why:** Rule 1 gave every other array boxes: each read tested the box's
  type number and each write tagged the pointer, and the replaced or
  removed boxes went through the box's release. Natively the element is a
  `lean_object*` read without a test.
- **Where:** `ArrayKinds.lean`; `LowerBase.lean`: `arrayStorage`,
  `arrayPtrKindOf`, `LowerCtx.typedKindsOn`, `LowerState.ptrKindCache`;
  `Emit/Program.lean`: `lowerProgram`; `Opt/Registry.lean`: `typed-arrays`
  (installed before `compact-arrays`, whose hooks read its switch,
  `PassConfig.typedArrays`).
- **Remove only if:** the box becomes a Reussir type with arrays of it as
  cheap as typed ones (clean step C), or never.

### The whole-program check of compact arrays decides the pointer kinds too

- **What:** `compactArrayKinds` (`CompactArrays.lean`, with `ptr`) treats
  a pointer kind as it treats a storage kind
  ([compact-arrays.md](compact-arrays.md#the-whole-program-check-turns-a-kind-off)):
  a crossing between arrays of two kinds (`Array Point` against
  `Array lcAny`), a flow class that holds `Array lcAny`, or a program that
  casts turns the kind off for the whole program. Two element types of one
  kind meet without a crossing (`Array (List Nat)` against
  `Array (List lcAny)`: one type, `RVec<T_List>`); what they hold is
  compared as they hold it, an inductive's type arguments in boxes
  (`alignArr`). Where the kinds of two arrays differ and one is a pointer
  kind, both go off, and their elements are then compared as values in
  boxes (`Array (Array Point)` against `Array (Array String)` still turns
  `I:Point` and `LStr` off). The kinds seen are those of the array types
  the check meets; a kind it never sees stays boxed. The pointer kinds
  come from a second run of the check; the storage kinds still come from
  the first run, without pointer kinds (`compactArrayKinds`,
  `compactArrayKindsRun`). In the second run more binders join flow
  classes (a binder joins only when its type can hold an array of a kind,
  and `Array Nat` now can), so its classes are larger: in lean-regex they
  turned `u32` off, which stays on without typed arrays. Its decisions are
  sound for the first run's kinds: an `Array (Array S)` against an
  `Array (Array lcAny)` turns both pointer kinds (`A(s)`, `A(box)`) off,
  so the outer arrays hold boxes where the first run assumed boxes.
  `L2R_DEBUG=1` prints `lean2rr: typed arrays: …` with the kinds that
  stay on and, for each kind seen and turned off, the first reason.
- **Why:** The lowering chooses the representation by type; nothing
  converts an array between `RVec<T>` and `RVec<Box>` (a conversion would
  copy the array and lose its sharing and its in-place updates). Generic
  code that still reaches `lcAny` after lean2rr's instantiation (an
  existential package, a type-code universe, polymorphic recursion, a
  `NonScalar` map loop that cannot be typed) keeps such arrays boxed.
- **Where:** `CompactArrays.lean`: `CAM.kindOf` (records the element types
  of each pointer kind), `CAM.scalarOf`, `alignArr`, `mentions`,
  `mayHoldArr`, `compactArrayKinds`, `compactArrayKindsRun`, `CAResult`. Tests `RtTArrGeneric`
  (generic code: every kind off), `RtTArrMixed` (typed and boxed kinds in
  one program), `RtTArrKinds`, `RtTArrInPlace` (`.l2r-debug` files list
  the kinds).
- **Remove only if:** never while arrays have two representations.

### Only elements whose releases cannot be observed are typed

- **What:** A pointer kind is also turned off when one of its element
  types can reach a value whose release the program can observe
  (`releaseUnsafe?`): a function type (a closure holds what it captured),
  `lcAny` (a box holds a value of any type; a handle, a mutex or a promise
  is `lcAny` in mono code), a handle, a task, a thunk, a reference, or a
  type that is no inductive. The walk follows an array's element type and
  an inductive's constructor fields at the instance's arguments
  (`ctorFieldTypes`); a type whose constructors' fields cannot be
  computed there (not its inductive applied to its parameters) is refused
  as well. Numbers, strings, byte and float arrays and scalars hold
  nothing observable. The reason printed is `its elements (…) may
  hold a value of type …, whose release the program can observe`.
- **Why:** leanrt releases the elements of a typed array in another order
  than native Lean's two passes when an element, or a member of two
  elements, is shared (`ReleaseElems` in `runtime/leanrt/src/drop.rs`:
  records in index order, other types from the last, each completely), and
  it releases a record that a set or a pop replaces by the record's own
  drop, which frees its fields in field order (next section). With a
  handle in the element, that changes the order in which files close
  (`RtArrayFreeDirectOrder`, `RtArraySetFreeNested`, `RtArrayPopFreeOrder`
  keep their arrays boxed for this reason). An array of boxes keeps
  native's order exactly. A hash map's buckets stay boxed for this reason
  too whenever code reads them at the layout's type: `Raw.buckets` is
  `Array (AssocList lcAny lcAny)` under rule 1, and its element type
  reaches `lcAny` (k-nucleotide, lean-regex). In hashmap (the classic
  program) no code reads them so, and `I:Std.DHashMap.Internal.AssocList`
  stays on.
- **Where:** `CompactArrays.lean`: `releaseUnsafe?`, the loop over
  `CAState.ptrElems` at the end of `compactArrayKinds`.
- **Remove only if:** leanrt releases typed elements in native's order (a
  release that decrements or, at the last reference, defers: a Reussir
  entry point, parked).
- **Possible extension:** a whole-program fact that the program makes no
  value with an observable release (no handle, task, promise or
  event-loop object) would let these kinds on too (`AssocList` buckets).

### A set or a pop releases a replaced record by its own drop

- **What:** leanrt's `ReleaseElem for Bridge` (`runtime/leanrt/src/array.rs`)
  drops the record a set or a pop removes by its own drop
  (`<record>_ffi_release`: a decrement, or the record's free), through a
  call out of line (`drop_record`). Before, every removed record went
  through a free the runtime starts (`array::release_last`,
  `drop::release_unique`), shared or not, so that its fields went in
  Lean's order.
- **Why:** That free cost about 74 instructions per set. With it, n-body
  with typed arrays ran 760 M instructions, more than with boxes (602 M);
  with the record's own drop, 493 M. The order is not seen: typed arrays
  hold only elements without observable releases (previous section). In
  line, LLVM put the record's whole release into the set texture, which
  then was too big to inline into Reussir code (unionfind's
  `l2r_array_set<nodeData>` stayed a call: 6.56 G instructions in all;
  out of line 5.89 G; with boxes 6.80 G).
- **Where:** `runtime/leanrt/src/array.rs`: `ReleaseElem`, `drop_record`,
  `release_last` (kept, unused, for element types whose release order is
  seen); [../ownership.md](../ownership.md#a-set-releases-a-replaced-record-by-its-own-drop).
- **Remove only if:** lean2rr types arrays whose elements may hold an
  observable value (then those need `release_last` again).

### A field `Array α` used with a pointer kind is a box

- **What:** `arrayFieldInductives` also collects the inductives with a
  field `Array α` (`Subarray.array`) that some binder type instantiates
  with an array of a pointer kind (`Subarray Point`). During the check
  such a field is a box (`caFieldTypes`); after it, the field stays a box
  when some pointer kind is on (as before, an inductive instantiated with
  a scalar array keeps its boxed field when some storage kind is on).
  With no pointer kind on, the field is the array of boxes `Array lcAny`
  again, which holds every array stored there, since all of them are
  arrays of boxes then.
- **Why:** As for compact arrays
  ([compact-arrays.md](compact-arrays.md#a-field-array-α-of-an-inductive-used-with-a-compact-array-is-a-box)):
  the field `Array lcAny` would meet every typed array stored in it. The
  field stays a box for every pointer kind that stays on, not only for
  the kinds its instances name: a binder of an imprecise type (a
  `Subarray lcAny` built from an `Array Point`) can store an array of
  another kind there, and the check, which saw a box, did not stop it.
- **Where:** `CompactArrays.lean`: `arrayFieldInductives`,
  `compactArrayKindsRun` (`boxedFinal`).
- **Remove only if:** the layouts of generic types change.

### A `map` split only for pointer kinds that end up boxed runs in place again

- **What:** Stage 3 decides the typed `map` loops before the whole-program
  check. A loop whose element types differ (`α ≠ β`) is split: the
  instance reads the source and pushes each mapped value onto a new array
  (`Array.emptyWithCapacity β n`). For a split only for pointer kinds
  (neither element type holds a storage kind), Stage 3 keeps the loop it
  types (`MRetypeState.ptrSplitOrigins`). After the check, every entry of
  such a split whose two element types stay boxed calls that loop again,
  with the original arguments, and the `let`s of the new array and of
  the source's size go (`revertPtrSplits`). The instance's own source and
  result parameters are found by names no user code has (`splitSrcName`,
  `splitDstName`: a numeric part after a plain string), with the
  instance's parameters one more than the loop's: a lambda's captured
  variables come first among the loop's parameters with their user
  names, and a capture named `src` matched by name moved the arguments
  (re-review probe SD2, an internal panic; test
  `RtTArrMapCaptureNames`). The program changed, so the
  check runs again, until no such entry is left. `L2R_DEBUG=1` prints
  `lean2rr: typed arrays: N map loop entries in place again (their kinds
  are off)`.
- **Why:** On boxed arrays the split allocates a new array per `map`
  where the loop updates the array of boxes in place, as natively: review
  probe D (rounds of `String → Nat → String` maps, every kind off) made
  96 bytes per element, native 8; with the entries in place again, 8, as
  on dev (test `RtTArrMapInPlace`). A split whose kinds stay on keeps its
  new array (the price of typing: natively a `map` is in place).
- **Where:** `CompactArrays.lean`: `revertPtrSplits`, `splitOrigin?`,
  `dropUnusedLets`, `codeUsedFVars`; `ArrayKinds.lean`: `splitSrcName`,
  `splitDstName`; `Opt/SplitMapLoops.lean`: `ensureSplit`, `buildSplit`,
  `splitMapLoops` (the kept loops); `Emit/Program.lean`: `lowerProgram`.
- **Remove only if:** Stage 3 knows the kinds before it splits.
- **Open:** in probe D the second `map` of a round (`Nat → String`) keeps
  Lean's loop over `Array NonScalar`, whose result in the `for` loop's
  state turns `Nat` and `LStr` off for the whole program.

### The `map` loops and array parameters are typed at pointer kinds too

- **What:** With `typed-arrays`, Stage 3 types the loops of
  `Array.mapMUnsafe` and `Array.mapFinIdxMUnsafe` and the `Array lcAny`
  parameters typed from their callers
  ([compact-arrays.md](compact-arrays.md#the-loops-of-arraymap-are-typed-optsplitmaploopslean))
  also when an element type has a pointer kind (`holdsCompactKind` with
  `ptr`; `MRetypeState.typedArrays`, set by `compact-arrays`' hooks). A
  source of pointers is still read with placeholders (only a source of
  scalars is read without them).
- **Why:** An untyped loop casts its array to `Array NonScalar`
  (`Array lcAny`): a crossing at every `map` of a typed array.
- **Where:** `Opt/SplitMapLoops.lean`: `splitEntries`,
  `arrayParamsFromCallers`, `Opt.CompactArrays.install`,
  `Opt.TypedArrays.install`; `ArrayKinds.lean`: `holdsCompactKind`.
- **Remove only if:** the optimization is off.

### The arguments of a spawned process are copied into boxes

- **What:** `spawnCall` (`Lower/Process.lean`) passes `SpawnArgs.args` to
  the runtime as an array of boxes; a typed `RVec<LStr>` is copied into a
  new array of boxes first (`l2r_proc_args_boxes_…`, an `arrayMapFn`).
- **Why:** `l2r_proc_spawn` and `l2r_proc_output` take `RVec<LAny>` and
  read each boxed string in place. The runtime only reads the copy.
- **Where:** `Lower/Process.lean`: `spawnCall`. Tests `RtCwdLong`,
  `RtProcessClosedFd` (process arguments from array literals).
- **Remove only if:** the runtime takes typed strings.

### No safety net: a missed crossing is a panic

- **What:** A box of a typed array has the program's payload number of
  `RVec<T>` (`boxKind`). Unboxed at `RVec<LAny>` it is a mismatch
  (`leanrt::any::mismatch`, a panic), never a wrong read. Compact arrays
  convert in that case instead
  ([compact-arrays.md](compact-arrays.md#the-safety-net-an-array-of-scalars-unboxed-as-an-array-of-boxes-is-converted)).
- **Why:** No net is needed: a typed array never reaches an unboxing at
  `RVec<LAny>`. Each pointer kind names one Reussir type (`ptrKind?`,
  the same function in the check and in the lowering), so two element
  types of one kind have one representation. The places where a value
  goes from one binder or position at one type to another at its own (an
  argument and its parameter, a result and its binder, a jump, a return,
  a constructor argument and its field, a field read, an extern's
  argument and result) compare the two types (`alignArr`), and arrays of
  two kinds there turn both kinds off. Every place joins the binders into
  flow classes, also those that only move a value without a second type
  to compare (the application of a value whose type is no function type,
  a constructor applied to fewer arguments than its fields, the startup
  glue's store of an initializer's result): those are safe by the class
  rule below. A box keeps its
  payload's type (`RVec<T>` has a payload number of its own), so a typed
  array in a box is unboxed only by a binder or position of its class,
  and a class that holds an `Array lcAny` (or a position of that type
  that gets a box, or an extern result of that type taken as a box) turns
  every kind its types mention off. An extern's parameters and results
  are compared strictly. (A net would need a generated conversion per
  typed array type and a dispatch at each unboxing at `RVec<LAny>`:
  leanrt does not know how to box a program's elements.)
- **Where:** `LowerBase.lean`: `boxKind`, `boxUnboxWith`.
- **Remove only if:** a net is added (generated, on the mismatch path
  only).

### Costs

- An array copy (copy-on-write) clones each record element with its
  `Clone` (`_ffi_acquire`, inlined by LLVM), where an array of boxes was
  one `memcpy` and in-line count increments.
- The free of an array of records calls each element's
  `<record>_ffi_release`, which LLVM does not inline (the record's whole
  free is in it), where an array of boxes decremented a shared element in
  line. Outside a free the array is freed at once (`free_now`, up to 16
  nested levels; below that, a step of the runtime's free, whose drain
  pushes the deeper arrays: `RtDropDeep`). Through a step for every array
  (Reussir's drain loop and its end hook), Cedar (Z06g), which frees many
  old copies of arrays of records, ran 0.6% more instructions with typed
  arrays than with boxes (75.91 → 76.36 G) and monadic-interp (L15) spent
  about 1.2 G of 20.3 G in the steps; with `free_now` Cedar runs 76.01 G
  (0.1% more than with boxes) and monadic-interp 19.61 G (3.3% fewer than
  through the steps).
- The placeholder that `Array.modify` stores is the element type's zero
  (`placeholder-cache`: a once-cell read), where a box was `box(0)`.
- rrc compiles the array textures again for each typed record type (a
  texture at a program type misses rrc's texture cache in every new
  program, `tyInEveryProgram`).
