# Typed references (typed cells)

The cell of a reference `ST.Ref σ X` holds `X`'s own Reussir type `T`,
`L2RRef_N(Cell<T>)`, when the whole program allows it: optimization
`typed-cells` (on by default; `--disable-opt typed-cells` gives every
reference its cell of boxes again, as in
[references.md](references.md#a-reference-is-one-record-type-around-a-reussir-cell-of-a-box)).
This is clean step B2 of the plan to use only Reussir's interface, for
references. Thunks, tasks and promises keep their cells of boxes (last
section). Paths: `lean2rr/LeanToReussir/` for lean2rr's files, `runtime/`
for the runtime.

Example. `r : IO.Ref Pt` (`structure Pt where n : Nat; s : String`) is a
record `L2RRef563(Cell<T_Pt_562>)`. `r.modify f` takes the record out of
the cell with `l2r_rc_swap<T_Pt_562>(r.0, <placeholder>)`, applies `f`,
and stores the result with `l2r_rc_set_ref<T_Pt_562, L2RRef563>(…)`: no
box is made or tested for the value. Without the optimization the cell is
`Cell<LAny>`, the value is boxed at the store and unboxed (a test of the
box's payload number) after the take.

### The cell kinds

- **What:** A cell kind names the Reussir type that the lowering gives an
  element type, so that two element types of one kind have one
  representation (`CellKinds.lean`: `cellKind?`):
  - `bool`, `u8`, `u16`, `u32`, `f32`: `Bool`, `UInt8`, `UInt16`,
    `UInt32` (and `Char`, whose mono type is `UInt32`), `Float32`;
  - `Nat`, `Int`, `LStr`: `Nat`, `Int`, `String` (`Nat` and `Int` none
    under `--int-backend rcgmp` without `--rcgmp-type-args`: `cellKind?`'s
    `natInt`; `l2r_rc_set_ref<T, R>` passes the old value to the texture
    `l2r_release_value_then<T, R>`, where Reussir would give it a raw rcgmp
    handle; [nat-int.md](nat-int.md#--int-backend-rcgmp-the-lowering-in-progress));
  - `I:<name>`: an inductive that the lowering makes a shared record or
    enum (`sharedInductive?`, the function typed arrays use: rule 1 gives
    `List Nat` and `List String` the one type `T_List`);
  - `A(<s>)`: an `Array Y`, where `s` is how the program's arrays store
    `Y` (`arrayStorage`): `Y`'s storage kind if compact, `Y`'s cell kind
    if its pointer kind is typed, else `box`. So `Array Nat` and
    `Array lcAny` are one kind, `A(box)`, in a program whose arrays of
    `Nat` hold boxes.

  `UInt64`, `USize` and `Float` have no cell kind, and neither have
  enumerations, function types, thunks, tasks, references, handles,
  `lcAny` and types that are no inductive. The glue of the six reference
  primitives (`refGlue`) asks `refElemTy` for the cell's type: `T` when
  the kind of the instance's `α` is on (`LowerCtx.refKindsOn`), else
  `Box` (also when `T` is not of the shape the kind names, which then
  holds for every type of the kind alike, so all of them keep the cell of
  boxes); `refTypeOf` gives one record type per cell type (`refType` for
  `Box`, as before).
- **Why:** Rule 1 gave every reference a cell of boxes: each store tagged
  or boxed the value, and each take tested the box's payload number. A
  typed cell keeps the value as typed code has it. A box of `UInt64` or
  `Float` allocates (a `Float` always, a `UInt64` from 2^63), and a
  reference's `get` gives its value in the IO result, whose field is a
  `Box` (`ST.Out`, one layout): a typed cell of such a type would allocate
  at each read, where the cell of boxes allocates at each store, as Lean
  does.
- **Where:** `CellKinds.lean`: `cellKind?`; `Lower/Externs.lean`:
  `refElemTy`, `refGlue`, `refCellOp`, `refCellOpPlain`, `refPoint`;
  `LowerBase.lean`: `refTypeOf`, `refElem?`, `isRefName`, `isRefType`,
  `LowerState.refTypes`, `refElems`; `Opt/Registry.lean`: `typed-cells`;
  `Opt/TypedCells.lean`; `PassConfig.typedCells`.
- **Remove only if:** the box becomes a Reussir type as cheap as a typed
  cell (clean step C), or never.

### The whole-program check compares the instances of the primitives

- **What:** `typedRefKinds` (`TypedCells.lean`) collects the element type
  `α` (`InstKey.typeArgs[1]`, through `toMonoTypeKeep`) of every instance
  of `ST.Prim.mkRef` (the makes) and of `get`, `set`, `swap`, `take` and
  `ptrEq` (the operations) among the program's declarations, and `lcAny`
  for a primitive called by its own name. For every make and operation
  whose types can be one type up to `lcAny` (`cellTypesMeet`, on the mono
  types: `lcAny` or a type whose head is no inductive meets every type;
  two different inductives never meet; arguments are compared in turn),
  unless their type arguments before mono are apart (`cellBaseApart`: at
  a position reached through one inductive head, two different inductive
  or opaque heads, one of which mono represents by a box, such as a
  reference or a promise inside the element type), both must have
  one representation (both kinds on and equal, or both cells of boxes);
  otherwise both kinds go off, until no pair differs. A kind is also off
  when its element type can reach a value whose release the program can
  observe (`releaseUnsafe?`, the rule of typed arrays), and every kind is
  off in a program that can cast (`programCasts`). `L2R_DEBUG=1` prints
  `lean2rr: typed cells: references: …` with the kinds that stay on and,
  for each kind seen and turned off, the first reason.
- **Why:** Mono types every reference `lcAny`, so the check cannot follow
  references through binders as the check of arrays does. It does not
  need to: a reference travels in a `Box` (its record has a payload number
  of its own), and only the six primitives touch its cell. A reference
  made at `M` reaches an operation at `O` only if `M` and `O` can be one
  type: the program is typed, and Stage 1 replaces a type variable by a
  type or by `lcAny` (an existential's type, a uniform instance,
  polymorphic recursion), never by an unrelated type. So an operation at
  `lcAny` (an existential package's reference, `RtTRefGeneric`) turns off
  every kind; the instances at concrete types decide everything else. Mono
  also gives a reference whose element is a reference, a promise or a
  token the element type `lcAny`; the type arguments before mono keep
  their heads (`ST.Ref lcAny Nat`), and two different inductive or opaque
  heads are never one type, so such a reference meets no reference of
  another element type (`cellBaseApart`; review repros: an
  `IO.Ref (IO.Ref Nat)` and an `IO.Ref (Array (IO.Ref Nat))` turned every
  kind off before). Known coarse case: base code already types a file
  handle (an opaque type) `lcAny`, so an `IO.Ref IO.FS.Handle` is a make
  and operations at `lcAny` and still turns every kind off. A
  missed pair would be a payload number mismatch at the unboxing of the
  reference (`l2r_unreachable`, a panic), never a read of a cell of
  another type. A typed cell's value is released by Reussir's own drop
  when the reference dies, in Reussir's field order, where a box's release
  follows Lean's order: hence the release rule.
- **Where:** `TypedCells.lean`: `typedRefKinds`, `refMakePrim`,
  `refOpPrims`, `TCResult`, `cellBaseApart`; `CellKinds.lean`: `cellTypesMeet`;
  `CompactArrays.lean`: `releaseUnsafe?`; `Emit/Program.lean`:
  `lowerProgram` (after the array decisions, which give the `A(…)`
  kinds). Tests `RtTRefKinds` (every kind on), `RtTRefGeneric` (an
  operation at `lcAny`: every kind off), `RtTRefMixed` (kinds off for
  their releases beside kinds on), `RtTRefTasks` (a program with tasks:
  `refPoint` at a typed record), `RtTRefInPlace` (`.alloc`: `modify` of a
  value only the cell holds runs in place); each has an `.l2r-debug` file
  whose lines are checked only while the optimization is on.
- **Remove only if:** never while references have two representations.

### `take` stores the placeholder of the element type

- **What:** `take` (in `modify`, `modifyGet`) swaps the zero of the cell's
  type into a typed cell (`cellZero`): a literal for a scalar or a small
  `Nat`/`Int`, the cached empty string, a nullary constructor, or a value
  built once and kept in a once-cell (a record, an empty array, an empty
  string outside the literal cache): `zeroValue`'s once-cell with
  `placeholder-cache`, without it one of `cellZero`'s own
  (`l2r_cellzero_N`, `cafAccessor`). The value taken out keeps the cell's
  reference, so a value only the cell holds stays unshared and is updated
  in place, as before.
- **Why:** A Reussir cell holds a value of its type; the cell of boxes
  stores `box(0)`, natively a null pointer, at no cost. A placeholder
  built at each take would allocate once per `modify`: with
  `placeholder-cache` off, `RtTRefInPlace` made 12058 allocations more
  than natively from n = 2000 to 8000 for an array, 12060 for a record
  (review of the change); with `cellZero`'s once-cell, as many as natively.
- **Where:** `Lower/Externs.lean`: `cellZero`, `refCellOpPlain`;
  `LowerBase.lean`: `LowerState.cellZeroFns`; `Lower/Conv.lean`:
  `zeroTry`, `cafAccessor`. Test `RtTRefInPlace` (`.alloc`; checked also
  with `placeholder-cache` off).
- **Remove only if:** never.

### The walks and placeholders of references follow the cell's type

- **What:** The walk of a constant for tasks reads a reference's value at
  the cell's type (`genPersist`); whether a reference can hold a task
  follows the cell's type (`typeHoldsTask`); a reference's own placeholder
  (an unused cell) holds the zero of the cell's type (`zeroTry`).
- **Why:** These read the cell; a typed cell holds no box.
- **Where:** `Lower/Finish.lean`: `genPersist`; `Lower/Conv.lean`:
  `typeHoldsTask`, `zeroTry`.
- **Remove only if:** never.

### Thunks, tasks and promises keep their cells of boxes

- **What:** `Thunk α`, `Task α` and `IO.Promise α` are not typed by this
  optimization ([../tasks/cells.md](../tasks/cells.md)).
- **Why:** Mono code keeps `Thunk X` and `Task X` in its types, and rule 1
  gives a field `t : Thunk α` the layout `Thunk lcAny`. A typed cell would
  then meet the cell of boxes directly, with no box between them, so the
  check would have to follow every binder and field, as the check of
  arrays does (flow classes, boxed fields), for a second container. Task
  cells also have one state type in the runtime's protocol (the task tag,
  `taskTag`, and the dispatch of handed-over tasks, `taskDispatchFns`),
  and a promise's cell is made by the runtime (`promise_new`).
- **Remove only if:** a later step extends the check of arrays to thunks
  and tasks.

### Effect

In an `Init`/`Std` program without casts the cell of `IO.stdGenRef`
(`StdGen`, a record of two `Nat`s) is typed: the classic corpus has 16
box sites and 15 payload types of `Box` fewer (1688 → 1672, 256 → 241;
`rr-fingerprint.py show`), its `.rr` 0.12% smaller. Of the 53 programs of
the shared benchmark set, 51 get another `.rr`; Cedar (Z06g, Z06d, Z06t)
types its references of a tree map and of a `Bool`. CslInitOnly casts, so
every kind is off there and its `.rr` is unchanged.

### Costs

- One record type and one placeholder per typed cell type, and the
  functions and textures of the reference primitives (`l2r_rc_set_ref`,
  `l2r_release_value_then<T, R>`, and in a program with tasks
  `l2r_ref_wait<R>`, `l2r_ref_take_mark<R>`) instantiated at each record
  type (16 in `RtTRefKinds`, 1 with cells of boxes): rrc compiles a
  texture at a program type again in every program. `wait` and
  `take_mark` read only the record's address and drop it, but no type
  common to the record types exists without a box, so they are not
  shared.
- `take` of a record or an array reads a once-cell (the placeholder),
  where a box was `box(0)`.
- `get` still boxes the value for the IO result's `Box` field, which the
  caller unboxes, as with a cell of boxes.
