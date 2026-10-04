# References (`ST.Ref`, `IO.Ref`)

Paths are relative to `lean2rr/LeanToReussir/` unless they start with
`runtime/`. Plan [§5.1](../../translation-plan.md#51-type-translation)
(the `ST.Ref` row, and "A reference (`ST.Ref`) is boxed…").

### A reference is a record around a Reussir cell, per element type

- **What:** A reference whose contents have Reussir type `e` is a
  generated shared record `L2RRefN(Cell<e>)` (N a fresh number) around a
  Reussir cell, the value stored in its own representation, every alias
  sharing the record. The cell is a counted object of its own, so a
  reference is two allocations (Lean's is one).
- **Why:** References used to hold `Box` values, so every `get`/`set`
  boxed (adv4 K1, 1688c98).
- **Where:** `LowerBase.lean`: `refType`, `refElem?`, `RefKind`;
  `Lower/LazyForce.lean`: `refNew`; `Lower/Externs.lean`: `refGlue`,
  `refCellOp`; `runtime/prelude.rr`: `l2r_rc_get`, `l2r_rc_set`,
  `l2r_rc_swap`.
- **Remove only if:** never. (`LRef<T>` and the prelude's `l2r_ref_*`
  are no longer used by generated code: promises hold an `LCell`.)

### `[value]` records in references are boxed

- **What:** A reference to a `[value]` record keeps the value in an
  `ElemBox` (one allocation per `set`). A `Nat` or `Int` reference holds
  the handle in its cell like any other value (one-word handles since
  mem-nat; they were split into a tagged word and a big-number cell,
  `L2RNatRef`/`L2RIntRef`, while they were `[value]` enums).
- **Why:** A Reussir `Cell` of a `[value]` record with counted members does
  not compile ([Reussir bug 19](../../../reussir-bugs/19-cell-of-value-record.md)).
- **Where:** `LowerBase.lean`: `refType` (`RefKind.boxed`).
- **Remove only if:** bug 19 is fixed.

### Typed references come only from `mkRef` at a precise type

- **What:** Mono types every reference `lcAny`. Stage 3 gives an
  `ST.Prim.mkRef` instance at a precise `α` the type `typedRef α` and
  carries it to the binders the reference flows into; elsewhere a
  reference travels in a `Box`. `typedRef` is the constant
  `_l2r.TypedRef`, which is not a Lean declaration: where lean2rr hands
  its mono declarations back to Lean's passes (borrow inference), it
  declares it for the run
  ([../ownership.md](../ownership.md#leans-borrow-inference-sees-lean2rrs-typed-references-as-opaque-types-a-failure-is-an-error)).
- **Why/Where:** see
  [../types/type-recovery.md](../types/type-recovery.md#references-created-at-a-precise-type-are-typed).
- **Remove only if:** never.

### A reference in a `Box` is used through a generated dispatch

- **What:** An operation on a reference held in a `Box` (uniform code, or
  typed code that got it through an `lcAny` position) calls a generated
  function (`l2r_refbox_<op>_<type>`, `l2r_refbox_addr`) that matches the
  reference types the program boxes and acts on that reference's one cell,
  converting between the cell's element type and the operation's. A `Box`
  holding no reference is unreachable there.
- **Why:** A reference cannot be converted without losing aliasing.
- **Where:** `Lower/Externs.lean`: `refBoxOpFn`, `finishRefFns`,
  `refGlue`; `Lower/Values.lean`: `refCall?` (references are passed at
  their own representation, not converted to the extern's `lcAny`).
- **Remove only if:** never. Cost: a dispatch per operation on a boxed
  reference.

### `take` moves the value out of the cell

- **What:** `ST.Prim.Ref.take` swaps the placeholder into the cell and
  returns the old value, as `lean_st_ref_take` stores `box(0)`, for every
  element type (a big `Nat`/`Int` too, since mem-nat).
- **Why:** Lean's `modify` is take-then-set: a value only the cell holds
  stays unshared and is updated in place. Reading a copy instead made
  every `modify`/`modifyGet` copy the array or string it updates
  (quadratic loops; adv round 1, 3f59239; runtime request 16).
- **Where:** `Lower/Externs.lean`: `refCellOp`; `runtime/prelude.rr`:
  `l2r_rc_swap`.
- **Remove only if:** never.

### `set` stores before it releases

- **What:** A reference's `set` stores the new value, then releases the
  old one.
- **Why/Where:** see
  [../ownership.md](../ownership.md#reference-sets-store-the-new-value-before-releasing-the-old-one).
- **Remove only if:** see the linked entry.

### `ST.Ref.ptrEq` is real identity

- **What:** `ST.Ref.ptrEq` compares the addresses of the two references'
  records, whatever representation each side is seen at.
- **Why:** All aliases share one record.
- **Where:** `Lower/Externs.lean`: `refGlue` (the `addr` operation);
  `runtime/prelude.rr`: `l2r_ptr_addr_rec`.
- **Remove only if:** never.
