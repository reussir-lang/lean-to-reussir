# References (`ST.Ref`, `IO.Ref`)

Paths are relative to `lean2rr/LeanToReussir/` unless they start with
`runtime/`. Plan [§5.1](../../translation-plan.md#51-type-translation)
(the `ST.Ref` row, and "A reference (`ST.Ref`) is boxed…").

### A reference is one record type around a Reussir cell of a `Box`

- **What:** Every reference, whatever its contents' type, is the one
  generated shared record `L2RRefN(Cell<Box>)` (N a fresh number) around a
  Reussir cell, every alias sharing the record. `set` boxes the value,
  `get` and `take` give a `Box` (the IO result's field holds it as it
  is). Mono types every reference `lcAny`, so a reference travels in a
  `Box`; an operation unboxes it (one variant: one reference type). The
  cell is a counted object of its own, so a reference is two allocations
  (Lean's is one).
- **Why:** One representation per type (rule 1 of the layouts of generic
  types). With a reference type per element type, an operation on a
  reference held in a `Box` went through a generated dispatch over every
  boxed reference type, and Stage 3 typed the references made at a
  precise type (`typedRef`) so that typed code avoided it.
- **Where:** `LowerBase.lean`: `refType`, `isRefType`;
  `Lower/LazyForce.lean`: `refNew`; `Lower/Externs.lean`: `refGlue`,
  `refCellOp`, `refCellOpPlain`; `runtime/prelude.rr`: `l2r_rc_get`,
  `l2r_rc_set_ref`, `l2r_rc_swap`.
- **Remove only if:** never. (`LRef<T>` and the prelude's `l2r_ref_*`
  are no longer used by generated code: promises hold an `LCell`.)

### `take` moves the value out of the cell

- **What:** `ST.Prim.Ref.take` swaps the placeholder `box(0)` into the
  cell and returns the old value, for every element type (a big
  `Nat`/`Int` too, since mem-nat). Natively `lean_st_ref_take` stores a
  null pointer (Lean 4.34's `io.cpp`), which only unsafe code can see
  before the next store (`refCellOpPlain`'s comment).
- **Why:** Lean's `modify` is take-then-set: a value only the cell holds
  stays unshared and is updated in place. Reading a copy instead made
  every `modify`/`modifyGet` copy the array or string it updates
  (quadratic loops; adv round 1, 3f59239; runtime request 16).
- **Where:** `Lower/Externs.lean`: `refCellOpPlain`; `runtime/prelude.rr`:
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
  records (each unboxed first).
- **Why:** All aliases share one record.
- **Where:** `Lower/Externs.lean`: `refGlue` (the `addr` operation);
  `runtime/prelude.rr`: `l2r_ptr_addr_rec`.
- **Remove only if:** never.
