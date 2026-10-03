# Identity: what `ptrAddrUnsafe` answers

**Status:** being removed. The project's contract is moving to functional
equivalence (same results, not the same object identities). Branch
`mem-identity` (not merged at b299aab) removes the identity emulation
below: `ptrAddrUnsafe` there answers the value's own cell (a word computed
from a scalar), the origin table goes
([../ownership.md](../ownership.md#converted-values-record-their-origin-being-removed)),
converted thunks and tasks no longer stand for their original, and
`fresh-rebuild` loses its identity guard. Update or delete these entries
when that branch is merged.

Paths are relative to `lean2rr/LeanToReussir/` unless they start with
`runtime/`. Plan [§9](../../translation-plan.md#9-open-items) ("Pointer
equality in `Init`").

### `ptrAddrUnsafe` maps each representation back to Lean's

- **What:** `addrOf` answers per representation: `lean_box(n) = 2n+1`
  for what Lean represents as a boxed scalar (a small `Nat`, an `Int` in
  `int32`, `UInt8/16/32`, `Char`, `Bool`, enumerations, nullary
  constructors, `Unit` as 1); the handle pointer for heap values; a
  `[value]` struct its field's answer; a fresh number for `UInt64`,
  `Float` and the like, which natively are boxed into a new cell at each
  call; a `Box` its payload's identity; a function value wrapped for
  another representation the wrapped value's; a converted thunk or task
  its original's; a structurally converted record, list or array its
  origin's (through the origin table). A `Nat` in [2^63, 2^64) or an `Int`
  outside `int32` (natively a big-number object) answers a number computed
  from its value.
- **Why:** Lean code stops when `ptrEq` says a step changed nothing
  (`Expr.replace`, fixpoint loops), so `ptrEq x x` must hold for every
  representation, and a payload returned by its own function must be
  `ptrEq` to itself (adv3 RP3-1, 90b29df; adv4 RP4-01/02, fad7e6b).
- **Where:** `Lower/Identity.lean`: `addrOf`, `cellScalar`, `nativeLeaf`,
  `lazyAddrFn`, `fnAddrFn`, `boxAddrFn`, `recAddrFn`, `genFnAddr`,
  `genBoxAddr`; `runtime/prelude.rr`: `l2r_addr_word`, `l2r_addr_nat`,
  `l2r_addr_int`, `l2r_addr_fresh`, `l2r_ptr_addr_obj`,
  `l2r_ptr_addr_rec`; `runtime/leanrt/src/lib.rs`: `fresh_addr`.
- **Remove only if:** the functional-equivalence contract is adopted
  (branch `mem-identity`).

### A heap value's address is its handle, whatever its count

- **What:** A heap value passed as it is goes to `l2r_ptr_addr_obj`,
  which answers the handle pointer whatever the reference count. For a
  shared record, `l2r_ptr_addr_rec` gives the reference it received back
  inline (a decrement) when others remain, instead of the record's
  out-of-line release.
- **Why:** A "count 1 means the value dies with the call, so give a fresh
  number" rule also fired for `ptrEq d d'` where `d`'s call had released
  the other reference (Rp3Dag printed `false`; adv3 RP3-1, 90b29df). The
  out-of-line release cost about a quarter of a `ptrEq` traversal (Rp3Dag
  25: 0.40 s → 0.29 s, 66edbfb).
- **Where:** `runtime/prelude.rr`: `l2r_ptr_addr_obj`,
  `l2r_ptr_addr_rec`; `Lower/Identity.lean`: `addrOf`.
- **Remove only if:** identity emulation goes (branch `mem-identity`
  keeps `l2r_ptr_addr_rec` but no longer looks up origins).

### Whether the program observes identity is a whole-program fact

- **What:** `LowerCtx.observesIdentity` is true when some declaration
  calls `ptrAddrUnsafe` (`lean_ptr_addr`, to which `ptrEq` and
  `withPtrAddrUnsafe` inline), `ST.Prim.Ref.ptrEq` or `dbgTraceIfShared`,
  also as a function value.
- **Why:** Only in a program that never observes identity or sharing can
  `fresh-rebuild` return an equal copy instead of the matched value
  ([../control-flow/cases.md](../control-flow/cases.md#an-arm-that-returns-the-matched-value-returns-that-value)).
- **Where:** `Lower/Identity.lean`: `codeObservesIdentity`,
  `programObservesIdentity`; `Emit/Program.lean`: `lowerProgram`.
- **Remove only if:** `fresh-rebuild` no longer needs the guard (branch
  `mem-identity` removes both).

### Sharing is not observable

- **What:** `isExclusiveUnsafe` answers `false`, `lean_is_scalar` answers
  `false`, `shareCommon` is the identity, and `ShareCommon.Object.eq`
  holds only for the same object.
- **Why:** lean2rr's objects have no Lean layout to compare byte by byte;
  answering "shared" only makes such code take its general path.
- **Where:** `runtime/prelude.rr`: `lean_is_exclusive_obj`,
  `lean_is_scalar`, `lean_sharecommon_quick`; `Lower/ExternCall.lean`:
  `customExtern` (`ShareCommon.State.shareCommon`);
  `lean2rr/L2RShim.lean` (`lean_sharecommon_eq`/`hash`).
- **Remove only if:** never (a documented divergence, plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features)).
