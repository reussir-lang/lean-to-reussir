# Identity: what `ptrAddrUnsafe` and `ptrEq` answer

lean2rr does not emulate native pointer identity or sharing: a translated
program gives the same results as natively when they do not depend on
them (the functional-equivalence contract, plan
[§9](../../translation-plan.md#9-open-items), "Identity is not
preserved"). Paths are relative to `lean2rr/LeanToReussir/` unless they
start with `runtime/`.

### `ptrAddrUnsafe` answers a cell address or a word computed from the value

- **What:** `ptrAddrUnsafe x` takes `x` in its own representation (it is
  not converted for the call) and answers: for a heap value (a record, a
  function value, a string, an array, a reference, a thunk or task, a
  runtime handle) its cell's address, whatever its count (a nullary
  constructor of a shared enum: its immediate); for a `Box` (the one-word
  `LAny`) its payload's address, or an immediate's own word, which is
  native's boxed scalar (`LAny::addr`); for a `Nat` or
  `Int` its word, which is native Lean's (the boxed scalar `2n+1` when
  small, else the big number's pointer; [nat-int.md](nat-int.md)); for
  `UInt8/16/32`, `Char`, `Bool` or an enumeration the boxed scalar's word
  `2n+1`; for `Unit` and erased values in typed code `1` (in uniform code
  an erased value is the boxed unit, the word `1`, native's `box(0)`); for
  `UInt64`, `Float`, `Float32` their bits; for a `[value]` struct its
  field's; for a value of a type `addrOf` does not know, a number
  answered only once.
- **Why:** For two values alive at the same time, equal answers then mean
  the same cell or equal values, so `ptrEq` answering `true` still means
  equal values, which code using it as a shortcut for equality needs
  (`Array.mapMono`, `List.mapMono`, `withPtrEq`, `ShareCommon`). Every
  caller in `Init` and `Std` compares live variables. Taking `x` as it is
  matters: converted for the call, it would be a temporary cell whose
  address the next temporary can get (499073c; adv3 RP3-1, 90b29df). The
  identity emulation that answered native's identity (origin table,
  address stand-ins, identity guards) was removed (mem-identity: 7869383,
  a4a04e8, 0f2f1e7, c5eaca5).
- **Where:** `Lower/Identity.lean`: `addrOf`; `Lower/Values.lean`:
  `lowerConstApp` (the `lean_ptr_addr` case); `runtime/prelude.rr`:
  `l2r_ptr_addr_obj`, `l2r_ptr_addr_rec` (which gives the reference it
  received back inline: 66edbfb), `l2r_addr_word`, `l2r_addr_nat`,
  `l2r_addr_int`, `l2r_addr_fresh`; `runtime/leanrt/src/lib.rs`:
  `fresh_addr`. Tests `RtPtrSound`, `RtPtrAddr`.
- **Remove only if:** never. Answers that differ from native (a value
  converted by a cast is a new object; equal `UInt64`s,
  `Float`s and small numbers are `ptrEq`, also through a generic function,
  which lean2rr instantiates at the type: two `Float`s compared by
  `ptrEq` on `α` are natively two new boxes, `false`, adversarial
  finding 4) are plan §9's list. Two boxings of one constant are one cell
  (`boxed-consts`), as natively (`_boxed_const_N`) within one module:
  native Lean caches its boxed constants per module (`cacheAuxDecl` in
  `ExplicitBoxing`), lean2rr one cell per constant for the whole program,
  so `ptrEq` on the boxings of one constant from two modules answers
  `true` here and `false` natively; in the body of a constant lean2rr
  boxes in line (a new cell each time, natively the module's cell). A
  temporary can reuse the
  cell of one that has died: `ptrAddrUnsafe` as a function value applied
  at another representation, the parameter of a non-inlined function given
  an argument converted by a cast, a polymorphic function value that boxes
  a `Float` or another value boxed in a cell.

### `ST.Ref.ptrEq` stays real identity

- **What/Why/Where:** see
  [references.md](references.md#strefptreq-is-real-identity).
- **Remove only if:** never.

### Sharing is not observable

- **What:** `isExclusiveUnsafe` answers `false`, `lean_is_scalar` answers
  `false`, `shareCommon` is the identity, `ShareCommon.Object.eq`/`hash`
  compare addresses, and `dbgTraceIfShared` reads the cell's count, which
  conversions and lean2rr's own copies can make differ from native: the
  count of each storage type (`leanrt::is_shared`: handles, strings,
  arrays, thunk and task cells, records, big numbers; a box answers for
  its payload). A task that one reference holds is not reported (natively
  a task from `Task.spawn` is multi-threaded, and so reported as shared).
- **Why:** lean2rr's objects have no Lean layout to compare byte by byte;
  answering "shared" only makes such code take its general path.
- **Where:** `runtime/prelude.rr`: `lean_is_exclusive_obj`,
  `lean_is_scalar`, `lean_sharecommon_quick`, `lean_dbg_trace_if_shared`
  (`runtime/leanrt/src/lib.rs`: `is_shared`); `Lower/ExternCall.lean`:
  `customExtern` (`ShareCommon.State.shareCommon`);
  `lean2rr/L2RShim/Core.lean` (`lean_sharecommon_eq`/`hash`).
- **Remove only if:** never (plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features)).
