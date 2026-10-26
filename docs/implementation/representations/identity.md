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
  `l2r_ptr_addr_obj`, and for a shared Reussir record `recordAddr`
  (`LowerBase.lean`: `l2r_ptr_pass` notes the handle's word and gives the
  value back to Reussir's own release, `l2r_consume`, which LLVM folds with
  the caller's increment; `l2r_ptr_passed` reads the word, before the
  value's release, with nothing in between: Lean code runs on one thread
  at a time; until clean step A1 the texture `l2r_ptr_addr_rec` decremented
  a shared record's count in line itself: 66edbfb, `ptrEq` in a traversal
  spent 40% of its time in an out-of-line release before),
  `l2r_addr_word`, `l2r_addr_nat`,
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
  arrays, thunk and task cells, big numbers; a box answers for its
  payload). A task that one reference holds is not reported (natively
  every task the task manager runs, from `Task.spawn`, `Task.map`,
  `Task.bind` or `IO.asTask`, is multi-threaded, and so reported as
  shared; `Task.pure` is not).
  At a Reussir shared record type (`isSharedRecordTy`: a record or enum of
  the program, a reference, a function value) lean2rr calls the record
  texture `l2r_dbg_trace_if_shared_rec`, and `leanrt::is_shared_record`
  answers from the record's handle word, with no Rust type name. It reads
  only what Reussir states for foreign code (Reussir l2r-base11, upstream
  00906e38): a nullary constructor of a type with a nullary variant may be
  an immediate, a scalar natively and never shared
  (`lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp`): under `tbi`,
  aarch64's default, its top byte is the tag + 1 ("Foreign code may
  decode `tag = top - 1` without dereferencing"); under `immortal` (rrc's
  `--nullary-variant-encoding arch-independent`) it is a dummy box whose
  count is 3 * 2^30, at or above 2^31 (`drop::IMMORTAL`), which a real box
  never reaches ("Foreign code sees a layout-compatible box"); and a box
  begins with the header that reussir-rt's `rc::Rc` mirrors
  (`crates/reussir-rt/src/rc.rs`: "Mirrors the compiler's box header"),
  so the count is read through an `Rc<()>` view of the handle. Thunk and
  task cells and the runtime handles, `Rc` boxes leanrt makes, are read
  through `Rc` too. A record in a box (an element of an `Array`, a value of
  unknown type) is answered by the box, which reads its payload's count in
  line until clean step C makes the box a Reussir type. A function value
  without captures that Reussir encodes as an immediate is not reported,
  where natively such a closure is usually a persistent closed term and
  reported as shared.
- **Why:** lean2rr's objects have no Lean layout to compare byte by byte;
  answering "shared" only makes such code take its general path.
- **Where:** `runtime/prelude.rr`: `lean_is_exclusive_obj`,
  `lean_is_scalar`, `lean_sharecommon_quick`, `lean_dbg_trace_if_shared`,
  `l2r_dbg_trace_if_shared_rec` (`runtime/leanrt/src/lib.rs`: `is_shared`,
  `is_shared_record`; unit tests `tests::shared_by_storage_type`,
  `tests::shared_record_and_immediates`); `Lower/ExternCall.lean`:
  `customExtern` (`ShareCommon.State.shareCommon`, `dbgTraceIfShared`),
  `LowerBase.lean`: `isSharedRecordTy`; tests `RtDbgShared`,
  `RtDbgSharedRecords` (nullary constructors under both encodings),
  `RtTraceShared`, `RtReprShare`;
  `lean2rr/L2RShim/Core.lean` (`lean_sharecommon_eq`/`hash`).
- **Remove only if:** never (plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features)).
