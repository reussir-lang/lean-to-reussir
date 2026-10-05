# Ownership and runtime glue

Reussir does all reference counting and reuse (Perceus); lean2rr adds none
of its own, except where Lean's *timing* of a release is observable or
where the runtime's containers must cooperate with Reussir's drop glue.
Paths: `lean2rr/LeanToReussir/` for lean2rr's files, `runtime/` for the
runtime.

### Borrowed parameters are emulated for resources

- **What:** Only in a program that creates resources (files, temporary
  files, child processes), lean2rr runs Lean's own borrow inference on
  copies of its declarations and keeps an owned argument that may hold a
  resource, passed to a borrowed parameter, alive until the call returns
  (`l2r_release_after`); arguments the caller only borrows itself are left
  alone, so loops keep their tail calls, and function values go through
  `<fn>_boxed` variants. The rules are in plan §5.8, "Borrowing".
- **Why:** Natively the caller releases a borrowed argument after the
  call; Reussir releases at the last use, inside the callee. Only resources
  can tell: a handle written by a helper that then reads the file again
  (natively still buffered), a child's stdin pipe a helper writes and then
  waits on (natively no end of file yet) (3f72016, test `RtBorrowRelease`).
- **Where:** `Lower/Borrow.lean`: `resourceExterns`,
  `programMakesResources`, `inferBorrowedParams`, `borrowedVars`,
  `borrowInfo`, `mayHoldResource`, `borrowKeeps`, `releaseAfter`,
  `boxedTarget`; `Lower/Values.lean`: `lowerConstApp`;
  `runtime/prelude.rr`: `l2r_release_after`; plan
  [§5.8](../translation-plan.md#58-externs-and-runtime-calls)
  ("Borrowing").
- **Remove only if:** Reussir gets borrowed parameters. Limits: closures
  and thunks are not looked into, and the inference runs on lean2rr's
  instances (plan
  [§10](../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Release time of borrowed parameters"). `IO.Promise.isResolved` is
  replaced for the same reason
  ([externs-ffi/shim.md](externs-ffi/shim.md#iopromiseisresolved-is-replaced-borrow-dependent-behaviour)).

### Lent arguments are released last first, by first occurrence

- **What:** After a call, the kept arguments (`borrowKeeps`) are released
  in the reverse order of their first occurrence among the call's
  arguments: `put3 a b c` releases `c`, `b`, `a`; `put4 w h1 h2 h1`
  releases `h2`, `h1`, `w`; in `own3 x y x` with the first parameter owned,
  `x` counts from its first (owned) position, so `y` goes first. A variable
  is kept when it is passed to a borrowed parameter at any position. The
  `_boxed` wrappers (`boxedTarget`) release last parameter first.
- **Why:** Lean's `ExplicitRC.addDecAfterFullApp` visits the arguments in
  order, takes each variable at its first occurrence (`isFirstOcc`) when
  some occurrence is borrowed (`isBorrowParam`), and *prepends* its `dec`
  to the code after the call, so the `dec`s run last first; `_boxed`
  functions go through the same pass. Handles show the order: each closes
  and flushes its buffer when released, so several handles on one file
  write their texts last first natively (`CBA`). lean2rr released them in
  argument order (`ABC`), and by first *borrowed* occurrence (cross-test
  XT-1, fixtures A545, A612, A613, A621; test
  `RtBorrowReleaseOrder`).
- **Where:** `Lower/Borrow.lean`: `borrowKeeps` (first occurrences, in
  order), `releaseAfter` (reverses them), `boxedTarget`; plan
  [§5.8](../translation-plan.md#58-externs-and-runtime-calls)
  ("Borrowing").
- **Remove only if:** the borrow emulation goes (see above).

### Lean's borrow inference sees lean2rr's typed references as opaque types; a failure is an error

- **What:** `inferBorrowedParams` declares `_l2r.TypedRef` (lean2rr's mono
  type of a reference created at a precise type, `typedRefName`) as an
  opaque type, an axiom `Type → Type`, in the environment it restores
  afterwards, so Lean's `toImpureType` represents it as `tobject`, as the
  `lcAny` that Lean's own mono phase gives every reference. Any failure of
  Lean's passes there is an error (`lean2rr: Lean's borrow inference
  failed on this program (...)`), as is a pass manager without `toImpure`
  or `inferBorrow`.
- **Why:** `_l2r.TypedRef` is not a Lean constant, so `toImpureType`
  failed on it (`Unknown constant`) in every program that has both a
  resource and an `IO.Ref` created at a precise type (`IO.Ref Nat`,
  `IO.Ref HB` with a handle inside, ...). The failure was caught and turned
  into "no borrowed parameters", which switched the emulation off for the
  whole program, silently: a helper's handle was then closed inside the
  helper (cross-test XT-2, fixture A621; test `RtBorrowTypedRef`).
  The emulation is all or nothing, so a failure cannot be skipped without
  changing when resources are released.
- **Where:** `Lower/Borrow.lean`: `inferBorrowedParams`;
  `MonoTypesKeep.lean`: `typedRefName`; plan
  [§5.8](../translation-plan.md#58-externs-and-runtime-calls)
  ("Borrowing").
- **Remove only if:** typed references stop using a constant of their own
  in mono types, or the borrow emulation goes.

### Reference sets store the new value before releasing the old one

- **What:** `l2r_rc_set` (references) reads the old value, stores the new
  one with Reussir's `cell::set`, and releases the old one through
  `l2r_release_value`, an FFI call Reussir keeps after the store.
  `l2r_lcell_set` (thunk, task and promise cells) does the same in Rust.
  Both release with `leanrt::drop::release`, as `lean_dec`: a shared value
  (or an immediate) is only decremented, in line; the last reference to a
  record is freed inside a free the runtime starts (`drop::run`), so its
  members go on the pending stack and are released last field first, and
  the `sync` dependents of the promises it drops run when that free ends,
  before the caller goes on. Other values are dropped (the runtime's
  containers free themselves that way). A value that cannot cross the FFI
  boundary (a unit or enumeration value, whose release runs nothing) is
  stored with `l2r_rc_put` (`refSetFn` chooses).
- **Why:** As `lean_st_ref_set`: code the release runs (the `sync`
  dependents of a promise it drops) must see the new value. Reussir's
  `cell::set` and Rust's assignment release first (round 7 RV7C-01,
  d5169c4). Releasing through the record's `_ffi_release` let Reussir's
  glue free the old value first field first: the dependents of the
  promises it held ran, and the file handles it held were closed, in the
  reverse of native's order (round 8 RV8T-02); and without patch 0040
  (required since switch step 6) the end of that free was not seen, so the
  dependents ran late and a condition-variable loop reading its flag first
  waited forever (RV8T-01;
  both 8af8f1a; tests `RtRefSetOrder`, `RtRefSetFiles`,
  `RtSyncLostWakeLoop`, `RtPromiseFreeGlue`).
- **Where:** `runtime/prelude.rr`: `l2r_rc_set`, `l2r_release_value`,
  `l2r_rc_put`, `l2r_lcell_set` (`l2r_ref_set` too, but `LRef` is no
  longer used); `runtime/leanrt/src/drop.rs`: `release`, `ReleaseValue`,
  `free_record`, `step_record`; `Lower/Externs.lean`: `refSetFn`.
- **Remove only if:** the `l2r_release_value` detour in `l2r_rc_set` can go
  if Reussir's `cell::set` stores before it releases and frees in Lean's
  order; the order inside `l2r_lcell_set` (plain Rust) must stay.

### Containers free through the thread's pending stack, in Lean's order

- **What:** The prelude's containers (`RVec`, `LRef`: `leanrt::drop::Vec`,
  the runtime's one-block array; `LCell`: `leanrt::drop::Cell`, a
  transparent wrapper of Reussir's `Rc`) have a `Drop` that frees a last
  reference through Reussir's per-thread
  stack of pending work (`reussir_rt::drop`, local patch 0014), shared with
  the record drop glue. A container freed while a free runs is pushed
  instead; the outermost free pops until empty. An array is emptied from
  its last element, and what an element's release pushes is done before
  the next one. File handles and promises reached during a free are pushed
  too.
- **Why:** Lean frees iteratively (`lean_dec_ref_cold`); a value deep
  through containers (a tree whose children are in arrays, chains of thunks)
  overflowed the stack (59b2551). Two separate stacks (the runtime's and
  0014's) released handles in another order than native (6889792, test
  `RtDropOrderRec`). The order still differs at the top of a free that
  starts at a record user code drops by itself (plan
  [§10](../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Order of releases in one free").
- **Where:** `runtime/leanrt/src/drop.rs`: `Vec`, `Cell`, `free_vec`,
  `step_vec`, `free_cell`, `run`, `defer`, `active`;
  [Reussir issue 13](../../reussir-bugs/13-long-list-drop.md) (a missing
  feature).
- **Remove only if:** never; the runtime does not build without patch
  0014.

### Arrays of records release shared elements inline

- **What:** Freeing an array of Reussir records (`Bridge` elements)
  decrements a shared element's count inline and skips nullary-constructor
  immediates (aarch64, 8-byte elements); only an element whose last
  reference goes takes the record's out-of-line `_ffi_release` and the
  stack. Outside a running free, an array none of whose elements is freed
  is freed without the stack at all.
- **Why:** One out-of-line glue call per element: `hash-map-heavily-shared`
  1.79x → 1.05x native, `hash-map-shared` 1.33x → 0.84x (perf5, 1dc63c6).
  Inside a free the array is still pushed: a later field of the record
  being freed may hold one of its elements. An immediate is never freed
  (local patch 0006), so skipping it changes nothing.
- **Where:** `runtime/leanrt/src/drop.rs`: `ReleaseElems`,
  `release_from_end`, `release_shared_from_end`, `free_vec`.
- **Remove only if:** never (speed only); the immediate skip depends on
  patch 0006 ([Reussir bug 6](../../reussir-bugs/06-static-count-wrap.md)).

### Array copies skip the increments of immediates

- **What:** Copying an array of records (copy-on-write, `extract`,
  `append`) increments real boxes inline, as `rc.inc` does, and skips
  immediates (aarch64 only; elsewhere the generic clone).
- **Why:** Under Reussir's aarch64 (TBI) encoding of nullary variants,
  which patch 0006 keeps, an immediate's increment is unguarded: every
  `nil` bucket of a hash map incremented the one static dummy of `nil`, a
  serial chain through one word (Pf4HashPersist 1.04 → 0.80 s; adv4
  PF4-11, fe483fe).
- **Where:** `runtime/leanrt/src/array.rs` (`ExtendCloned`, the copy
  paths).
- **Remove only if:** never (speed only).

### Reads take their container owned, and in-bounds indices end on a big index

- **What:** Every FFI call consumes its arguments, so an array or string
  read is an increment by the caller and a release in the inlined texture
  (`leanrt::array::release`, last reference out of line). An index proved
  in bounds, or a position proved valid, converts with
  `l2r_index_of_nat`, whose big case ends the program instead of
  rejoining the read; an index checked by `get!`/`set!` is taken as its
  word once (`l2r_word_index_ok`), with no counting on it in bounds.
- **Why:** LLVM cancels the increment against the release (Reussir's
  `rc.inc` lets it assume the old count was at least 1) only when no store
  or call lies between them; a rejoining big-index path with reference counting
  on the big number broke that (insertion sort on `Array UInt64`:
  0.52 → 0.23 s, native 0.19; adv4 PF4-06, ddb46f1). Natively such an index
  is never big (`lean_unbox` of it would be garbage).
- **Where:** `runtime/prelude.rr`: `l2r_index_of_nat`, `l2r_word_index_ok`,
  `lean_array_get`; `runtime/leanrt/src/array.rs`: `release` (a
  decrement; `drop_last` out of line).
- **Remove only if:** Reussir gets borrowed FFI parameters (a feature
  request; plan [§9](../translation-plan.md#9-open-items)).

### A thunk's cell gives up its closure before running it

- **What:** Forcing a pending thunk or task swaps `busy` into the cell,
  runs the closure it took out, and stores `done(v)`, which Reussir can
  build in the cell the pending state frees.
- **Why:** As `lean_thunk_get_core`, which takes the closure out before
  calling it: the cell no longer holds it, so the closure and its captures
  are released as soon as it has run.
- **Where:** `Lower/LazyForce.lean`: `lazyGetFn`; see
  [tasks/cells.md](tasks/cells.md).
- **Remove only if:** never.
