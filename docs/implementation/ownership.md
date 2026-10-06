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
  `RtDropOrderRec`; `RtArrayRecordFreeOrder`: one release of an array of
  structures that hold handles, an array of handles and unresolved
  promises, whose file and dependents fail if elements whose last
  reference goes were released outside the stack, in field order). The
  order still differs at the top of a free that
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

### A set releases a replaced record with its decrement in line

- **What:** An array set (`leanrt::array::set`, the texture
  `l2r_array_set`, behind `Array.set`, `set!`, `uset`, `fset`) releases
  the element it replaces first, then stores the new one, as
  `lean_array_uset`; a pop (`array::pop`) releases the element it removes,
  as `lean_array_pop`. For a Reussir record (`Bridge` elements, aarch64,
  8 bytes) only the decrement is in line, as `rc.dec` does it: an
  immediate is skipped and a count above 1 is decremented, as the array
  free does (`drop::ReleaseElems`). The last reference goes to
  `array::release_last` (`#[cold] #[inline(never)] extern "C"`), which
  frees the record as `lean_dec` does (`drop::release`): inside a free the
  runtime starts, so its fields go in Lean's order, the last one first,
  and the `sync` dependents of the promises it drops unresolved run when
  that free ends, before the set returns. Other element types are dropped
  in line as before (a handle's decrement, its free out of line).
- **Why:** With the record's whole release in line (its fields' tagged
  decrements, `big::free`, `__reussir_deallocate`), the set texture was
  too big for LLVM to inline into Reussir code: unionfind's
  `l2r_array_set<nodeData>` stayed a call at all five sites (6.9% of its
  instructions, 29 per call, about 12 of them the call's own cost, in an
  instruction-count profile of the classic programs); now none is. That
  in-line release also freed the record through its own release, which
  frees the first cell's fields in field order: a structure of two handles
  `{a, b}` replaced by a set (or removed by a pop) closed `a b`, natively
  `b a` (review RS10-01 of switch step 10; dev had it too; tests
  `RtArraySetFreeOrder`, `RtArrayPopFreeOrder`). `extern "C"`:
  `drop::run` may unwind, and a Rust call is then an invoke with a landing
  pad in the texture, which stayed a call at six sites of `RtArraySets`.
  Cost, switch step 10 (cachegrind, small sizes, against dev): a set that
  frees the replaced record pays for the free the runtime starts, about
  140 instructions (`drain_slow` 64, `run_step` 33, `step_record` 11,
  `release_last` 11, the stack's `memmove`/`memcpy` 13, `free_record` 3),
  the same per-free cost as a reference set that frees its old value
  (`l2r_rc_set`). Correctness first: unionfind (174,000 freeing sets of
  `{find, rank : Nat}`) runs 4.6% more instructions than dev (9.4% more
  than with the record's own release out of line, which had it 4.4%
  fewer); a micro loop of 300,000 sets each freeing a record of scalars
  118% more, one with a record of two strings too 50% more. A set whose
  replaced record is shared only decrements it in line: liasolver 3.9%
  fewer instructions (the sets of a hash map's buckets), monadic-interp
  0.6%. The immediate test costs 2 instructions per set of a record.
  `tests/runtime/ffi-inline-check.sh` builds `RtArraySets` (sets of
  every element representation in loops) to LLVM IR and fails when a
  set's texture or function stays a call; dev's runtime kept the two sets
  of the structure there. At a call site that LLVM judges cold (deep in
  branches) every set texture, of any element type, is still a call: the
  uniqueness test with its copy, the bounds check with its panic and the
  store are above LLVM's cold-site threshold (Reussir issue 36).
- **Where:** `runtime/leanrt/src/array.rs`: `ReleaseElem`,
  `release_last`, `set_in`, `pop_in`; `runtime/leanrt/src/drop.rs`:
  `release`; tests `RtArraySets`, `RtArraySetFreeOrder`,
  `RtArrayPopFreeOrder`, `tests/runtime/ffi-inline-check.sh`.
- **Remove only if:** never; the immediate skip depends on patch 0006, as
  the array free's. A cheaper free of the last reference (a free-stack
  drain that costs less, or the record's own release for element types
  with no observable release) would remove the cost.

### Reads give their reference up first, for a view

- **What:** Every FFI call consumes its arguments, so an array read is the
  caller's increment and the read's decrement. A read gives its reference
  up before anything else: `l2r_array_give` (`leanrt::array::give`;
  `tagvec::give` for `Array Nat`/`Array Int`) decrements a shared array
  and returns a *view*, a `u64`: the block's address, with bit 0 set for a
  shared array (the last reference keeps its count of 1, bit 0 clear). The
  bounds check comes next, in Reussir code (`l2r_view_size`); then
  `l2r_view_take` clones the element (the last reference then frees the
  block out of line, `free_vec`), or `l2r_view_end` ends the view (`get!`
  out of bounds). Nothing is released between `give` and `take` or `end`:
  `get!` releases its default in bounds after the take (`l2r_consume`, a
  use that keeps it alive until then), where Reussir would release it at
  the start of the branch. The failing branch
  of a read that a proof keeps in bounds releases nothing and ends the
  program: a big index is
  unreachable code, a small one `index_bug` (`l2r_index_fail`,
  `l2r_array_index_bug`). String reads decide their release before their
  rule runs (`leanrt::string::read_owned`); `get_fast`/`next_fast` take
  the position's word, and a big one is unreachable code inside the
  texture (`l2r_string_get_fast_word`, `leanrt::index_word`); the
  `Pos.Raw` reads turn a big position into `u64::MAX` without a call
  (`l2r_pos_of_word`) and release it after the read.
- **Why:** LLVM removes the increment and the decrement together only when
  no call and no other store come between them on any path (Reussir's
  `rc.inc` lets it assume the old count was at least 1; so do the
  runtime's clones of array and string handles, such as a constant's read,
  `l2r_once_get`: [startup/constants.md](startup/constants.md), "A read of
  a constant is one load"). Three earlier
  forms kept them (lean-zip's LZ77 loop, count stores on its hot paths;
  perf-array-reads): the texture checked the bounds and released after
  (the panic's call came between: 77 stores; and 279 of lean-zip's array
  reads stayed calls, too costly for LLVM); a check in Reussir code before an
  unchecked texture left a release in the failing branch, so the
  increment had two decrements, one on each side, and dead-store
  elimination needs one store that overwrites it on every path (58); one
  checked texture that decrements first costs 55 in LLVM's inline cost
  model, above its threshold for a cold call site, 45 (41 of the loop's
  reads stayed calls; [Reussir issue 36](../../reussir-bugs/36-trampoline-inline.md),
  a missed optimization). Split into `give`, `size` and `take`, each
  texture is small enough for a cold call site: no read stays a call, and
  the loop has 47 hot stores, at most 7 on one iteration (15 before).
  Bit 0 is set for the shared case because LLVM does not know that the
  block's address is even: after the caller's increment it sees the view
  `o | 1` and folds the test; with the bit set for the last reference it
  kept the test, unswitched loops on it and kept the clone of a record
  element. `view_take` clones in line on both of its paths, so that a
  later release of the element cancels against the clone. `get!`'s default
  released at the start of the in-bounds branch could hold the other
  reference to the array (a tree's child or the tree itself, `cs[i]!` with
  the tree as the default; a closure that captures the array): it freed
  the block the view then read (review PAR-01, test `RtArrayGetDefault`).
  Left to LLVM: a
  loop body whose slow path (a big number's `nat_add`, a call) rejoins the
  fast path keeps a count store per iteration. GVN reloads the count after
  the call, so the count becomes a phi: LLVM can no longer tell that it is
  above 1, or the store writes a phi of loads back, which dead-store
  elimination does not take for a no-op (one store per iteration in a
  `ByteArray` sum over a `USize` index; in lean-zip's `ugetUInt32LE`, an
  increment and a decrement per call). The increments before calls that
  take the array (`updateHashesMerged`) are the cost of owned parameters,
  not of reads.
- **Where:** `runtime/prelude.rr`: `l2r_array_give`, `l2r_view_size`,
  `l2r_view_take`, `l2r_view_end`, `l2r_array_get`, `l2r_array_get_word`,
  `l2r_index_fail`, `l2r_array_index_bug`, `lean_array_get`,
  `lean_byte_array_get`, `lean_float_array_get`, the string reads;
  `runtime/gen_tagarr.py`: `l2r_natarr_give`, `l2r_natarr_view_take`,
  `l2r_natarr_get`, `lean_natarr_get` (and `intarr`);
  `runtime/leanrt/src/array.rs`: `give`, `view_size`, `view_take`,
  `view_end`; `tagvec.rs`: the same and `view_take_slow`; `string.rs`:
  `read_owned`; `lib.rs`: `index_word`; tests `RtArrayReadViews`,
  `RtArrayGetDefault`, `RtReadsDeep`, leanrt's unit tests `views`; plan §10
  ("Reads take their container owned").
- **Remove only if:** Reussir gets borrowed FFI parameters (a feature
  request; plan [§9](../translation-plan.md#9-open-items)). A view is
  valid only while nothing else runs between `give` and `take` or `end`:
  no Lean code (one thread runs Lean code, and the bounds check calls
  none), and no release of another owned value that Reussir inserts there
  (a value used only on one branch is released at the branch's start: such
  a value must be consumed after the take, as `get!`'s default is).
  `tests/runtime/ffi-inline-check.sh` checks that the read textures stay
  inlined at cold call sites (`RtReadsDeep`).

### A read's index is passed in a `let`

- **What:** lean2rr binds the `Nat` arguments of a read extern (`a[i]'h`,
  `a[i]!`, the byte, float and one-word arrays' reads, the string reads at
  a `Nat` position: `readExternSyms`) by a `let` before the call:
  `let k = i; read(a, k)`. That is the index, and also `get!`'s default at
  `Array Nat` (a `Nat` too; harmless). `String.Pos.Raw.get?` goes through
  lean2rr's glue (`Lower/Externs.lean`, `lean_string_utf8_get_opt`) and is
  not covered.
- **Why:** Reussir increments a variable that is used again later where it
  is used, the arguments of a call from left to right. As a direct
  argument, an index used after the read (`a[i]`, then `i + 1`) was
  incremented after the array; the increment of a big index is a store
  that LLVM cannot tell from the array's count, and between the array's
  increment and the read's decrement it made LLVM reload the count and
  keep both. With the `let`, Reussir increments the index at the `let` and
  the array at the call, the last store before the read. Reussir keeps the
  `let` (its front end does not propagate copies). Lean-zip with the
  runtime's reads above: the LZ77 loop's hot stores 72 → 47,
  `updateHashesMergedH3FastU` 12 → 4.
- **Where:** `Lower/ExternCall.lean`: `readExternSyms`, `bindReadIndex`,
  both final calls of `lowerExternCall`.
- **Remove only if:** Reussir gets borrowed FFI parameters, or increments
  a call's arguments in another order.

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
