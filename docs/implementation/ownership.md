# Ownership and runtime glue

Reussir does all reference counting and reuse (Perceus); lean2rr adds none
of its own, except where Lean's *timing* of a release is observable or
where the runtime's containers must cooperate with Reussir's drop glue.
Paths: `lean2rr/LeanToReussir/` for lean2rr's files, `runtime/` for the
runtime.

### Borrowed parameters are emulated for resources

- **What:** Only in a program that creates resources (files, temporary
  files, child processes, promises), lean2rr runs Lean's own borrow
  inference on copies of its declarations and keeps an owned argument that
  may hold a
  resource, passed to a borrowed parameter, alive until the call returns
  (`l2r_release_after`); arguments the caller only borrows itself are left
  alone, so loops keep their tail calls, and function values go through
  `<fn>_boxed` variants. Whether a value may hold a resource is decided
  on the mono type of the parameter it is passed to (`mayHoldResource`:
  an `lcAny`, a handle, or an inductive, array or reference with such a
  field at its type arguments), not on its Reussir type: with one type
  per inductive, a `List Nat` holds `Box`es, as a list of handles does.
  Lean takes every parameter of an exported declaration (`@[export]`, and
  `main`) owned, and decides that by name (`isExport`): the instances of
  such a declaration (`helper._l2r_0`) are marked exported in the copy of
  the environment that the inference uses. The rules are in plan §5.8,
  "Borrowing". The inference runs on lean2rr's code after the optional
  passes, so a pass that changes code keeps Lean's code where a value may
  hold a resource: `flatten-structs` leaves alone each declaration with a
  parameter or a result that may hold one, and each declaration whose
  borrow flags decide the flag of such a parameter (a callee that gets a
  field of it), and keeps whole each join point parameter that may hold
  one; a whole-program flow analysis of the values decides which
  (`Opt/ResourceFlow.lean`;
  [optional-passes.md](optional-passes.md#structure-arguments-and-results-are-spread-into-their-fields-flatten-structs)).
- **Why:** Natively the caller releases a borrowed argument after the
  call; Reussir releases at the last use, inside the callee. Only resources
  can tell: a handle written by a helper that then reads the file again
  (natively still buffered), a child's stdin pipe a helper writes and then
  waits on (natively no end of file yet) (3f72016, test `RtBorrowRelease`).
  A promise can tell too: its last reference resolves its `result?` task
  with `none`, so a helper that asks `IO.hasFinished` after its last use
  of a borrowed promise got `true`, natively `false` (hunt3 own, test
  `RtBorrowPromise`). The instances of an exported declaration have other
  names than the declaration: their parameters were inferred borrowed, so
  a handle written in an exported helper stayed open until the call
  returned, where natively the helper's last use closes it (hunt3 own,
  test `RtBorrowExport`). An element read with `a[i]!`
  (`Array.get!Internal α inst a i`) derives from the array and from the
  `Inhabited` instance (its value out of bounds): it is borrowed only when
  both are, as in Lean's `explicitRc`. `borrowedVars` read argument 1 (the
  instance) as the array: with an instance parameter and an array of the
  function's own, the element was not kept and closed inside the callee
  (hunt3 own, test `RtBorrowGetBang`); with the array alone checked, an
  instance the function builds (`⟨some h⟩`) was not kept either (review,
  test `RtBorrowGetBangDflt`). Values that Lean's inference does not make
  owned and after which its `explicitRc` puts no `dec` are borrowed too:
  the value of a constant (a closed term such as `#[]`, Lean's
  `fap c #[]`), a constructor applied to no variable (it holds nothing:
  `none`, a scalar natively, or one whose relevant fields are all `◾`), and a join point's parameter to which every jump passes such
  a value or `◾`. Kept, they broke self tail calls that passed them to a
  borrowed parameter, and loops of 10^6 steps overflowed an 8 MB stack
  (hunt3 own and its review, tests `RtBorrowTailConst`,
  `RtBorrowTailNone`, `RtBorrowTailNoneH`).
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

### Reference sets store the new value before releasing the old one

- **What:** `l2r_rc_set_ref` (references) reads the old value, stores the
  new one with Reussir's `cell::set`, and releases the old one and then
  the reference through `l2r_release_value_then`, an FFI call Reussir
  keeps after the store. The reference (the `L2RRefN` record) is passed
  beside its cell: natively the set borrows it and the caller releases it
  after the set, so when the set is its last use the old value goes
  first, then the reference, which frees the new value.
  `l2r_lcell_set` (thunk, task and promise cells) does the same in Rust.
  Both release with `leanrt::drop::release`, as `lean_dec`: a shared value
  (or an immediate) is only decremented, in line; the last reference to a
  record is freed inside a free the runtime starts (`drop::free_record`:
  the record is one pending cell, see
  [below](#the-last-reference-to-a-record-is-freed-as-one-pending-cell)), so its
  members go on the pending stack and are released last field first, and
  the `sync` dependents of the promises it drops run when that free ends,
  before the caller goes on. Other values are dropped (the runtime's
  containers free themselves that way). A reference's cell holds a `Box`,
  which always crosses the FFI boundary.
- **Why:** As `lean_st_ref_set`: code the release runs (the `sync`
  dependents of a promise it drops) must see the new value. Reussir's
  `cell::set` and Rust's assignment release first (round 7 RV7C-01,
  d5169c4). Releasing through the record's `_ffi_release` let Reussir's
  glue free the old value first field first: the dependents of the
  promises it held ran, and the file handles it held were closed, in the
  reverse of native's order (round 8 RV8T-02); and without patch 40-a
  (required since switch step 6) the end of that free was not seen, so the
  dependents ran late and a condition-variable loop reading its flag first
  waited forever (RV8T-01;
  both 8af8f1a; tests `RtRefSetOrder`, `RtRefSetFiles`,
  `RtSyncLostWakeLoop`, `RtPromiseFreeGlue`). With only the cell passed,
  the cell's last use was the store: when the set was the reference's
  last use, Reussir freed the cell, and the new value with it, before the
  old value (a structure of two handles closed "new.b new.a old.b old.a",
  natively "old.b old.a new.b new.a": test `RtRefSetLastUse`).
- **Where:** `runtime/prelude.rr`: `l2r_rc_set_ref`, `l2r_release_value_then`,
  `l2r_lcell_set` (`l2r_ref_set` too, but `LRef` is no longer used);
  `runtime/leanrt/src/drop.rs`: `release`, `ReleaseValue`,
  `free_record`, `free_unique`, `free_deferred`, `release_record`;
  `Lower/Externs.lean`: `refCellOpPlain`.
- **Remove only if:** the `l2r_release_value_then` detour in
  `l2r_rc_set_ref` can go if Reussir's `cell::set` stores before it
  releases and frees in Lean's order, and the reference is released after
  the set; the order inside `l2r_lcell_set` (plain Rust) must stay.

### Containers free through the thread's pending stack, in Lean's order

- **What:** The prelude's containers (`RVec`, `LRef`: `leanrt::drop::Vec`,
  the runtime's one-block array; `LCell`: `leanrt::drop::Cell`, a
  transparent wrapper of Reussir's `Rc`) have a `Drop` that frees a last
  reference through Reussir's per-thread
  stack of pending work (`reussir_rt::drop`, local patch 13-b), shared with
  the record drop glue. A container freed while a free runs is pushed
  instead; the outermost free pops until empty. An array is freed in
  native Lean's two passes (below): its elements are decremented in index
  order, then those whose last reference went are released from the last
  one, and what an element's release pushes is done before the next one.
  File handles and promises reached during a free are pushed too.
- **Why:** Lean frees iteratively (`lean_dec_ref_cold`); a value deep
  through containers (a tree whose children are in arrays, chains of thunks)
  overflowed the stack (59b2551). Two separate stacks (the runtime's and
  13-b's) released handles in another order than native (6889792, test
  `RtDropOrderRec`; `RtArrayRecordFreeOrder`: one release of an array of
  structures that hold handles, an array of handles and unresolved
  promises, whose file and dependents fail if elements whose last
  reference goes were released outside the stack, in field order). The
  glue's own order must match too: below the first
  cell of a free, 13-b's glue released a cell's last record field after
  the cell, directly, while a later container field had already pushed
  its free, so the record field's contents came out first (review
  RS11-01, test `RtNestedArrayFreeOrder`). Local patch 13-d keeps the last
  record field for last only when no field after it can push work;
  otherwise every record field is pushed, in field order. The order still
  differs at the top of a free that starts at a record user code drops by
  itself (plan
  [§10](../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Order of releases in one free").
- **Where:** `runtime/leanrt/src/drop.rs`: `Vec`, `Cell`, `free_vec`,
  `step_vec`, `free_cell`, `run`, `defer`, `active`;
  [Reussir issue 13](../../reussir-bugs/13-long-list-drop.md) (a missing
  feature; patches 13-b and 13-d).
- **Remove only if:** never; the runtime does not build without patch
  13-b.

### Arrays are freed in native Lean's two passes

- **What:** The free of an array of boxes (on every target) or of
  Reussir records (on aarch64 with 8-byte handles: elsewhere the immortal
  encoding of nullary variants is not told apart, and the generic loop
  releases every element from the last) (`drop::free_vec`, `step_vec`)
  first decrements every element in index order (`ReleaseElems::scan`): an immediate is skipped, a shared element
  is decremented in line, and an element whose count is 1 is kept, moved
  to the front of the block (`len`: the number kept). Then the kept
  elements are released from the last one (`release_from_end`), each with
  what it pushes done before the one before it. Outside a running free the
  first pass runs in `free_vec`, and an array that keeps no element is
  freed without the stack; inside one the array is pushed, and both passes
  run when it is popped. A step may run several times (it stops when a
  release pushes work), so the block's header records that the first pass
  is done: `Hdr::_pad` (`SCANNED`, 1; 0 in every live block).
- **Why:** Native `lean_del_core` decrements every element of an array in
  index order, pushing each one whose count reaches zero, and pops them
  last first. The order differs from one pass from the last element when
  an element is shared inside the array: a value held twice is freed at
  its last index, and a value that a later element also holds is freed
  inside that element's release (review of the runtime's speed items,
  finding F1: `RtArrayDupFreeOrder` printed `dcba` and `cba`, natively
  `dbca` and `acb`). The kept elements' counts stay 1 until they are
  released: each is the array's only reference. The first pass is a
  loop, so a deep nesting of arrays still frees on a small stack
  (`RtArrayDeepSharedFree`: 10^6 levels on 256 KiB). Cost (cachegrind,
  small sizes, minimum of two runs, against one pass from the end):
  monadic-interp -0.53 % (its shared elements are decremented in the first
  pass instead of by the step's loop), sieve +0.25 %, qsort +0.31 %,
  liasolver +0.41 % (an immediate costs 5 instructions instead of 4:
  sieve's million-element `Array Bool`); unionfind, binarytrees, deriv
  and rbtree unchanged.
- **Where:** `runtime/leanrt/src/drop.rs`: `free_vec`, `step_vec`,
  `SCANNED`, `ReleaseElems` (`scan`, `release_from_end`) for `LAny` and
  `Bridge`; tests leanrt's `any::tests::box_array_free_shared_inside`,
  `drop::tests::record_array_free_shared_inside` (aarch64 only),
  `RtArrayDupFreeOrder`,
  `RtArrayDeepSharedFree`. Other element types (scalars, which have no
  release, and strings, whose order is not seen) keep one pass from the
  last element (`release_from_end_each`).
- **Remove only if:** never (native's order).

### Arrays of records release shared elements inline

- **What:** Freeing an array of Reussir records (`Bridge` elements)
  decrements a shared element's count inline and skips nullary-constructor
  immediates (aarch64, 8-byte elements), in the first pass (above); only
  an element whose last reference goes takes the record's out-of-line
  `_ffi_release` and the stack. Outside a running free, an array none of
  whose elements is freed is freed without the stack at all.
- **Why:** One out-of-line glue call per element: `hash-map-heavily-shared`
  1.79x → 1.05x native, `hash-map-shared` 1.33x → 0.84x (perf5, 1dc63c6).
  Inside a free the array is still pushed: a later field of the record
  being freed may hold one of its elements. An immediate is never freed
  (local patch 06-a), so skipping it changes nothing.
- **Where:** `runtime/leanrt/src/drop.rs`: `ReleaseElems`,
  `release_from_end`, `scan`, `free_vec`.
- **Remove only if:** never (speed only); the immediate skip depends on
  patch 06-a ([Reussir bug 6](../../reussir-bugs/06-static-count-wrap.md)).

### Arrays of boxes skip immediates and decrement shared payloads inline

- **What:** Freeing an array of boxes (`LAny` elements: every `Array` of
  a Lean type) skips an immediate (an odd word) and decrements a shared
  payload's count inline, without storing the block's `len` or reading
  the stack's depth (`ReleaseElems for LAny`, its first pass `scan`).
  Only a payload whose count is 1 is released (`any::release_last`, or
  its release called in the step: next section), after `len` is set to
  the elements before it, and only then is the depth read (a payload that
  the release pushed is done before the next element). Outside a running
  free, an array none of whose elements is freed is freed without the
  stack at all (`scan` in `free_vec`), and one that keeps one payload or
  leaf releases it without a step (next section).
- **Why:** The generic loop (`release_from_end_each`) stored `len`, dropped
  the element (`LAny`'s drop, inline) and read the depth for every
  element: 12 to 15 instructions an element, and an array of immediates
  (sieve's million-element `Array Bool`) took the stack's step machinery
  (`run`, `step_vec`): sieve 15.0 M instructions in `step_vec`, now 5.0 M
  in `free_vec` (sieve -2.0 %, qsort -3.2 % without mimalloc's free path;
  cachegrind). Skipping immediates four at a time saved 0.25 % more on
  sieve but cost liasolver 0.55 % (its arrays hold pointers), so it is not
  done. The order of releases is unchanged: the elements
  that release nothing come out as before, and a payload freed is
  released at its place, with what it pushes done before the next
  element.
- **Where:** `runtime/leanrt/src/drop.rs`: `ReleaseElems for LAny`; tests
  leanrt's `any::tests::box_array_free`, `RtNestedArrayFreeOrder`,
  `RtArrayRecordFreeOrder`, `RtDropOrderRec`.
- **Remove only if:** never (speed only).

### The array free calls a payload's release where the stack would pop it next

- **What:** Two shortcuts in the free of an array of boxes
  (`ReleaseElems for LAny`). Neither changes the order of releases.
  - *In the step.* The second pass runs as a step of a running free
    (`step_vec`, `release_from_end`). A kept element that is a program
    payload (leaf or not), other than the last kept element, has its
    release called in the step (`any::release_last_in_step`: the
    program's `l2r_any_rel_<num>_c` from leanrt's table) instead of being
    deferred (`any::release_last`). When the release pushed nothing the
    loop goes on with the element before; when it pushed work the step
    returns to the drain, as before. The last kept element (index 0) is
    still deferred. leanrt's own kinds go to `release_last` as before.
  - *Outside a free.* When no free runs and nothing is pending on the
    stack (`depth() == 0`), an array whose first pass keeps exactly one
    element is freed without a step (`free_single`, called by
    `free_vec`) if that element is a program payload or one of leanrt's
    leaves (a big number, a string, a scalar cell; `any::frees_flat`):
    the block is freed, then the element goes to `any::release_last`. A
    payload that is not a leaf is then deferred and drained
    (`drop::free_deferred`): with nothing else pending, Reussir's drain
    of one cell (`drain_one`) releases it in a drain of its own. A leaf,
    of either kind, is released directly.
- **Why:** MonadicInterp frees about 144,000 old copies of its variables
  array, each holding one count-1 pair of its own, and each went through
  `run_step`, the drain's general loop, `step_vec` and a deferral. Hash
  maps free bucket arrays inside a step, one deferral, one return to the
  drain, one pop and one new call of the step per freed bucket (liasolver
  62,500, hashmap 17,500). Instructions against the same runtime without
  these two shortcuts (cachegrind, small sizes, SVE off, minimum of two
  runs, the `.rr` files identical, outputs equal native, `mi_free`'s
  instructions equal within 0.0001 %): monadic-interp -1.63 %
  (1,055.13 -> 1,037.93 M), liasolver -2.28 % (220.29 -> 215.27 M),
  hashmap -1.25 % (120.84 -> 119.33 M); unionfind -0.01 %, binarytrees
  unchanged. The order:
  - *In the step.* Deferred, the payload's cell would be the only entry
    above the step. The step sees the depth change and returns. The drain
    pops the cell next, and the pop of a run of one cell leaves the step
    as the top entry, so the drain calls the same release with the stack
    as it was in the step. What the release pushes goes above the step in
    both cases, and the depth test returns to the drain, which does that
    work before it runs the step again. When the release pushed nothing,
    the drain runs the step again at once, and the step goes on with the
    element before. So the same releases come in the same order, each
    with the same stack under it (leanrt's `Bridge` loop calls a record's
    `<record>_ffi_release` the same way). The last kept element stays
    deferred: the block is then freed first, as natively (`lean_del_core`
    frees the array, then pops its elements), and the element is released
    after the step's entry is gone. (A leaf payload is released at once,
    in the step, by `any::release_last`: it frees only its own cell, so no
    release can tell the difference.)
  - *Outside a free.* The step would start a drain with the step as its
    only entry. The step frees the block and defers the element (its last
    kept element). The drain removes the step, pops the element and
    releases it with nothing else on the stack, releases what that pushed,
    last first, and ends; its end runs the promise resolutions put off in
    it (`__reussir_drop_drained`). `any::release_last` does exactly that
    for a payload, without the step: it defers the cell and drains, and
    with nothing else pending Reussir's drain of one cell (`drain_one`)
    starts a drain, pops the cell, releases it, releases what that
    pushed and ends the same way. A leaf (a leaf payload or a leanrt
    leaf) frees its own block and nothing else: it has no member and holds
    no promise, so outside a drain it pushes nothing and does the same as
    inside one, and the end of the skipped drain would have run nothing (a
    leaf puts off no resolution, and outside a drain no resolution is put
    off: every drain's end runs those put off in it). Natively,
    `lean_del_core` also frees the block and then pops its one element.
    With work pending outside a drain (a record's `drop_in_place` between
    the members it defers and its drain), the step stays: its drain
    releases that work too before the free returns, and a leaf's direct
    release would leave it for later. An element that is an array of
    boxes keeps the step: released directly, it would be freed by
    `free_vec` again, and a deep nesting of one-element arrays would
    recurse (the unit test `deep_nesting_of_one_element_arrays`: 10^6
    levels on a 256 KiB stack). A `ByteArray` or `FloatArray` element
    would be one `mi_free`, without recursion; it keeps the step only
    because the case is rare.
- **Where:** `runtime/leanrt/src/drop.rs`: `free_vec`,
  `ReleaseElems::free_single`, `ReleaseElems for LAny`
  (`release_from_end`, `free_single`); `runtime/leanrt/src/any.rs`:
  `release_last_in_step`, `frees_flat`. Tests: leanrt's
  `any::tests::box_array_free_releases_in_its_step` (the order, and the
  depth of the stack each release sees, as the deferral's pop gave it),
  `one_kept_element_without_a_step` (also with work pending outside a
  drain), `deep_nesting_of_one_element_arrays`; `RtArrayFreeDirectOrder`
  (the closes in native's order, through both shortcuts),
  `RtArrayDupFreeOrder`, `RtArrayDeepSharedFree`, `RtBoxLeafRelease`,
  `RtNestedArrayFreeOrder`, `RtArrayRecordFreeOrder`, `RtDropOrderRec`.
- **Remove only if:** never (speed only). It depends on how Reussir's
  drain pops a run of one cell above a step and on how it drains one
  pending cell outside a drain (`drain_one`; `reussir_rt::drop`); if
  either changes, the deferral (`any::release_last` in the step) and the
  step (`run`) are the fallback.

### Array copies skip the increments of immediates

- **What:** Copying an array of records (copy-on-write) increments real
  boxes inline, as `rc.inc` does, and skips
  immediates (aarch64 only; elsewhere the generic clone). An immediate is
  a pointer with a nonzero top byte (`tbi`, the default encoding) or one
  to a dummy box whose count is 2^31 or more (`immortal`, which
  `--nullary-variant-encoding arch-independent` selects on aarch64 too):
  both are skipped, here and in the in-line releases of records
  (`drop::ReleaseValue`, `ReleaseElems`, `array::ReleaseElem`), as
  `any`'s `into_any` tells them apart (review HRT-04: the `immortal`
  dummy's count was changed, and after about 2^30 releases it was no
  longer immortal; `drop::IMMORTAL`).
- **Why:** Under Reussir's aarch64 (TBI) encoding of nullary variants,
  which patch 06-a keeps, an immediate's increment is unguarded: every
  `nil` bucket of a hash map incremented the one static dummy of `nil`, a
  serial chain through one word (Pf4HashPersist 1.04 → 0.80 s; adv4
  PF4-11, fe483fe).
- **Where:** `runtime/leanrt/src/array.rs` (`ExtendCloned`, the copy
  paths).
- **Remove only if:** never (speed only).
- **Boxes:** an array of boxes (`LAny` elements) is copied with one
  `memcpy` of its words, and then each pointer's payload count goes up
  (`CloneInto for LAny`); an immediate needs nothing. The generic loop
  cloned and stored each box in turn. Test: leanrt's
  `any::tests::box_array_copy`.

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
  frees the record as `lean_dec` does (`drop::release_unique`, which does
  not test the count again; the record is one pending cell, see
  [below](#the-last-reference-to-a-record-is-freed-as-one-pending-cell)): inside a free the
  runtime starts, so its fields go in Lean's order, the last one first,
  and the `sync` dependents of the promises it drops unresolved run when
  that free ends, before the set returns. Other element types are dropped
  in line as before (a handle's decrement, its free out of line). The
  array of a Lean type holds boxes (`LAny`, rule 1), so a record replaced
  in it is a boxed one: the box's drop has only its decrement in line too
  (`LAny::drop`: an immediate skipped, a count above 1 decremented), and
  the last reference goes to `any::release_last`, which frees a program
  payload as one pending cell as well (next section).
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
  the free may unwind, and a Rust call is then an invoke with a landing
  pad in the texture, which stayed a call at six sites of `RtArraySets`.
  Cost (cachegrind, small sizes): a set that frees the replaced record
  pays for the free the runtime starts, about 74 instructions since
  switch step 11 (about 140 at step 10, when the record was a step: next
  section), the same per-free cost as a reference set that frees its old
  value (`l2r_rc_set`). Unionfind (174,000 freeing sets of
  `{find, rank : Nat}`) runs 0.8% more instructions than dev d39294a
  (step 10: 5.0% more than d39294a). Against dev 9a2ddf6 (step 10's
  micro baseline): a micro loop of 300,000 sets each freeing a record of
  five `UInt64`s runs 63% more (step 10: 118%), one with a record of two
  strings too 19% more (step 10: 50%). A set whose replaced record is
  shared only decrements it in line (step 10, against dev 9a2ddf6):
  liasolver 3.9% fewer instructions (the sets of a hash map's buckets),
  monadic-interp 0.6%. The immediate test costs 2 instructions per set of a record.
  `tests/runtime/ffi-inline-check.sh` builds `RtArraySets` (sets of
  every element representation in loops) to LLVM IR and fails when a
  set's texture or function stays a call; dev's runtime kept the two sets
  of the structure there. At a call site that LLVM judges cold (deep in
  branches) every set texture, of any element type, is still a call: the
  uniqueness test with its copy, the bounds check with its panic and the
  store are above LLVM's cold-site threshold (Reussir issue 36, not
  patched: its patch 36-a, which made every such texture `alwaysinline`,
  is parked).
- **Where:** `runtime/leanrt/src/array.rs`: `ReleaseElem`,
  `release_last`, `set_in`, `pop_in`; `runtime/leanrt/src/drop.rs`:
  `release`; tests `RtArraySets`, `RtArraySetFreeOrder`,
  `RtArrayPopFreeOrder`, `tests/runtime/ffi-inline-check.sh`.
- **Remove only if:** never; the immediate skip depends on patch 06-a, as
  the array free's. The record's own release for element types with no
  observable release, or a cheaper drain of one cell in Reussir's
  runtime, would remove the rest of the cost.

### The last reference to a record is freed as one pending cell

- **What:** `drop::release` (reference and cell sets) and
  `drop::release_unique` (`array::release_last`: a set or a pop that
  removes the last reference) free a record whose count is 1 (aarch64,
  8-byte `Bridge`) with `drop::free_unique`: `drop::free_deferred` calls
  `__reussir_drop_defer(p, release_record::<X>)`, which puts the record on
  the thread's pending stack as one deferred cell (a deferral that is not
  `_wide` writes nothing into the cell), and `__reussir_drop_drain()`
  releases it. Outside a free that is Reussir's drain of one pending cell
  (`drain_one`, local patch 13-b): the drain starts, `release_record` runs
  the record's `<record>_ffi_release` inside it (its fields go on the
  stack and come out last first), and the drain ends, through the general
  loop only when the release pushed work; the end of the drain calls
  `__reussir_drop_drained` (patch 40-a: the promise resolutions put off,
  `task::drained`). Inside a free the drain returns at once: the cell is
  only pushed (above the run on top, which moves to the vector) and is
  released when the free pops it. `release_unique` does not test the
  count again (its caller did). On other targets (the immortal encoding:
  the count is not tested) the record's release is a step (`drop::run`,
  `step_record`). The last reference to a box's program payload is freed
  the same way, on every target (`LAny`'s count is always tested):
  `any::release_last` gives the payload's cell (the box's word without its
  number) to `drop::free_deferred` with `release`, the program's release
  of the payload's type, found by number in leanrt's table
  (`l2r_any_rel_<num>_c`, box-and-uniform.md); a number with `WIDE_BIT`
  goes to `drop::free_deferred_wide` (`__reussir_drop_defer_wide`, which
  links the cell to the run on top: box-and-uniform.md, "A payload whose
  cell has a wide header is deferred `_wide`"). A leaf payload is released
  directly, inside a free too (it frees only its own cell). This covers
  boxed records replaced or removed in an array, a reference's or cell's
  old value, and any other box dropped for the last time.
- **Why:** At switch step 10 the record was a step (`drop::run`:
  `run_step` writes a `Work::Step` into the stack's vector, the drain
  dispatches it and moves the entries above it down with `memmove`):
  about 140 instructions per freed record (`drain_slow` 64, `run_step` 33,
  `step_record` 11, `release_last` 11, `memmove`/`memcpy` 13,
  `free_record` 3). As one pending cell: about 74 (cachegrind, the loop
  of 300,000 sets each freeing a record of five `UInt64`s: `drain_one` 26,
  `__reussir_drop_drain` 18, `__reussir_drop_defer` 17, `release_last` 7,
  `release_record` 6 with the record's own free). The order is the same:
  in both forms the record's release runs inside the drain on top of the
  stack as it was, and the stack is popped last pushed first. Totals
  (step 10 in brackets): unionfind +0.8% against dev d39294a (+5.0%);
  the micro loop 58.1 M instructions (77.9 M; dev 9a2ddf6 35.7 M), with a
  record of two strings too 87.4 M (109.6 M; dev 9a2ddf6 73.3 M); 16 of
  the other 17 classic programs as at step 10 (within 0.02%), and
  binarytrees +2.9%
  from code layout only (an
  identical `.rr`; `check` has four alignment `nop`s before its loop,
  executed once per call, and an erratum-843419 veneer moved to a load
  in `make'`). Reussir's three calls (61 of the 74 instructions) could be
  one: the parked Reussir patch 42-a (reussir-bugs/42-drop-run.md) adds
  that entry point (monadic-interp -4.99% instructions, unionfind
  -2.52%), a gain too small for a local Reussir patch (owner,
  2026-10-07).
- **Where:** `runtime/leanrt/src/drop.rs`: `release`, `release_unique`,
  `ReleaseValue`, `free_record`, `free_unique`, `free_deferred`,
  `release_record`, `step_record`, `free_deferred_wide`;
  `runtime/leanrt/src/array.rs`: `release_last`;
  `runtime/leanrt/src/any.rs`: `release_last`; Reussir's
  `reussir_rt::drop` (`__reussir_drop_defer`, `__reussir_drop_defer_wide`,
  `__reussir_drop_drain`, `drain_one`). Tests: leanrt's unit tests
  `drop::tests::record_free_order` and `record_free_inside_a_free`;
  `RtArraySetFreeNested` (a set, a pop and a reference set freeing
  structures that hold structures and a list), `RtArraySetFreeOrder`,
  `RtArrayPopFreeOrder`, `RtRefSetOrder`, `RtPromiseFreeLaterUnresolved`.
- **Remove only if:** Reussir's pending stack changes what a deferral
  that is not `_wide` does (the drain releases the cell with the given
  function and writes nothing into it) or what a drain of one pending
  cell does; then the step (`run`) is the fallback.

### Reads give their reference up first, for a view

- **What:** Every FFI call consumes its arguments, so an array read is the
  caller's increment and the read's decrement. A read gives its reference
  up before anything else: `l2r_array_give` (`leanrt::array::give`)
  decrements a shared array
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
  a missed optimization, not patched). Split into `give`, `size` and
  `take`, each texture is small enough for a cold call site: no read stays
  a call, and the loop has 47 hot stores, at most 7 on one iteration (15
  before). With the one-word `Box` the read of a box is over that
  threshold again (`view_take<LAny>`: the copy of a box tests its low bit
  and masks its top bits), and so are the reads of a `Nat` or `Int`
  element at its type (`view_take_as`): at a cold call site they stay
  calls (`tests/runtime/ffi-inline-check.sh` allows this in `RtReadsDeep`
  only).
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
  Out of bounds, `get!` panics before it ends the view, as natively the
  panic comes inside the extern and the caller's release of the array
  after it: what freeing the array releases (a handle's flush) follows the
  message, and under `LEAN_ABORT_ON_PANIC` does not happen (review HA-01,
  test `RtArrayGetOobOrder`).
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
  `runtime/leanrt/src/array.rs`: `give`, `view_size`, `view_take`,
  `view_end`; `string.rs`:
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
  `a[i]!`, the byte and float arrays' reads, the string reads at
  a `Nat` position: `readExternSyms`) by a `let` before the call:
  `let k = i; read(a, k)`. That is the index. A parameter declared at a
  type variable (`get!`'s default, at `Array Nat` a `Nat`) is left out
  (`atVar`): its argument is in its storage, a `Box`, and since the
  boxing of a box unboxed at once folds away (`boxUnboxed?`), a box field
  passed as the default is the box variable itself, which a `Nat` `let`
  would mistype (the classic `sieve`'s `omega` passes such a default).
  `String.Pos.Raw.get?` goes through
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
