# Arrays

`Array α` is the runtime's copy-on-write vector `RVec<S>`, updated in place
when unique. Paths: `lean2rr/LeanToReussir/` for lean2rr's files,
`runtime/` for the runtime. Plan
[§5.1](../../translation-plan.md#51-type-translation).

### Elements are stored in their storage type

- **What:** `S`, the storage type of `α`, is `α`'s own representation when
  that can cross Reussir's FFI boundary (integers, floats, `bool`, runtime
  handles, `Nat` and `Int` among them, shared records, function values);
  otherwise a generated one-field shared struct `ElemBox` around it
  (`[value]` structs, Reussir closures; `Nat` and `Int` too before
  mem-nat). The same storage
  wraps once-cell values and the type-parameter arguments of extern
  instances.
- **Why:** Reussir's FFI passes only integers, floats, `bool`, opaque
  types and shared records; `[value]` records, closures and `unit` do not
  cross it (plan [§9](../../translation-plan.md#9-open-items), probe
  results). Lean boxes array elements too.
- **Where:** `LowerBase.lean`: `isBoundaryTy`, `arrayElemTy`,
  `arrayStorage`, `storageElem`, `ArrayRepr`, `arrayRepr?`.
- **Remove only if:** Reussir passes `[value]` types across the FFI (a
  feature request).

### An array is one block

- **What:** `RVec<S>` (and `LRef<S>`) is `leanrt::drop::Vec<S>`, a
  `#[repr(transparent)]` pointer to one `mi_malloc` block: a 24-byte header
  (the `u32` reference count Reussir's `rc.inc` bumps, padded; the size;
  the capacity), then the elements inline. `Clone`/`Drop` do the counting;
  `leanrt::array` allocates (a fresh block's size rounded up to 8 bytes,
  the rest capacity), grows a unique block in place (`mi_realloc`, at least
  doubling, to a whole mimalloc block) and copies a shared one
  (copy-on-write). `ByteArray.mk`/`data` stay the identity.
- **Why:** It was Reussir's `reussir_rt::collections::vec::Vec` (an `Rc`
  around a Rust `Vec`): two allocations per array, a 32-byte counted box
  and the buffer, and every element read loaded the buffer pointer first.
  Reussir needs nothing of an opaque type but the count at the handle's
  address (`rc.inc`, `rc.assume_unique`) and its drop hook, so the layout
  is the runtime's choice. One block: one allocation per array instead of
  two, 8 bytes less, and fewer instructions in array loops (an in-place
  quicksort 0.87x, perf-rvec).
- **Cost:** An array asked for with a payload of exactly 16 MiB (2^21
  buckets of `Std.HashMap`) is, with its header, past mimalloc's
  large-object limit: a huge segment, purged 100 ms after it is freed, so
  hashmap with 0.8M-2M keys peaks up to 24% higher than with the buffer
  apart (as natively). Elements kept apart above 64 KiB (a capacity test
  in every access) or `arena_purge_mult = 0` remove that; the first cost
  7-19% more instructions in array loops, the second changes how mimalloc
  reuses huge memory (needs a timing session).
- **Where:** `runtime/leanrt/src/drop.rs`: `Hdr`, `elems`, `Vec`,
  `free_vec`, `step_vec`, `ReleaseElems`; `runtime/leanrt/src/array.rs`:
  `alloc`, `grow`, `make_mut`, `copy_shared`, `CloneInto`, `from_vec`,
  `bytes_filled`; `runtime/prelude.rr`: `RVec`, `LRef`, the `l2r_ref_*`
  textures.
- **Remove only if:** never (a storage type above 8 bytes or 8-aligned
  would need the element offset and allocation alignment generalized:
  `elems` rejects one at compile time).

### Bytes read go straight into the array

- **What:** `Handle.read` (so `IO.FS.readBinFile`), reads of standard input
  and `IO.getRandomBytes` allocate the byte array first and read into its
  block (`array::bytes_filled` over lean-runtime's `Handle::read_uninit`
  and `RandomSource::fill_uninit`), keeping the
  capacity asked for, as `lean_io_prim_handle_read`.
- **Why:** With the elements inline, a buffer read and then turned into an
  array is a second copy: reading a 256 MiB file peaked at twice its size
  (review RVA-01; test `RtReadIntoArray`). The old two-allocation array
  adopted the buffer.
- **Where:** `runtime/leanrt/src/array.rs`: `bytes_filled`;
  `runtime/leanrt/src/fs.rs`: `lean_read`, `read_bytes`,
  `get_random_bytes`; `runtime/leanrt/src/io.rs`: `stream_read`;
  lean-runtime's `src/io/cfile.rs`: `read_uninit`, `xsgetn`.
- **Remove only if:** never (the other byte arrays the runtime builds from
  a `Vec`, a process's output or a socket's data, are copied once; a
  process's output is copied into a string afterwards anyway).

### A release tests `count == 1`

- **What:** The `Drop` of an array (`leanrt::drop::Vec`, also
  `tagvec::TagVec`, `string::LStr`, `array::release`) and of a thunk or
  task cell (`drop::Cell`) frees when the count is 1 and otherwise
  decrements; never `count > 1`. Its free path is an `extern "C"` function
  (no unwinding, no landing pads in the textures). A cell's read
  (`l2r_lcell_get`, `drop::cell_get`) releases the cell before it copies
  the state.
- **Why:** Reussir's `rc.inc` asserts that the old count was neither 0 nor
  `u32::MAX`; a read's texture, inlined, releases right after the
  caller's increment, and with `== 1` LLVM sees that the free cannot
  happen and cancels the pair (and the bounds check behind it). With
  `> 1` it cannot exclude a wrapped count: an in-place quicksort ran 1.6x
  the instructions (perf-rvec). For a cell, copying the state first
  increments the state record, which LLVM cannot tell from the cell, so
  the cell's count was reloaded and tested; deciding the release first
  (the last reference moves the state out) lets the pair fold: reading a
  finished thunk in a loop runs 0.81x the instructions (perf-cell).
- **Where:** `runtime/leanrt/src/drop.rs`: `Vec::drop`, `free_vec`,
  `Cell::drop`, `free_cell`, `cell_get`; `runtime/prelude.rr`:
  `l2r_lcell_get`.
- **Remove only if:** never.

### Enumerations and `Unit` in arrays are indices

- **What:** An array of an enumeration (a field-less `[value]` enum) or of
  `Unit` stores each element's constructor index, as `u8`, `u16` or `u32`
  by the number of constructors. Internally the storage type is
  `L2RIx<w, T>` (so different enumerations stay distinct); it renders as
  `w`. Generated `l2r_ix_of_T`/`l2r_ix_to_T` convert; an index past the
  last constructor gives the last one, and an empty enumeration is
  unreachable.
- **Why:** An `ElemBox` per element was one allocation each; natively Lean
  stores a tagged scalar (adv4 K2, 23e65fb).
- **Where:** `LowerBase.lean`: `ixStorage?`, `arrayStorage`,
  `ArrayRepr.store`, `ArrayRepr.load`; `RR.lean`: `Ty.render`.
- **Remove only if:** never. Once-cell values and other extern arguments
  of such types are still wrapped (plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Element storage").

### `Array Nat` and `Array Int` store one word per element

- **What:** With the optional pass `nat-arrays`, `Array Nat`/`Array Int`
  are the runtime's `LNatArr`/`LIntArr`, which store the elements' own
  words ([nat-int.md](nat-int.md): a small value's `lean_box`, a big
  number's pointer); the handles move in and out as their words. The
  object is one block laid out like Lean's array
  object, with the same 24-byte header (a `u32` count that Reussir's
  `rc.inc` bumps, size, capacity, then the words), a pointer of type
  `leanrt::tagvec::TagVec` that does its own counting. Every `lean_array_*`/
  `l2r_array_*` function has a `natarr`/`intarr` counterpart with the same
  arguments, generated by `runtime/gen_tagarr.py`.
- **Why:** Before mem-nat, `Nat`/`Int` were `[value]` enums and a generic
  `RVec` boxed each element (adv4 PF4-08, a74072b; runtime request 11);
  then a generic `RVec<Nat>` (one word per element) was two allocations.
  Since arrays are one block (above), `RVec<Nat>` has the same memory
  layout as a tag vector; whether the pass still pays for itself is open.
- **Where:** `LowerBase.lean`: `lowerTypeApp`, `natArrSym?`;
  `Lower/ExternCall.lean`: `lowerExternCall`; `Opt/NatArrays.lean`;
  `runtime/leanrt/src/tagvec.rs`; `runtime/gen_tagarr.py`.
- **Remove only if:** the pass is off (arrays like the others). The
  header was 40 bytes (with a `Box<dyn Any>` marker) until mem-layout
  (7a784e1): 6M small rows took 431 MB, now 336 MB (native 338).

### Shared copies keep their capacity for a push

- **What:** A push onto a shared array copies it with the capacity
  `lean_array_push` gives (its own, unless below `2 * size + 1`); other
  updates of a shared generic array copy it to its size (rounded up to 8
  bytes), while a tag vector keeps its capacity (`lean_copy_expand_array`);
  `Array.mkEmpty` and `ByteArray.emptyWithCapacity` reserve what is asked,
  after Lean's allocation checks; growing blocks take whole mimalloc
  blocks.
- **Why:** A literal `#[a, b, c]` pushes onto a shared empty closed term of
  capacity 3: copied with capacity 0, it grew three times (PF4-08,
  a74072b). Capacities were capped at 2^24 elements, so large buffers grew
  by copying (1.73x memory, adv4 K3, b97cdcd). Blocks that fell just past
  a mimalloc size class wasted 35 MB growing a 10M-element `Array Nat`
  (de0352f).
- **Where:** `runtime/leanrt/src/array.rs`, `tagvec.rs`.
- **Remove only if:** never.

### `Array T` inside `T`'s own fields

- **What:** A field `Array T` of `T` (a rose tree's children) has the
  representation `Array T` has everywhere else.
- **Why/Where:** see
  [records.md](records.md#whether-a-type-is-a-shared-record-is-decided-before-its-fields).
- **Remove only if:** never.

### `Array.mk`, `Array.toList` and list folds are generated loops

- **What:** `Array.mk` and `String.mk`/`String.ofList` fold their list with
  a generated tail-recursive function (`listFold`); `Array.toList` is a
  generated loop that conses the elements from the last
  (`l2r_array_to_list_<list type>_<family>`). Lists whose elements have no
  representation (`Array Type`, `Array Prop`) are handled (adv2 D3,
  0cba3ff).
- **Why:** These externs take or return Lean-defined `List`, which the
  runtime cannot name; a loop keeps a 10^7-element list within an 8 MB
  stack, as natively (plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Stack depth").
- **Where:** `Lower/ExternCall.lean`: `customExtern`;
  `Lower/Externs.lean`: `listFold`.
- **Remove only if:** never.

### Maps that change the element representation write a new array

- **What:** A `map` loop whose element representation changes
  (`Nat → Bool`) gets a split instance over the source `Array α` and a new
  result `Array β` created with the source's size as capacity: reads at
  `α`'s representation, the placeholder written back into the source,
  each mapped value pushed onto the result. No split when the stored
  values' type is `◾` (a value Stage 3 did not recover).
- **Why:** Otherwise the loop runs on an array of `Box`es, converted on
  entry and on exit (adv4 PF4-07, d044198); nested maps and a first
  iteration Lean specialized apart are split too (round 6 PRG6-01: up to
  22x native memory; RV6L-02: 3.5x). A split at `◾`, a map projecting a
  field of a parametric structure (`(xs.zip ys).map (·.2)`), stored
  placeholders or panicked "unreachable" (round 7 RV7D-01, a9b89e6; test
  `RtMapProjFields`).
- **Where:** `Opt/SplitMapLoops.lean`: `splitMapLoops`, `loopShape?`,
  `ensureSplit`, `buildSplit`, `splitCode`, `splitEntries`; plan
  [§4](../../translation-plan.md#4-stage-3--check-and-recover-lost-types).
  Optional pass `split-map-loops`.
- **Remove only if:** the pass is off (correct, slower). Cost when on: the
  two arrays live together until the map ends (0.7-1.1x native peak
  memory for scalar targets).

### Updates of a uniform container run on it (`uniform-updates`)

- **What:** After Stage 3's fixpoint, in each declaration: a call of an
  `Array` extern at a precise type whose array argument is uniform
  (`Array lcAny`) calls the extern's instance at `lcAny` instead. The
  single element is boxed going in, or unboxed when the binder stays
  precise (`get`, `size`). When the result is itself a container, its binder
  becomes `Array lcAny`; that needs one use of it to expect exactly that
  type and every other use to expect it or a precise type it converts to (a
  read, converted at that use: review C02R-02), and a chain of such calls
  counts (greatest fixpoint), as does a join point's parameter of a precise
  container type that a jump passes a uniform value (or a planned uniform
  result), every other jump that or a precise array (converted at that
  jump), and whose uses fit as above (candidate parameters are made until
  none is added, since one join point's planned parameter can be the jump
  argument another needs). Then `uniformParams`: a declaration's
  parameter of a precise array type that every call site (partial
  applications included; `callSites`) passes a uniform array becomes uniform
  when, with that type, the body after the pass uses it only where a uniform
  array is expected and its recursive calls pass a uniform array (a lifted
  closure capturing the column, a fold loop). A constructor
  application whose uses all expect one uniform type (`i :: d` at
  `List lcAny`) is built at that type, if its fields then need at most a box.
  A call is changed only if it receives a uniform value that the current
  call would convert.
- **Why:** A column `data : Array ty.denote` (the element type depends on a
  value) is `Array lcAny`. Each `push` at `Array Nat` converted the whole
  array there and the result back into the field: two O(n) copies per
  update, quadratic in a loop (review RV9C-02: C9DepPush 40000 pushes 7.7 s
  for 0.00 s natively; C9Columns 29 s for 0.07 s; through a join point
  typed at `Array Nat`, review C02R-01: 20000 `modify` steps 3.84 s for
  0.00 s). Natively the cast is free
  and the update is in place. Externs do not depend on their type
  arguments, so the `lcAny` instance computes the same thing.
- **Where:** `Opt/UniformUpdates.lean`: `uniformUpdatesDecl`;
  `MonoRetype.lean`: `Stage3Config.uniformUpdates`, called at the end of
  `retypeMono`; plan [§4](../../translation-plan.md#4-stage-3--check-and-recover-lost-types)
  and §10 "Structural conversions". Tests `RtUniformUpdates`,
  `RtUniformUpdatesJp`, `RtUniformUpdatesMixed`, `RtUniformUpdatesNested` (review C02R-02: a rare
  `foldl`, a closure capture, a fresh array on a rare path kept the chain
  precise: 20000 steps 4.2 s for 0.09 s), `tests/runtime/conv-count-check.sh` (the elements
  conversions rebuild, counted at two sizes: `L2R_COUNT_CONVERSIONS` makes
  every generated conversion count the array elements or constructor
  cells it rebuilds, `Lower/Conv.lean`: `countConversion`; off by default,
  so ordinary builds are unchanged).
- **Remove only if:** the pass is off (correct, quadratic on such loops).
  Cost when on: none where no uniform container meets a precise use.
  Not covered (plan §10): a function taking `Array Nat` that another call
  site keeps typed (a typed argument, a use as a function value, a recursive
  call with a precise array) is not retyped, so a column passed to it at
  every step is converted at every call (review C03R-01, test
  `RtUniformUpdatesShared`). The fix would be a copy of the function with
  the parameter uniform for the uniform call sites (cloning, as Stage 1
  makes instances), not a retyping of the function itself.

### `Array Nat` literals of small numbers are built from tables

- **What:** With `nat-arrays`, a run of 32 or more small `Nat` literals
  pushed onto an `Array Nat` becomes one call that pushes the words of a
  generated table.
- **Why/Where:** see
  [../startup/constants.md](../startup/constants.md#long-array-nat-literals-become-tables).
- **Remove only if:** see the linked entry.
