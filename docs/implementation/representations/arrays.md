# Arrays

`Array α` is the runtime's copy-on-write vector `RVec<LAny>`, updated in
place when unique, whatever `α` is; `ByteArray` and `FloatArray` are
`RVec<u8>` and `RVec<f64>`. Paths: `lean2rr/LeanToReussir/` for lean2rr's
files, `runtime/` for the runtime. Plan
[§5.1](../../translation-plan.md#51-type-translation).

### An array holds `Box`es, whatever its element type

- **What:** `Array α` is `RVec<LAny>` for every `α` (`lowerTypeApp`). A
  value goes into an array by boxing (`Array.push` at `Nat` boxes the
  `Nat`) and comes out by unboxing, at the extern's boundary
  (`lowerExternCall`: an extern over arrays stores its type parameters'
  values as `Box`es). `Array.mk`, `Array.toList` and the map loops of
  Lean's library move the boxes as they are. `ByteArray.mk`/`data` and
  `FloatArray.mk`/`data` convert between an array of `Box`es and the
  runtime's bytes or floats (natively `lean_byte_array_mk` copies too;
  [below](#bytearraymkdata-and-floatarraymkdata-are-one-loop-at-the-exact-size)).
- **Why:** One representation per type (rule 1 of the layouts of generic
  types): with an array type per element type (`RVec<Nat>`, `LNatArr`,
  index arrays for enumerations, `ElemBox` cells for `[value]` elements),
  an array read at another element type (`Array Nat` out of a generic
  `Prod (Array α) Nat`, the `NonScalar` arrays of `Array.map`) was copied
  element by element, at every use: quadratic in a loop of updates
  (review RV9C-02), and the `map` loops needed a split pass. Natively an
  array element of unknown type is one `lean_object*`.
- **Cost:** none for small scalars: a box is one word (`LAny`), so a small
  `Nat`, a `Bool` or an enumeration is a scalar in the slot, as natively; a
  `Float` element is a cell, as natively. Each `get!` boxes its default
  value.
- **Where:** `LowerBase.lean`: `lowerTypeApp`, `arrayElem?`, `arrayCall`;
  `Lower/ExternCall.lean`: `lowerExternCall`, `customExtern`;
  `Lower/Process.lean`: `arrayMapFn`.
- **Remove only if:** never.

### `ByteArray.mk`/`data` and `FloatArray.mk`/`data` are one loop at the exact size

- **What:** `ByteArray.data` (`lean_byte_array_data`), `ByteArray.mk`,
  `FloatArray.data` and `FloatArray.mk` call a texture of the prelude
  (`l2r_boxes_of_bytes`, `l2r_bytes_of_boxes`, `l2r_boxes_of_floats`,
  `l2r_floats_of_boxes`; `leanrt::array`): it allocates the result at the
  source's size, converts the elements in one loop (a byte to its
  immediate box and back; a float to its cell, `any::of_f64`, and back,
  the box read in place) and releases the source, as natively
  (`lean_alloc_array(n, n)`). A box that the plain unboxing does not read
  (a pointer read as a `UInt8`; a pointer other than a float's or a large
  `UInt64`'s cell read as a `Float`) is `any::mismatch`, a panic, as the
  generated unboxing is in a program without casts. In a program that
  casts, that unboxing reads such a pointer instead (`l2r_unbox_u8`): there
  lean2rr calls the texture only after a check of the elements
  (`l2r_boxes_all_imm`, `l2r_boxes_all_float_words`), and else its
  generated loop, element by element (`arrayMapFn`).
- **Why:** The generated loop pushed each element onto an empty array:
  about 18 instructions a byte and a block that grew by doubling, so a
  `ByteArray.data` of a buffer used up to twice its size. In lean-zip it
  was the largest cost (Adler-32 over `data`, buffers made with
  `ByteArray.mk`). With the textures (cachegrind, silesia `xml`; outputs
  equal native): decompression 865.9 to 775.1 M instructions (-10.5 %),
  compression 2517.7 to 2437.5 M (-3.2 %); peak RSS from 141.4 to 61 to
  69 MB and from 150.7 to 71 to 83 MB (two runs; native 74.7 and 98.4
  MB).
- **Where:** `Lower/ExternCall.lean`: `customExtern`;
  `runtime/prelude.rr`: the `ByteArray` section;
  `runtime/leanrt/src/array.rs`: `boxes_of_bytes`, `bytes_of_boxes`,
  `boxes_all_imm`, `boxes_of_floats`, `floats_of_boxes`,
  `boxes_all_float_words`; `runtime/leanrt/src/any.rs`: `bits_of_word`,
  `is_word_box`. Tests: `RtByteArrayData`, `RtByteArrayDataCast`; leanrt's
  `array::tests::byte_and_float_array_conversions`.
- **Remove only if:** `ByteArray` and `FloatArray` become arrays of boxes.

### An array is one block

- **What:** `RVec<S>` (and `LRef<S>`) is `leanrt::drop::Vec<S>`, a
  `#[repr(transparent)]` pointer to one `mi_malloc` block: a 24-byte header
  (the `u32` reference count Reussir's `rc.inc` bumps, padded; the size;
  the capacity), then the elements inline. `Clone`/`Drop` do the counting;
  `leanrt::array` allocates (a fresh block's size rounded up to 8 bytes,
  the rest capacity), grows a unique block in place (`mi_realloc`, at least
  doubling, to a whole mimalloc block) and copies a shared one
  (copy-on-write).
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

### A block's capacity is mimalloc's size class, without a call up to 64 bytes

- **What:** A grown array or string and every big number take as
  capacity the whole mimalloc block their size falls in
  (`alloc::good_size`; arrays and strings from 4 KiB on a power of two
  instead). Up to 64 bytes `good_size` returns the
  size itself, without calling `mi_good_size`: mimalloc's size classes
  there are every multiple of 8, and the sizes asked for are multiples of
  8, so the answer is the same (unit test `alloc::tests::small_good_size`
  checks every size up to 4 KiB against `mi_good_size`).
- **Why:** The call (with mimalloc's `_mi_bin_size`) was 1.9% of
  liasolver's instructions (218,000 calls, for one-limb big numbers) in an
  instruction-count profile of the classic programs. Without it (switch
  step 10, cachegrind, small sizes): liasolver 2.8% fewer instructions,
  strings 0.26%, qsort 0.15% (an array's growth is under 64 bytes only for
  its first growth, to 8 elements, of elements of 4 bytes or less, such as
  qsort's `UInt32` at the time: 24 + 32 bytes; a string's up to 32
  bytes). Were
  a size class there bigger, a capacity of the size asked for would still
  lie inside the block (room left unused).
- **Where:** `runtime/leanrt/src/alloc.rs`: `good_size`; its callers
  `big.rs` (`block_bytes`), `array.rs` and `string.rs` (`grow`).
- **Remove only if:** mimalloc's small size classes stop being every
  multiple of 8 (the unit test fails then; the capacity stays safe, only
  smaller than the block).

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
  `string::LStr`, `array::release`) and of a thunk or
  task cell (`drop::Cell`) frees when the count is 1 and otherwise
  decrements; never `count > 1`. Its free path is an `extern "C"` function
  (no unwinding, no landing pads in the textures). A cell's read
  (`l2r_lcell_get`, `drop::cell_get`) releases the cell before it copies
  the state; a read of a shared array or string releases it before its
  bounds check (`array::give`, `string::read_owned`), and
  the last reference frees the block after the read (`view_take`,
  `view_end`, after the rule; see
  [../ownership.md](../ownership.md#reads-give-their-reference-up-first-for-a-view)).
- **Why:** Reussir's `rc.inc` asserts that the old count was neither 0 nor
  `u32::MAX`; a read's texture, inlined, releases right after the
  caller's increment, and with `== 1` LLVM sees that the free cannot
  happen and cancels the pair. With
  `> 1` it cannot exclude a wrapped count: an in-place quicksort ran 1.6x
  the instructions (perf-rvec). For a cell, copying the state first
  increments the state record, which LLVM cannot tell from the cell, so
  the cell's count was reloaded and tested; deciding the release first
  (the last reference moves the state out) lets the pair fold: reading a
  finished thunk in a loop runs 0.81x the instructions (perf-cell).
- **Where:** `runtime/leanrt/src/drop.rs`: `Vec::drop`, `free_vec`,
  `Cell::drop`, `free_cell`, `cell_get`; `runtime/leanrt/src/array.rs`:
  `give`; `runtime/prelude.rr`: `l2r_lcell_get`, `l2r_array_give`.
- **Remove only if:** never.

### Shared copies keep their capacity for a push

- **What:** A push onto a shared array copies it with the capacity
  `lean_array_push` gives (its own, unless below `2 * size + 1`); other
  updates of a shared array copy it to its size (rounded up to 8 bytes);
  `Array.mkEmpty` and `ByteArray.emptyWithCapacity` reserve what is asked
  when it can be reserved (next section); growing blocks take whole
  mimalloc blocks.
- **Why:** A literal `#[a, b, c]` pushes onto a shared empty closed term of
  capacity 3: copied with capacity 0, it grew three times (PF4-08,
  a74072b). Capacities were capped at 2^24 elements, so large buffers grew
  by copying (1.73x memory, adv4 K3, b97cdcd). Blocks that fell just past
  a mimalloc size class wasted 35 MB growing a 10M-element `Array Nat`
  (de0352f).
- **Where:** `runtime/leanrt/src/array.rs`.
- **Remove only if:** never.

### A capacity that cannot be reserved reserves nothing

- **What:** `Array.mkEmpty c`, `Array.emptyWithCapacity c`,
  `ByteArray.emptyWithCapacity c` and `FloatArray.emptyWithCapacity c`
  reserve `c` elements when they can, and nothing otherwise, and give the
  empty array either way. A big `Nat` (2^63 or more) is released and gives
  the empty array (the prelude). Above 2^24 elements,
  `leanrt::array::check_capacity` takes lean-runtime's rule
  (`sem::array::empty_with_capacity`: 0 when the object size
  `24 + elem * c` is above 2^64 - 1 or `isize::MAX`), then reserves nothing
  when the native allocation of that size would fail (a `mi_malloc` probe,
  untouched, then freed). Example: `ByteArray.emptyWithCapacity (2^62)`
  passes the rule, the probe fails, and the result is the empty array with
  capacity 0. The probe is freed before the array's own allocation, so a
  failure between the two (unreachable in practice: one thread, the same
  size just reserved) would still end with `out of memory`; a fallible
  allocation of the array itself needs a fallible version of leanrt's
  block allocation (`array::alloc`, which ends with `out of memory` on a
  null `mi_malloc`; an issue, not done).
- **Why:** the Lean definitions give the empty array whatever the
  capacity: it is only a hint. Natively a capacity that cannot be reserved
  ends the process (`INTERNAL PANIC: out of memory`, or `integer overflow
  in runtime computation` for an object size above 2^64 - 1):
  lean-runtime's LB-37, a lifted limit (switch step 13). `Array.replicate`
  keeps native's ends (`check_alloc`): its size is the array's.
- **Where:** `runtime/leanrt/src/array.rs`: `check_capacity`,
  `capacity_slow`, `with_capacity_checked`; `runtime/prelude.rr`:
  `l2r_mk_empty_with_capacity`. Tests `RtAllocBigNat`, `RtAllocOverflow`,
  `RtAllocOom`; lean-runtime's rows `array/mkempty.*`, `bytesempty.*`,
  `floatsempty.*` (`rows-check.sh`).
- **Remove only if:** never.

### `Array.mk`, `Array.toList` and list folds are generated loops

- **What:** `Array.mk` and `String.mk`/`String.ofList` fold their list with
  a generated tail-recursive function (`listFold`); `Array.toList` is a
  generated loop that conses the elements from the last
  (`l2r_array_to_list_<list type>_<array type>`); an array's `Box`es are a
  list's heads as they are. Lists whose elements have no
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
