# The uniform type `Box`

A value whose type is `lcAny` in a relevant position (see
[../types/uniform-types.md](../types/uniform-types.md)) is a `Box`: the
`lcAny` binders of uniform code, and every field, array element, reference
and thunk or task value of a parameter's type (one representation per
type). A typed local never pays for it. `Box` is the prelude's `LAny`
(`leanrt::any`): one word, as Lean's `lean_object*`. Paths are relative to
`lean2rr/LeanToReussir/`. Plan
[§5.1](../../translation-plan.md#51-type-translation), "The uniform type
`Box`".

### The box API: one place knows the encoding

- **What:** Every box made, taken apart, tested for `box(0)` or looked
  into goes through the box API of `LowerBase.lean`: `boxKind` (how a type
  is boxed), `boxNum` (a payload number), `boxPayload` (the registration of
  a payload type), `boxPayloads`, `boxInit`, `boxValue`, `boxZero` (and
  `boxZeroAllocates`, false), `boxUnbox` (the unboxing at a type),
  `boxDispatch` (a match on the payload number, `BoxArm`), `boxSink`,
  `boxAddr`, `boxFnOfIndex`, `boxAllocates` (whether boxing a type can
  allocate); and `boxTypeItems` (`Lower/Finish.lean`,
  the program's release of its payloads). The callers: boxing and
  unboxing in `tryCoerce` (boxing through `boxOf`: a placeholder is
  `box(0)`, a constant boxed once, [placeholders.md](placeholders.md),
  [../optional-passes.md](../optional-passes.md)) and `unboxMatch`
  (`Lower/Conv.lean`), the box
  placeholder (`zeroTry`), the unboxing functions (`genUnbox`), the walk of
  a constant for tasks (`genPersist`, `holdsTask`), identity (`addrOf`) and
  the program's box item (`lowerProgram`). Outside it, `Lower/Live`
  recognizes the payloads live code builds by the number a box
  construction passes, and the runtime's generic `l2r_sink`,
  `l2r_ptr_addr_rec` and `l2r_persist_seen` take a box as one counted
  handle (`l2r_ptr_addr_rec` answers `LAny::addr` for a box).
- **Why:** The encoding changed from a shared enum (a heap cell per box,
  rule 1's step 4) to one word in one section; the rest of lowering did
  not change.
- **Where:** `LowerBase.lean`: "The box API"; `Lower/Finish.lean`:
  `genUnbox`, `boxTypeItems`.
- **Remove only if:** never.

### How each type is boxed

- **What:** `boxKind` gives a type's form in a box:
  - the unit: `box(0)`, the word 1 (`l2r_any_unit`), no allocation;
  - `u8`, `u16`, `u32` (`Char`), `bool`, `f32`: the immediate of the word
    (`l2r_any_of_<k>`, `l2r_any_as_<k>`); an enumeration (a `[value]` enum
    without fields): the immediate of its index;
  - `u64`, `f64` (and `i64` as its `u64` bits): an immediate below 2^63,
    else a cell (`l2r_any_of_u64`; a `Float` is always a cell, as
    natively); `i8`, `i16`, `i32`: their bits zero-extended, always an
    immediate. No Lean value has a signed type: Lean's `toMonoType` erases
    `Int8`…`Int64` and `ISize` to `UInt8`…`USize` (`hasTrivialStructure?`),
    so they are `u8`…`u64` and boxed as those. The signed words keep the
    box API total; no caller boxes one today;
  - a `[value]` struct: its one field, boxed at the field's type; a field
    that is a `Box` (`ST.Out σ α`) is the box itself (below);
  - `Nat`, `Int`, `String`, `Array α`, `ByteArray`, `FloatArray`:
    leanrt's kinds 1, 2, 3, 6, 7, 8 (`l2r_any_of<T>`; a small `Nat`/`Int`
    is its own word); a compact array (`compact-arrays`,
    [compact-arrays.md](compact-arrays.md)) by its storage: `RVec<u8>` 7
    (as `ByteArray`), `RVec<f64>` 8 (as `FloatArray`), `RVec<u16>` 9,
    `RVec<u32>` 10, `RVec<u64>` 11, `RVec<f32>` 12;
  - every other type (a shared record or enum, a function value, a
    reference, a thunk or task cell, a handle, another array): a pointer
    with the program's payload number (`boxNum`, from 16; from `0x8000 +
    16` for a leaf type, `boxIsLeaf`: a record or enum whose fields are
    all scalars), wrapped in an `ElemBox` when it cannot cross the FFI
    boundary. A shared enum's nullary variant is the immediate of its
    index (Reussir represents it as an immediate; `leanrt::any` turns it
    into the index). A function value boxes with `l2r_any_of_fn`, whose
    nullary variants keep their type: `(num << 32) | index`. A type
    without nullary variants (a record, an enum whose constructors all
    have fields, an `ElemBox`, a reference, a cell, a handle) boxes with
    `l2r_any_of_ptr`: its handle is always a pointer, so the box is the
    word with the number (`leanrt::any::of_ptr`'s check of the address
    only), without `l2r_any_of`'s tests for a nullary variant's immediate
    (the top byte under `tbi`, the dummy's count under `immortal`).
- **Why:** One word per generic field and array element, as natively; a
  cell only for `Float`, large `UInt64` and values that need one. An
  immediate is untyped, as natively: a word read at another word type
  through `unsafeCast` reads the same word. A function type has several
  representations (`Nat → Nat`, `Box → Box`), so a nullary variant's index
  is only meaningful with its type.
  The tests for a nullary variant cost a top-byte test and a load and
  compare of the count at every box of a record (review perf-r1 item 6;
  cachegrind, without mimalloc's free path: sieve -4.1 %, unionfind
  -3.7 %, monadic-interp -2.4 %, typeclass-generic -2.3 %, liasolver and
  mergesort -1.0 %).
- **Where:** `LowerBase.lean`: `BoxKind`, `boxKind`, `boxNum`, `boxIsLeaf`,
  `boxValue` (`l2r_any_of_ptr`); `runtime/prelude.rr`: `l2r_any_of_ptr`;
  `Lower/Live.lean`: `exprRefs` (a box construction's payload).
- **Remove only if:** never.

### A `[value]` struct over a box is the box itself

- **What:** A `[value]` struct whose one field is a `Box` (`ST.Out σ α`:
  `val : α`, a parameter's type, and an erased `Void σ`, lowered as
  `struct [value] T_ST_Out(LAny)`) is boxed as that field, the box itself
  (`boxValue`), and unboxed as the struct around the box (`boxUnbox`). It
  has no payload of its own (`boxPayload` registers none), and its boxing
  never allocates (`boxAllocates`). The boxing of such a struct built at
  once folds to the field (`boxUnboxed?`). `boxKind` of `Box` itself is an
  internal error: a box is never boxed again.
- **Why:** The struct was boxed by boxing its field at the field's type,
  and `boxKind` of `Box` fell through to a program payload with a number
  of its own: an `ST.Out` put into a list, an array, a thunk or a
  reference panicked at its first unboxing (`ifNum` against that number,
  "unreachable code"; with `l2r_any_of_ptr`, at its first boxing: the box's
  word is not a 48-bit address). Natively
  the struct is its field, the same object (review of deptypes-lowperf,
  finding 1; test `RtValueStructBox`).
- **Where:** `LowerBase.lean`: `BoxKind.valueStruct`, `boxKind`,
  `boxPayload`, `boxAllocates`, `boxValue`, `boxUnbox`, `boxUnboxed?`.
- **Remove only if:** never (a box cannot be a payload).

### Unboxing follows the split rule

- **What:** `boxUnbox` at a type `t`: a scalar, an enumeration or one of
  leanrt's kinds is decoded by the runtime (`box(0)` is its zero); a
  program type splits the word: an immediate is a nullary variant by
  index, the 0 arm (`box(0)`) the type's zero (or variant 0 when it is
  nullary), any other immediate a cast or unreachable; a pointer is checked
  against `t`'s number and taken (`l2r_any_raw_take`), any other number a
  cast or unreachable. A `[value]` struct is its field's unboxing (over a
  `Box`, the struct around the box itself; over a function value, the
  struct around the generated unboxing of the function type,
  `l2r_unbox_fn_T`, which `boxUnbox` gets as `fnUnbox`). The
  prelude's comment above `l2r_any_as` shows the rule.
- **Why:** `box(0)` reaches typed positions (an erased argument at a type
  with data, rule 4e), and only the program can make a record's zero or a
  nullary variant. A function value has several representations and typed
  immediates (`l2r_any_of_fn`), which only the generated function reads: a
  recursive structure whose one field is a function
  (`inductive G | mk : (Nat → Option (Nat × G)) → G`, a `[value]` struct)
  stopped lean2rr at its first unboxing, "boxUnbox at function type
  (internal error)" (hunt box, test `RtValueStructFnBox`).
- **Where:** `LowerBase.lean`: `boxUnbox`; `Lower/Conv.lean`:
  `unboxMatch` (passes `unboxFnFn`), `tryCoerce`; `Lower/Finish.lean`:
  `genUnbox` (its immediates through `unboxMatch`).
- **Remove only if:** `box(0)` stops reaching typed positions.

### A field of a parameter's type holds a `Box`; a boxed value is matched at its type

- **What:** An inductive has one type, whose fields of a parameter's type
  are `Box`es (`nominalType`; `uniformType` gives that type). A `cases` on
  a value held in a `Box` first unboxes it to that type.
- **Why:** Values boxed from every use of the inductive have the one
  type (and, in a program that can cast, the unboxing also reads the
  types a cast reads), so one match covers them.
- **Where:** `LowerBase.lean`: `nominalType`, `uniformType`;
  `Lower/Code.lean`: `lowerCases`.
- **Remove only if:** never.

### A value that only goes back into boxes keeps its box

- **What:** Before a declaration is lowered, `boxedOnlyVars` finds the
  variables whose every use is a boxed position: a field of a parameter's
  type in a constructor, a `Box` parameter of a callee, an extern's
  argument at a `Box` parameter or at a type variable it stores in a
  `Box` (`Array.push`'s element), a `Box` result, a `Box` join-point
  parameter (`CodeCtx.boxedOnly`). A `cases` field among them is bound as
  the field's box (`bindField`: no unboxing `let`), and a `let` among them
  whose value is a box to start with (a projection of a box field, a call
  whose callee returns a `Box`, an extern's result at a type variable it
  stores in a `Box`: `letValueBoxed`) is bound as a `Box`. Separately,
  `tryCoerce` folds a box unboxed and boxed again at once into the box
  itself (`boxUnboxed?` recognizes each form of `boxUnbox`'s result). Any
  other use (a projection, a `cases`, an extern's argument at its own
  type, a closure's argument, a capture by a local function) keeps the
  old binding: the field is unboxed once and boxed again where it goes
  back into a box.
- **Why:** `List.reverseAux` at a concrete `α` unboxed each head and boxed
  it again into the new cell, at every instance (mergesort -11.8 %,
  typeclass-generic -10.2 %, monadic-interp -3.0 %, unionfind -3.4 %
  instructions; review perf-r1 item 5); a `Float` or a `UInt64` from 2^63
  got a new cell each time (`a ++ b` on `Array Float`: one cell per
  appended element, from 1000 to 4000 elements +6002 allocations against
  native's +3001, now +3002; `RtArrayAppendFloat`). Natively the head is the same object all
  along, so passing the box on is closer to native: `box(0)` stays
  `box(0)` (every unboxing at the type reads its zero, as it read the
  boxed zero before), a nullary variant stays its immediate, and a word
  read at another type through `unsafeCast` is passed on unchanged where
  the unboxing truncated it (`RtBoxPassOnCast`: a `List Nat` read as
  `List UInt8` and copied read back 255 for 511). The `reverseAux`
  instances are now identical up to names. A variable with another use as
  well is not given the box for its boxed uses: the unboxed value would
  then be dead where only the box goes on, and Reussir's token reuse
  takes such a release as a new cell's donor (issue 39, `RtProbeBump`).
  So a word read at another type and also used at that type is still
  truncated where it is boxed again (`RtCastMixedRebox`, expected to
  fail). A `let` whose value is not a box (a constructor) stays at its
  type: boxing it at the `let` instead of at its use saves nothing, and
  it moved a hot loop's code in nqueens.
- **Where:** `Lower/BoxedUses.lean`: `boxedOnlyVars`, `boxedUsesCode`,
  `boxedUsesValue`, `boxedArgMask` (which arguments of a declaration or an
  extern are boxed positions, cached by callee in
  `LowerState.boxedArgMasks`), `letValueBoxed`; `Lower/Hooks.lean`: `bindField`;
  `Lower/Code.lean`: `lowerCode` (`let`s), `lowerDecl`; `Lower/Values.lean`:
  `lowerConstApp` (its value at the binder's type `rty`),
  `lowerLetValue`; `LowerBase.lean`: `boxUnboxed?`; `Lower/Conv.lean`:
  `tryCoerce`; `Lower/ExternCall.lean`: `bindReadIndex` (`atVar`). Tests
  `RtBoxPassOn`, `RtBoxPassOnCast`, `RtCastMixedRebox` (xfail),
  `RtProbeBump` and `RtArrayAppendFloat` (alloc-check).
- **Remove only if:** never (the round trips come back).

### An array element read at once at an immediate type, `Nat` or `Int` takes no copy of its box

- **What:** An unboxing at a type a box holds only as an immediate
  (`UInt8/16/32`, `Char`, `Bool`, an enumeration) or at `Nat` or `Int`,
  whose box is an array read at `Box` (`lean_array_fget`, `get!`'s
  `lean_array_get`, `uget`, their `_borrowed` forms, maybe in
  `bindReadIndex`'s block), calls the read's `_as<T>` variant instead
  (`boxWordRead?`): `l2r_view_take_as<T>` looks at the element in place and
  tests bit 0 once; an immediate is read without a copy of the box (no
  reference count step), a big `Nat` or `Int` is copied as before. At an
  immediate type the result is the box's word, which `l2r_any_word_as_<k>`
  (or `l2r_any_word_imm` for an enumeration) reads, any pointer being a
  mismatch, as for `l2r_any_as_<k>`; `get!`'s default out of bounds is
  taken at `T` (`l2r_any_take_as`). Only without `slow` (a program that
  casts reads other payloads through the generated function, which needs
  the box). `boxUnboxed?` folds the boxing of such a read back into the
  read of the box.
- **Why:** The read copied the element (`LAny::clone`: a test of bit 0,
  an increment for a pointer) and the unboxing tested bit 0 again (review
  perf-r1 item 7). The same read of a field (a match binder or a
  projection unboxed at once) still copies the field's box: Reussir
  copies a field a use takes, and no texture can borrow it (Reussir has no
  borrowed reads across its FFI boundary).
- **Where:** `LowerBase.lean`: `boxWordReads`, `boxWordRead?`,
  `boxWordReadBack?`, `boxUnbox` (`.scalar`, `.enumIdx`, `.leanrt` 1 and 2),
  `boxUnboxed?`; `runtime/prelude.rr`: `l2r_view_take_as`,
  `l2r_any_take_as`, `l2r_array_get_as`, `l2r_array_get_word_as`,
  `lean_array_fget_as` and the other `_as` reads, `l2r_any_word_imm`,
  `l2r_any_word_as_<k>`; `tests/runtime/ffi-inline-check.sh` lists the
  `_as` reads among those that must stay inlined at cold call sites. At
  `RtReadsDeep`'s cold sites LLVM keeps 3 `l2r_view_take_as` calls (the
  reads at `Nat` and `Int`; a big number's copy is out of line, `big`),
  as it keeps 4 `l2r_view_take` calls there: on deptypes 5234d3b with the
  anybox Reussir it kept 7 `l2r_view_take` calls, so the check failed
  before. Test `RtArrayReadImm`.
- **Remove only if:** never (each read copies the box again).

### Unboxing functions are generated last, until the payloads are stable

- **What:** Unboxing to a function type, or to a nominal or word type in a
  program that casts, is a generated function (`l2r_unbox_T`,
  `l2r_unbox_fn_T`; a nominal or word type unboxes its own payload in
  line, `boxUnbox`), whose body (`genUnbox`, `boxDispatch`) matches the
  payload numbers that can hold a value of the target's Lean type (with
  `conv-liveness`, those live code boxes): at a function type every
  compatible representation, converted (and the typed immediates of their
  nullary variants, `l2r_fn_of_index_S`); in a program that casts, the
  payloads of types a cast reads. Generating a conversion can add payload
  types, so the bodies are regenerated until the set stops growing.
- **Why:** A function type has several Reussir representations, and in a
  program that casts a box can hold a value of another type.
- **Where:** `LowerBase.lean`: `unboxFn`, `boxDispatch`;
  `Lower/FnValues.lean`: `unboxFnFn`; `Lower/Finish.lean`: `genUnbox`,
  `finishUnboxFns`, `boxTypeItems` (`l2r_fn_of_index_S`).
- **Remove only if:** never.

### Function values keep their identity in a `Box`

- **What:** A function value is boxed as itself, at its own type; it is
  not converted when boxed.
- **Why:** A function value that goes through uniform code and back is
  then the same object (no wrapper chain).
- **Where:** `Lower/Conv.lean`: `coerce`.
- **Remove only if:** never.

### The program releases its own payloads, one function per type

- **What:** For each program payload type `T` with number `n`, lean2rr
  emits `fn l2r_any_rel_<n>(x : T) -> unit { }` (Reussir drops `x` at its
  type) and the trampoline `l2r_any_rel_<n>_c`, whose C signature is
  `void (cell)`, the type of a release on Reussir's pending stack. A
  texture, `l2r_any_releases`, holds a static table of
  `leanrt::any::Rel(n, l2r_any_rel_<n>_c)` and installs it in leanrt
  (`leanrt::any::install`). The trampoline `l2r_any_init_c` calls it;
  leanrt calls that once at the start of `rt::run_main2`, before the
  initializers and before any other thread (`any::init_releases`; a weak
  symbol, absent in a program without program payloads).
- **Why:** Only the program knows its types' drop glue. A function per
  type, found by number in a table, replaces one release with a `match` on
  the number (`l2r_any_drop`, called through `l2r_any_drop_c` and leanrt's
  `release_program`): that function saved six register pairs and went
  through a jump table on every call, about 26 instructions of its own,
  and the trampoline of each type now takes the cell itself, so it is
  deferred as is. With the changes of `release_last` (cachegrind, small
  sizes, two runs, without mimalloc's free path, whose generic branch
  varies from run to run; outputs equal native): monadic-interp 1008.1 to
  917.3 M instructions (-9.0 %), unionfind -3.3 %, liasolver -1.1 %,
  typeclass-generic -0.9 %.
- **Where:** `Lower/Finish.lean`: `boxTypeItems`; `Emit/Program.lean`:
  `lowerProgram` (after `liveDrop`, with every payload type known);
  `runtime/leanrt/src/any.rs`: `Rel`, `RELEASES`, `install`,
  `init_releases`; `runtime/leanrt/src/rt.rs`: `run_main2`; the probe's
  own table (`tests/runtime/any-probe/probe.rr`, `probe_install`).
- **Remove only if:** never.

## The runtime side: `leanrt::any`

### A box is one word: an immediate or a numbered pointer

- **What:** `LAny` (`leanrt::any`, the prelude section "The one-word box")
  is a `tagged` opaque type. An odd word is an immediate `(v << 1) | 1`:
  scalars, unit (word 1, Lean's `box(0)`), a small `Nat` or `Int` (its own
  word). An even word owns a reference to a counted object: the low 48
  bits are the address, the top 16 bits the number of the payload's type.
  Numbers 1 to 15 are leanrt's kinds: 1 a big `Nat`, 2 a big `Int`, 3
  `LStr`, 4 and 5 the `f64` and large-`u64` cells, 6 `RVec<LAny>`, and 7 to
  12 the arrays of scalars (below); 13 to 15 are free. 16 and up are the
  program's (`0x4010` up with `WIDE_BIT` for a type whose cell has a wide
  header, `0x8010` up with `LEAF_BIT` for a leaf type: below). A `Float` and a `UInt64`/`USize` from 2^63 go into a cell
  (`Rc`), as natively. The arrays of scalars:
  - 7 `NUM_BYTES`, `RVec<u8>`: `ByteArray`; a compact `Array` of `UInt8`,
    `Bool` or an enumeration of at most 256 constructors;
  - 8 `NUM_FLOATS`, `RVec<f64>`: `FloatArray`; a compact `Array Float`;
  - 9 `NUM_U16S`, `RVec<u16>`: a compact `Array UInt16`;
  - 10 `NUM_U32S`, `RVec<u32>`: a compact `Array UInt32` or `Array Char`;
  - 11 `NUM_U64S`, `RVec<u64>`: a compact `Array UInt64` or `Array USize`;
  - 12 `NUM_F32S`, `RVec<f32>`: a compact `Array Float32`.
- **Why:** One word per generic field and array element, as Lean's
  `lean_object*`. A copy is the payload's count increment, in line; the
  number lets the drop hook release the payload as its own type and lets
  an unbox check the type (a mismatch panics, it never reads wrongly).
- **Where:** `runtime/leanrt/src/any.rs`; `runtime/prelude.rr`, section
  "The one-word box"; Reussir patch 38-a (issue 38: `rc.inc` clears the top
  16 bits of a tagged handle; `reussir-bugs/38-tagged-top-bits.md`).
  Places in lean2rr that the switch to `LAny` touches, because they treat
  `Box` as one record pointer today: `Lower/Identity.lean`, `addrOf` (the
  `Box` case calls `l2r_ptr_addr_rec`, used by `ptrAddrUnsafe` and
  `ptrEq`; the texture answers `LAny::addr` for a box, `l2r_any_addr` is
  the direct form); `Lower/Finish.lean`, `boxSink` (releases a box out of
  line through `l2r_ptr_addr_rec`); `LowerBase.lean`, `isBoundaryTy` (a box
  crosses the FFI boundary as one handle) and `refType`'s boxed path; the
  prelude's shared checks (`lean_dbg_trace_if_shared`, `l2r_shared_check`:
  they answer for a box's payload); leanrt's array copy and release loops
  (an `RVec<LAny>` has its own: `CloneInto for LAny`, `ReleaseElems for
  LAny`, ownership.md); the capacity checks that pass the element size 8.
- **Remove only if:** `Box` goes back to a generated enum (the fallback is
  a two-word `[value]` enum).

### A boxed `Float` or large `UInt64` is a small cell, read in line

- **What:** `any::of_f64` and `any::of_u64` (from 2^63) put the value in
  a cell from `alloc::rc_new`, which takes `mi_malloc_small` for a box of
  at most 128 words (a constant size, so the choice is made at compile
  time). `any::as_u64` and `any::as_f64` read a cell in line
  (`take_cell_bits`: the type number checked, the 8 bytes at offset 8
  read, then the cell freed with `mi_free` when that was its last
  reference, else decremented); the two cells have one layout, so each
  reads the other's bits, as `unsafeCast` does natively. `release_kind`
  frees a scalar cell with `mi_free` too.
- **Why:** The read was a call into a generic `Rc` read and drop (about 21
  instructions and Rust's deallocator), and `mi_malloc` tests the size
  that `mi_malloc_small` takes as small. Mergesort reads 145 000 `UInt64`
  cells (values from 2^63) and typeclass-generic boxes floats: -1.6 % and
  -1.8 % instructions, higher-order -1.0 % (cachegrind, small sizes).
- **Where:** `runtime/leanrt/src/alloc.rs`: `rc_new`, `free`, `rc_data`;
  `runtime/leanrt/src/any.rs`: `of_f64`, `of_u64_cell`, `as_u64`,
  `as_f64`, `take_cell_bits`, `release_kind`. Test: leanrt's
  `any::tests::scalar_cells_read_shared_and_last`.
- **Remove only if:** `Float` and large `UInt64` stop going into cells.

### A nullary variant is boxed as the immediate of its index

- **What:** `leanrt::any::of` turns a Reussir nullary-variant immediate
  (top byte `tag + 1` under the `tbi` encoding; a dummy count of at least
  2^31 under the `immortal` one) into the box immediate of its variant
  index. Unboxing an immediate at an enum type is the program's code: it
  splits on the low bit (`l2r_any_raw_is_imm`) and builds the variant from
  the index (index 0 also serves `box(0)`).
- **Why:** The top bits of a box hold the type number, and only Reussir can
  make a nullary variant's handle (the dummy box's address). As natively:
  Lean boxes a nullary constructor as `lean_box(i)`.
- **Where:** `runtime/leanrt/src/any.rs`: `Payload for Bridge<X>`.
- **Remove only if:** Reussir stops encoding nullary variants as
  immediates.

### `box(0)` unboxes to the zero of every type

- **What:** Lean's `box(0)` is the box word 1 (the immediate 0). Read at
  one of leanrt's kinds it is that kind's zero (`0`, `0.0`, `""`, `#[]`,
  the `Nat`/`Int` 0), in `leanrt::any`. A generated unbox at a program
  type splits the word first (`l2r_any_raw`, `l2r_any_raw_is_imm`): an
  immediate `i` is the nullary variant of index `i`, or, for index 0 when
  variant 0 is not nullary, the zero of the type (lean2rr's `l2r_zero_N`);
  any other immediate is `l2r_unreachable`; a pointer goes to
  `l2r_any_raw_as<T>`. The prelude's comment above `l2r_any_as` shows the
  shape.
- **Why:** As the `b0` arm of the old enum `L2RBox` did: an erased argument passed
  where data is expected (rule 4e) is `box(0)`, and code may read it at any
  type. Only the program can make a record's zero or a nullary variant.
- **Where:** `runtime/leanrt/src/any.rs`: `leanrt_kind!`, `Payload for
  Vec<LAny>`, `f64_of_word`; `runtime/prelude.rr`, the comment above
  `l2r_any_as`; the probe's unbox functions
  (`tests/runtime/any-probe/probe.rr`).
- **Remove only if:** `box(0)` stops reaching typed positions.

### An array of scalars unboxed as an array of boxes is converted (the safety net of compact arrays)

- **What:** `Payload for Vec<LAny>` (the unbox at `RVec<LAny>`, number 6:
  `l2r_any_as`, `l2r_any_raw_as`) accepts a box of an array of scalars
  (numbers 7 to 12) too. `any::boxes_of_compact` (out of line, `#[cold]`)
  makes a new array of the same size whose elements are the scalars boxed
  as lean2rr boxes them (`array::boxes_of_scalars`, trait `BoxScalar`):
  `u8`, `u16` and `u32` as immediates, an `f32` as the immediate of its
  bits, a `u64` as `of_u64` (an immediate below 2^63, a cell from there),
  an `f64` as `of_f64` (a cell). Then it gives up the box's reference (a
  shared source is decremented, a unique one freed). For example, the box
  of an `RVec<u16>` `[1, 2]` unboxed at `RVec<LAny>` gives `[imm 1, imm 2]`;
  the box of an `RVec<u64>` `[5, 2^63]` gives `[imm 5, cell 2^63]`. With
  the environment variable `L2R_DEBUG_ARRAY_CONVERT` set (read once), each
  conversion writes `leanrt: compact array of kind N converted to boxes (L
  elements)` on descriptor 2. The reverse (a box of number 6 unboxed at an
  array of scalars) stays a mismatch.
- **Why:** lean2rr's whole-program check (C0) keeps a compact array away
  from every place that reads it as `Array lcAny`, so the conversion does
  not happen. If the check misses a flow, the program gives the same
  results as with boxes, at the cost of a copy, instead of the mismatch's
  panic. The line lets tests check that no conversion happens. The reverse
  needs the element type, which a box of number 6 does not give.
- **Where:** `runtime/leanrt/src/any.rs`: `Payload for Vec<LAny>`,
  `boxes_of_compact`, `report_conversion`; `runtime/leanrt/src/array.rs`:
  `BoxScalar`, `boxes_of_scalars`. A generated unbox in a program that
  casts tests the number before it calls `l2r_any_as` (`boxUnbox` with a
  cast function): there a box of 7 to 12 goes to the cast function, not
  here. Tests: leanrt's `any::tests::compact_arrays_convert_at_an_array_of_boxes`,
  `any::tests::conversion_line_and_reverse_mismatch`,
  `array::tests::scalar_arrays_as_boxes`.
- **Remove only if:** compact arrays are removed, or the static check is
  proved to cover every flow.

### The last reference of a program payload goes to the program, through the worklist (a leaf directly)

- **What:** `LAny`'s drop decrements the payload's count in line. At count
  1 it calls `any::release_last(w)` (out of line, `#[cold]`), which tests
  for a program number first (16 and up). A program payload's
  release is `RELEASES[num]` (the program's `l2r_any_rel_<num>_c`, see
  above); its cell, the word without the number, is deferred as one
  pending cell with `__reussir_drop_defer(cell, release)` and drained with
  `__reussir_drop_drain()` (`drop::free_deferred`; switch step 11's rule
  for records, `drop::free_unique`). Inside a free that only pushes the
  cell; outside one Reussir's `drain_one` runs the release inside a new
  drain and then what it pushed. A number with `WIDE_BIT` (`0x4000`, next
  entry) is deferred with `__reussir_drop_defer_wide` instead
  (`drop::free_deferred_wide`). A leaf payload (a number with `LEAF_BIT`,
  `0x8000`: lean2rr's `boxIsLeaf`, a record or enum whose fields are all
  scalars) is released by a direct call of its release, also inside a
  free. leanrt's own kinds go to `release_kind`. A number without a release
  installs the table if that was not done yet, else it is Lean's internal
  panic (`release_unregistered`). The array free calls a payload's release
  directly where the stack would pop the deferred cell next
  (`release_last_in_step` in its step; an array that keeps one element,
  outside a free: ownership.md, "The array free calls a payload's release
  where the stack would pop it next").
- **Why:** Only the program knows its types' release (Reussir's drop glue).
  Through the worklist, a chain of nested boxes is freed in a loop, not by
  recursion (the probe frees chains of 10^6 boxes on a 1 MiB stack, and
  `RtBoxDeepChain` 10^6 nested boxes on a 1 MiB stack), and in native
  Lean's order: inside a free, a record's observable members (a file
  handle, a promise) are pushed and released last field first, as
  `lean_dec`/`lean_del` frees a box's payload. A direct call of the
  program's release outside a free runs the payload's glue in field order
  instead (a box of `H2(A, B)`: `AB`, natively `BA`; a chain of boxes
  `C(1, C(2, C(3)))`: `132`, natively `321`), and runs promise dependents
  in the middle of it; the probe checks the native orders (any-probe,
  `s_order`). A leaf holds nothing to order, frees only its own cell and
  pushes nothing (Reussir frees a leaf record member at once in its glue
  too, never deferred), so its direct release changes no order that a
  program can see, inside a free or outside one. Deferred inside a free it
  took one entry of Reussir's stack (24 bytes) per leaf while others
  waited: Reussir's glue frees a list along its tail before the drain pops
  anything, so a `List P` of structures of scalars dropped whole held one
  entry per element (hunt HMEM-01: n = 4M, 382 MB against native's 258
  MB; consumed cell by cell, 195 MB). A deferral that is not `_wide`
  neither reads nor writes the cell. `release_last` stays `#[cold]`: the
  drops in a loop then keep their decrement in line and the call out of
  the way (without it, sieve +0.5 % instructions from the loop's layout,
  monadic-interp -0.1 %).
- **Where:** `runtime/leanrt/src/any.rs`: `release_last` (`LEAF_BIT`,
  `WIDE_BIT`), `release_kind`, `release_unregistered`;
  `runtime/leanrt/src/drop.rs`: `free_deferred`, `free_deferred_wide`;
  `LowerBase.lean`: `boxIsLeaf`, `boxNum`. Tests:
  leanrt's `any::tests` (`deep_chain_frees_without_recursion`,
  `deep_chain_of_two_numbers`, `fields_in_lean_order`,
  `a_leaf_payload_is_released_directly`, `one_kept_element_without_a_step`),
  any-probe, `RtBoxDeepChain`, `RtBoxPackFreeOrder`, `RtDepDropOrderBoxed`,
  `RtListDropWhole` (alloc-check: peak memory), the order tests of
  ownership.md.
- **Remove only if:** Reussir gives opaque types a drop glue of their own
  that defers.

### A payload whose cell has a wide header is deferred `_wide`: consecutive cells take no memory

- **What:** lean2rr numbers a non-leaf payload type whose Reussir cell has
  a wide header with `WIDE_BIT` (`boxWideBit`, `0x4000`: numbers `0x4010`
  to `0x7fff`; the others `16` to `0x3fff`, the leaves `0x8010` up;
  `boxNum`, `boxIsWide`). A wide header is Reussir's rule for
  `__reussir_drop_defer_wide` (`hasWideHeader` in Reussir's
  `lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp`):
  the cell's first 8 bytes are the 32-bit count and then a 32-bit word that
  is a fused tag below 2^16 or padding. That holds for
  - a shared enum (`enum`, shape `.enum`) of at most 2^16 constructors:
    Reussir fuses its tag into the header's second word
    (`RecordType::hasFusedHeader`: a variant whose capability is not
    `value`);
  - a shared struct (`struct`, shape `.struct`, not `[value]`; the
    reference record `L2RRef`; an `ElemBox`) whose alignment is 8: its
    members start at offset 8, after 4 bytes of padding (the box is
    `{i32 count, record}`). Its alignment is 8 when a member is 8-aligned
    (`rrAlign8`): a `u64`, `i64` or `f64`; a member Reussir stores as a
    pointer (a shared record or enum, a function value, a Reussir `Cell`
    or closure, an opaque runtime type such as `Nat`, `LStr`, `LAny`,
    `RVec`: `memberStorageType` in Reussir's `lib/IR/ReussirTypes.cpp`); a
    `[value]` struct or tuple that holds one;
  - a function value: the shared enum `L2RFn_…` of its run-time type
    (`fnTypeItems`), a fused enum as above. Its variants are known only
    at the end of the translation, after its number is given, so
    `fnTypeItems` stops with an internal error if the enum of a function
    type numbered with `WIDE_BIT` has more than 2^16 constructors
    (`boxWideMaxCtors`): the mark is never wrong.
  Not marked: runtime types (`RVec`, `LCell`, `LHandle`: leanrt's or
  Reussir's blocks, not Reussir records), a struct whose members are all
  4-aligned or less (a leaf anyway). A thunk's or task's cell (`LCell`)
  can never be wide: it keeps its task index in the header's second word.
  An array as a list's head stays one step entry each (not done: needs a
  step-linking mechanism). `release_last` defers
  a marked payload's cell with `__reussir_drop_defer_wide`
  (`drop::free_deferred_wide`). When the top entry of Reussir's stack is a
  run, the cell links to the run's last cell through its header (the
  count and the upper 16 bits of the second word: the offset and the
  release's index), so the run grows by one cell and the stack by nothing.
  The drain sets both back (count 1, upper bits 0, the tag kept) before it
  calls the release, which then sees the cell as it was deferred.
  Example: a `List (Nat × Nat)` dropped whole. Reussir's glue for
  `T_List(LAny, T_List)` releases each head (the box of a `T_Prod(LAny,
  LAny)`, a wide struct) and frees the cell, then goes on along the tail;
  each head's cell links to the one before, and the drain pops them last
  first after the walk.
- **Why:** Before, every head took one 24-byte entry of the stack's
  vector, which grew by doubling during the walk (hunt HMEM-01: n = 4M,
  391 MB against native's 258 MB; consumed cell by cell, 195 MB). Native
  Lean's to-do list links the freed objects themselves and takes no
  memory. The order of releases is the same: a link only stores the run's
  next cell in the cell. Outside a free the stack is empty at almost every
  deferral, so no link forms; the wide deferral costs about 3 instructions
  more there (monadic-interp +0.6 % instructions when every payload was
  deferred `_wide` before the mark). After the change, at n = 4M: 195 MB
  for the pairs and for structures of scalars (the leaf rule above), as
  when the list is consumed cell by cell; `RtListDropWhole` at n = 10^6
  (five head types): peak 46040 to 76756 KB against native's 55216 to
  102332 KB (before: 99304 to 132072 KB), and the bytes requested equal
  native's (before: 1.7 to 2.3 times, the stack's vector). Function
  values got the mark later (HRT2-02): a `List (Nat → Nat)` dropped whole
  peaks at 45596 KB at n = 10^6 and 162396 KB at n = 4M, against native's
  69496 and 258016 KB (before: 89196 and 275496 KB), and lean2rr requests
  30 MB where native requests 42 MB (before: 68 MB).
- **Where:** `LowerBase.lean`: `boxWideBit`, `boxWideMaxCtors`,
  `rrAlign8`, `boxIsWide`, `boxNum`; `Lower/Finish.lean`: `fnTypeItems`
  (the check of a boxed function type's enum);
  `runtime/leanrt/src/any.rs`: `WIDE_BIT`, `release_last`;
  `runtime/leanrt/src/drop.rs`: `free_deferred_wide`; Reussir's
  `reussir_rt::drop` (`__reussir_drop_defer_wide`, `State::link`,
  `unlink`). Tests: leanrt's `any::tests::wide_cells_link_into_one_run`
  (the depth a release sees stays 1 for wide cells, grows by one per
  narrow cell), `fields_in_lean_order` and `deep_chain_of_two_numbers`
  with a wide number; `RtListDropWhole` (alloc-check: peak memory of a
  list of pairs, of options, of lists and of function values dropped
  whole within native's plus 4 MB). An array as a list's head is not a program payload with a
  release (`NUM_ARRAY`, `RVec` of records): its free stays a step, one
  entry each.
- **Remove only if:** Reussir's pending stack changes what a wide
  deferral writes into the cell, or its layout rule (`hasWideHeader`)
  changes; then `boxIsWide` must follow, or answer false.
