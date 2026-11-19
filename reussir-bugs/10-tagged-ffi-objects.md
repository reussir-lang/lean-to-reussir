# 10. An opaque FFI handle cannot be an immediate

**Kind:** missing feature. Not a bug: Reussir does not promise handles
that may be a number instead of a pointer. lean2rr's box `LAny` needs
them (and its one-word `Nat` and `Int` did, until clean-integration D8 on
2026-10-26); patch 10-a adds them (*tagged* opaque handles).

## Summary

**Kind:** missing feature (lean2rr's prelude needs it). **Status:**
patched (10-a), the first patch of the series on upstream `36a55a0f`
(Reussir branch `l2r-base13-r7`, tree `6dc99546`; 43 files,
+742/-50, without `tests/` +283/-50).
lean2rr's prelude declares the box `LAny` `tagged` (until D8 also `Nat`
and `Int`); rrc rejects the attribute without the patch.

**Upstream (2026-11-17):** Not upstream at `36a55a0f`: an opaque FFI
handle must still be a pointer to a counted box. Reussir's maintainer
tried the feature upstream himself (Reussir #923, "port Lean integration
handle and bigint support") and closed that pull request unmerged on
2026-11-05; his port of lean2rr (pull request #4) keeps the patch here.
Upstream's new opaque pointers (`Ptr<A>`) carry no ownership and do not
replace counted tagged handles. On `36a55a0f` upstream has three new
places that read the count of an rc value, so 10-a grew
([below](#the-readers-of-a-count-on-36a55a0f)), and its refinement of
2026-11-18 made the rule a rule of the dialect
([below](#the-refinement-of-2026-11-18)).

**Upstream, earlier bases (history, 2026-10-24):** Not upstream at 0378b744: an opaque FFI handle must still be a pointer to a counted box. Upstream 0378b744 has built-in `Nat` and `Int` (#776 `af25863e`, with #770 to #803): rcgmp integers, where a small value is an immediate and a large one a counted heap object. They are another way to a one-word `Nat` and `Int`; since D8 (2026-10-26) lean2rr's `Nat` and `Int` are these built-in integers, and its prelude still needs 10-a for the box `LAny`. 10-a stays in the series on 0378b744, ea240b19 and 00906e38 (2026-10-25; it applies unchanged), and on `l2r-base12` (Phase 2: the first patch of the series, on upstream `95d9a1c8`, commit `f4cd7729`; only line offsets change; its rebase onto 7954a367 had two conflicts: upstream added the `placement` and `launch` fields to records).

Until 2026-10-06 this patch had no entry: it was one of the two "local
additions" (file `local-additions.md`, now entries
9, retired on 2026-10-25, and 41).

## What is missing

An opaque Reussir record (`#[ffi(rust = "path")] pub struct T;`) is a
handle to a foreign, reference-counted box. Reussir copies such a handle by
incrementing the 32-bit count at offset 0 of the box, in line, and releases
it by calling a generated drop hook (the Rust type's `Drop`). Every handle
must be a pointer to such a box.

Until D8, lean2rr represented `Nat` and `Int` as one word, as Lean does
(today the box `LAny` is such a word: an odd word an immediate, an even
word a pointer to a counted cell). A small `Nat`
`n` (below 2^63) was the word `2n+1`, a small `Int` (the `int32` range)
`lean_box` of its 32 bits; a big one is a pointer to a counted big number
(lean2rr's own layout, one block with the limbs inline). The words are
Lean's own representation, and Lean's C runtime makes the same low-bit test
before every count update (`lean_inc`, `lean_dec`). Before the patch, `Nat`
was a two-word `[value]` enum `{ Small(u64), Big(LBig) }`: 16 bytes in
every record field (natively 8), and `Std.TreeMap Nat Nat` used about 1.5x
native memory. lean2rr cannot skip the counting of small values itself:
Reussir inserts it (in records, closures, enums, its drop and acquire
glue). Without the feature, Reussir would increment "the count" of a small
`Nat` at address `2n+1`, a crash. A clone hook would be the same mechanism
with a call per copy, and lean2rr cannot change the drop glue Reussir
generates (plan §5.1, "History: one-word `Nat` and `Int`", weighs the
options).

**Repro.** None in [`repros/`](repros/): without the patch rrc rejects the
attribute, and with it the Reussir tests below show the guarded count (see
[Checks and review](#checks-and-review)).

## Patch

Patch file
[`patches/10-a-tagged-ffi-objects.patch`](patches/10-a-tagged-ffi-objects.patch)
(on `36a55a0f`: commit `f85fa22c`, subject `[ffi] support tagged foreign
handles`; before, `l2r-local` commit `a75ed2cf`; made as commit
`b4ea1ae1` in a scratch checkout on top of old 23-a (upstream #683), for the work of branch
`mem-nat`).

The patch adds an opt-in flag, `#[ffi(rust = "path", tagged)]`: a handle of
such a type may also be an odd word that is not a pointer at all, and
Reussir then increments the count, or calls the hook, only when the
handle's low bit is clear.

### Where in Reussir

- Frontend: the attribute is parsed in `crates/reussir-core/src/semi/ctxt.rs`
  (`Record::ffi_tagged`) and travels through the textual HIR
  (`{ ffi tagged "path" }`; the shared IR lexer's `tagged` keyword is also
  accepted as a name), the package interface, monomorphization into
  the MIR layout (`RecordLayout::Opaque { tagged }`, printed
  `{ "path", @hook, tagged }`) and codegen
  (`crates/reussir-codegen/src/lower/ty.rs`, through the C API
  `reussirFFIObjectTypeGet(..., tagged)`).
- Dialect: `FFIObjectType` gets a default-valued `bool` parameter, printed
  `!reussir.ffi_object<"path", @hook, tagged = true>` and omitted when
  false (existing IR is unchanged). Since 2026-10-25 the type also has a
  builder with the two old parameters (`FFIObjectType::get(ctx, name,
  hook)` in `include/Reussir/IR/ReussirTypes.td`), which gives an untagged
  object: C++ code written for the type before `tagged` compiles
  unchanged. Upstream's C++ unit test `record_drop.cpp` builds the type
  that way; without the builder, Reussir's C++ unit tests (`reussir-ut`)
  do not compile. With it, all 82 pass on `l2r-base9` (on the bases with
  patch 02-b, that patch also updated upstream's `glue_symbols.cpp`).
- Lowering (`lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp`, the only
  place where `rc.inc` and `rc.dec` of an `ffi_object` become code):
  `beginRealBoxGuard` splits the block on `(ptrtoint p) & 1 == 0`; the
  increment and the call to the cleanup hook go in the guarded block, and
  nothing is loaded from the handle before the test.
- The two other places that read the count of an arbitrary rc value skip
  tagged objects: the optional `--instrument-nonlinear-ffi` check and the
  uniqueness-carrying analysis (`rc.assume_unique` on a carried argument;
  it cannot fire for an FFI object, which Reussir never creates fresh, but
  is excluded anyway). On the bases up to `l2r-base12` nothing else read
  through an opaque handle; on `36a55a0f` there are more readers, which
  the next section lists. An
  `ffi_object` produces no reuse token
  and reaches foreign code only as its Rust type, which knows the encoding
  (`leanrt::any::LAny`'s `Drop` and `Clone` make the same test, as did
`leanrt::nat::LNat`'s until D8). Real boxes
  are at least 4-aligned (the count is a `u32` at offset 0), so the low bit
  of a real handle is always clear, and an immediate (odd) is never null.

### The readers of a count on 36a55a0f

The rule of 10-a: only the lowering of `rc.inc` and `rc.dec` may touch
the count of a tagged handle, because only that code tests the low bit
first. Upstream's drop series of 2026-11-01 and #983 added code that
reads the count of an arbitrary rc value. The patch on `36a55a0f` keeps
tagged handles away from each such place. All of them are in the one
patch 10-a (a fix of our own patch's rule is part of that patch); in
the maintainer's port to `44abd17c` the first one was the separate
patch 24-c.

**1. `emitWorklistDecrement`** (`lib/Conversion/AcquireDropExpansion/WorklistDrop.cpp`;
from the maintainer's port). Inside worklist drop glue, every shared rc
member goes through this function, which reads the count to see whether
the member is dead. For a tagged FFI object it now emits a plain
`reussir.rc.dec` marked as not deferred, and returns: the lowering of
`rc.dec` tests the low bit and calls the cleanup hook. Without it, an
immediate, or a handle with data in its top 16 bits, is read as the
address of a count. Tests: `conversion/worklist_tagged_ffi.mlir` (a
tagged object released directly, through a ref and through a nullable
ref: no `rc.fetch`), `frontend/ffi_tagged_worklist.rr` (a `[value]`
record and an enum that hold tagged words; it runs).

**2. The array task's `deadTest`** (the same file; new on 2026-11-17).
A Reussir array whose element is an rc of an FFI object goes to the
array task of the worklist drops (an FFI element cannot finish in
line). Under **forward** drop order, each element got a count test in
line: `rc.fetch` and `rc.set` (for an atomic count, `rc.fetch_sub`).

- *Repro:* MLIR with one array of `tagged = true` handles, lowered with
  `drop-order=forward`: both ops appear on the tagged handle (the
  patch's test has the same input).
- *Fix:* `deadTest` answers "dead" for a tagged handle, so each element
  goes to its release function, whose `rc.dec` tests the low bit. That
  release function does not retain an atomic tagged object first (the
  retain was there to undo the `fetch_sub`, which no longer happens).
- *Cost:* one deferred release for each element, immediates included,
  under forward order only.
- *lean2rr:* not reached. lean2rr builds with backward order, where the
  array task emits a plain `rc.dec`, which was right already. The fix
  keeps the patch's rule true under both orders.
- *Test:* `conversion/worklist_tagged_ffi_array.mlir` (plain and atomic
  nullable array elements under forward order: no count access, no
  retain).

**3. `core::object::is_unique`** (#983; new on 2026-11-17). This
intrinsic lowers to `reussir.rc.is_unique`, whose lowering loads the
count through the handle.

- *Repro:* `fn direct(w: Word) -> bool { core::object::is_unique(w) }`
  with a tagged `Word`: `rrc --emit mlir` gave `reussir.rc.is_unique` on
  the handle.
- *Fix:* the checker and monomorphization reject the intrinsic on a
  tagged object, with a diagnostic (`tagged_handle_rejection` in
  `crates/reussir-core/src/semi/ty_eval.rs`). `unsafe_inc` and
  `unsafe_dec` stay allowed: they become `rc.inc` and `rc.dec`, which
  test the handle.
- *lean2rr:* not reached (lean2rr does not emit the intrinsic).
- *Test:* `frontend/ffi_tagged_is_unique.rr` (the direct use and a
  generic's instance rejected; an untagged handle and the manual retain
  and release accepted).

Other places, read on 2026-11-17 and left as they are:

| Place | Why a tagged handle does not reach it |
|---|---|
| `deadTest` from `releasePure` (record members) | a record that holds an FFI object has observable cleanup, and `releasePure` needs none |
| the shortcut for a decrement that is not the last (#924), `RcDecrementExpansion.cpp`, the outlining of #968 | each excludes every `FFIObjectType` |
| `TailDrop.cpp`, `emitHeapRelease` | for an rc of a record with a tail-loop drop, not for the FFI member |
| `BorrowSpecialization.cpp`, `rc.is_unique` in a traversal entry | the parameter must be a value that the callee takes apart, which an opaque FFI object cannot be. Read only; no repro proves it |
| the top-byte reading of nullary tags (#980 to #982) | another type family (the nullary tags of records); it does not touch `ffi_object` handles |

One thing upstream does that matters if lean2rr's prelude changes: for
an **untagged** FFI object, upstream's worklist code reads and writes
the count in line. That is right only for a foreign type with a plain
`u32` count at offset 0 whose release, when it is not the last, is only
a decrement. lean2rr's untagged opaque types (`LStr`, `drop::Vec`,
`drop::Cell`, an `Rc` of a boxed value) were not checked against this
rule one by one. The port's first gate (2026-11-18) gives the practical
answer: no crash and no wrong result in 747 runtime tests, and its six
failures, all release order, have other causes
([issue 2](02-native-drop-order.md#on-upstream-36a55a0f)).

### The refinement of 2026-11-18

An independent review of 10-a and 07-a on `36a55a0f` found no hole in
the rule, and asked for these changes, which are in the patch:

- **One predicate, and a verifier rule.** `RcType::isTaggedFFIObject()`
  (declared next to `mayCarrySpecialPointerTag`) replaces four spellings
  of the same test. The verifier rejects `rc.fetch`, `rc.fetch_sub`,
  `rc.set`, `rc.is_unique`, `rc.assume_unique` and `rc.defer` on a
  tagged object, with `cannot access the count of a tagged FFI object`.
  Before, the rule was kept by convention at each site: the next
  upstream pass that reads the count of an arbitrary rc value would
  have compiled, and the program would have read an immediate as an
  address. Now such a pass fails the verifier. Test
  `basic/failure/tagged_ffi_count_ops.mlir`.
- **The contract of the foreign type.** The low-bit test works only if
  LLVM knows nothing about the handle's alignment. So the foreign type
  of a `tagged` record must be a pointer-sized scalar that promises
  neither alignment nor dereferenceability: an integer or a raw
  pointer, not a reference, a `Box`, or an `Option` of one. This is the
  declaration's contract, stated in the type's description and at the
  attribute. The texture of the drop hook checks what it can: the type
  has the size and the alignment of `usize` (`u8` is refused; test
  `frontend/ffi_tagged_word.rr`). A first form of the check (a niche
  test) was withdrawn after its own review: it refused types that work
  and let through types that break. lean2rr's `LAny` is a raw pointer
  and passes.
- **An end-to-end test of arrays.** `frontend/ffi_tagged_array.rr`:
  arrays of immediates in a record and in a recursive enum, run under
  both drop orders.
- **Atomic paths kept.** An atomic tagged object cannot come from the
  frontend but is valid MLIR, as an atomic untagged one is; its paths
  stay, with tests.
- Not done: one field for `Record::ffi` and `Record::ffi_tagged` (it
  would change every upstream reader of the field). Parked: a marker
  trait in Reussir's runtime that would state the contract of the
  foreign type in Rust.

### Measured claim

No wall time was measured for this patch. What was measured:

- **Code without tagged types does not change.** LLVM IR of pristine
  `36a55a0f` against the patched compiler, 7 programs at `-O none` and
  `-O aggressive` (16 compilations: an untagged FFI object, enums with
  nullary variants, arrays of rc elements, closures, upstream's
  `ffi_vec_e2e` and `ffi_member_drop`): 0 differing lines.
- **A tagged handle costs** a test and a branch on a retain and on a
  release, and one AND on the retain of a box (07-a); an immediate is
  not allocated and not counted.
- **The refinement changes no instruction of lean2rr's programs:** LLVM
  IR of 8 lean2rr programs, the patch before and after the refinement:
  identical.
- On upstream's benchmark suite, core and std (33 units, lowered MLIR):
  25 units are byte-identical under the whole series, and the other 8
  (core, std and the six integer programs) are byte-identical after
  10-a, 07-a and 20-a.

### Checks and review

On `36a55a0f` (2026-11-18, aarch64, the final series): the ten lit
tests of the patch pass (`basic/failure/tagged_ffi_count_ops`;
`conversion/tagged_ffi_object`, `instrument_nonlinear_ffi_tagged`,
`worklist_tagged_ffi`, `worklist_tagged_ffi_array`; `frontend/ffi_tagged`,
`ffi_tagged_worklist`, `ffi_tagged_array`, `ffi_tagged_is_unique`,
`ffi_tagged_word`), `reussir-ut` passes 97 of 97, and the patch was
built and tested alone (121 lit tests of tagged handles, object
intrinsics and worklists). Reviews: one of the patch as folded and one
of the refinement (local notes `port13/reviews/RV1`, `RV6`): no hole in
the rule; the findings of both are in the patch (above). Through lean2rr: `tests/runtime/any-probe.sh` passes
its 19 scenarios under both encodings of nullary variants, and the
port's final gate passed on the patch as it is in the series (748 of
750 runtime tests identical to native, 2 expected failures). The
port's first gate ran on the patch before its refinement (739 of 747
runtime tests identical to native; the six failures are release order,
[issue 2](02-native-drop-order.md#on-upstream-36a55a0f)). The text
below records the checks on the earlier bases.

Tests: `conversion/tagged_ffi_object.mlir` (guarded `rc.inc`/`rc.dec` for a
tagged object, unguarded for an untagged one, the textual form),
`conversion/instrument_nonlinear_ffi_tagged.mlir`, `frontend/ffi_tagged.rr`
(the attribute through HIR, MIR and MLIR), HIR and MIR round-trip unit
tests; all `reussir-core` unit tests (467) and the existing FFI tests
(`instrument_nonlinear_ffi.mlir`, `ffi_vec.rr`, `rc_delta.mlir`) pass
unchanged. On lean2rr: the runtime suite, the classic corpus, the Reussir
benchmark suite, the round-7 big-number repros, and tests of every
`Nat`/`Int` operation at 2^62, 2^63 and 2^64 and of `Nat`s in every
container, including counted big-number allocations and frees
(`tests/runtime/nat-alloc-check.sh`: `RtNatStress`, also through
`IO.Ref` set/swap/modify, and `RtNatConst`).

Reviews: the mem-nat review (local review notes,
`mem/nat/review/FINDINGS.txt`) and round RV8 (local review notes,
`rv8/nat/FINDINGS.txt`, Q3) found no defect in the patch: the guard covers
the delta, atomic and immortal-steering paths of `rc.inc`; `rc.dec` calls
the hook only for an even word (and the hook re-tests it); every other
reader or writer of a count was traced to a guarded path or excludes FFI
objects; Reussir puts no alignment or dereferenceable attributes on FFI
handles, so LLVM cannot fold the low-bit test away. The first review's
optional hardening (exclude tagged objects from `rc.assume_unique`) is in
the final patch.

**Effect on lean2rr.** Until D8, `Nat` and `Int` fields took 8 bytes
instead of 16, small values were never allocated, copying or dropping
one was a bit test; the box `LAny` keeps these properties for its
immediates.
(When arrays and references had a representation per element type, an
`Array Nat` without the `nat-arrays` pass was `RVec<Nat>`, one word per
element, and an `IO.Ref Nat` a cell holding the handle; since rule 1 they
hold boxes, `LAny`, which hold a small `Nat` as its own word.) lean2rr's
prelude needs the patch (rrc rejects the `tagged` attribute without it).

**Extension.** Patch 07-a ([issue 7](07-tagged-top-bits.md)) lets the
top 16 bits of a tagged pointer handle carry foreign data: `rc.inc` clears
them before it touches the count (lean2rr's one-word `Box` keeps its
payload's type number there). `Nat` and `Int` pointers had them clear
(until D8).

## Upstream note

The feature is general: any foreign type with a pointer-or-immediate
encoding (Lean objects, OCaml values, small-string optimizations) can use
it. A fuller version could let the foreign side choose the tag bit, or
lower the guard to a `select` where branches are costly.
