# Local additions to Reussir (not bugs)

Two of the local patches fix no Reussir bug: they add something lean2rr's
runtime or representation needs. They are kept with the bug fixes
([`README.md`](README.md#applying-the-patches)), applied in `./reussir`
(`l2r-local` cc8e5aa5), and reviewed like them.

| Patch | What | Needed by | Review |
|---|---|---|---|
| [0040](#0040-a-hook-at-the-end-of-a-drain-__reussir_drop_drained) | `reussir_rt::drop` calls a host function when a drain ends | lean2rr's runtime (promise dependents released inside a free) | rv8/reussir: no defect |
| [0050](#0050-tagged-opaque-handles-one-word-nat-and-int) | `#[ffi(rust = "...", tagged)]`: an odd handle is an immediate, not counted | one-word `Nat`/`Int` (lean2rr's prelude) | rv8/nat and the mem-nat review: no defect |

## 0040: a hook at the end of a drain (`__reussir_drop_drained`)

Patch file
[`patches/0040-l2r-local-drop-call-the-host-s-function-when-a-drain.patch`](patches/0040-l2r-local-drop-call-the-host-s-function-when-a-drain.patch)
(`l2r-local` commit `e3e267af`, applied in `./reussir`; made as commit
`3aad05ae` in a scratch checkout on 91da4f80). Not a Reussir bug: a hook
that lean2rr's runtime needs.

### Why

Natively, dropping the last reference to an unresolved promise resolves it
with `none` and runs its `sync` dependents at once, on the dropping thread,
also in the middle of freeing a container that holds the promise. lean2rr's
runtime runs every context of its scheduler on one thread, and the pending
stack of `reussir_rt::drop` (patches 0014, 0015) is the thread's: a
dependent may block (a lock, a sleep), and a context suspended inside a
drain would let the other contexts push their frees onto that drain. So a
promise resolved inside a drain has its dependents walked once the drain is
over (`leanrt::task::resolve`, `run_later_walks`).

The runtime sees the end of a drain that it starts itself (`leanrt::drop::run`,
for arrays, reference cells and task cells, and for the old value of a
reference's `set`, `leanrt::drop::release`), but not of one that the record
glue starts (`drop_in_place`'s `__reussir_drop_drain`, when the program's
own code releases a structure, a list, an `Option`). Without this patch
those dependents run only at the context's next output, block, Std.Sync
wait or question about a task: code in between sees the old state, output
they print escapes `IO.FS.withIsolatedStreams`, and a condition-variable
loop that reads its condition before waiting can wait forever (plan §10).

### The change

`crates/reussir-rt/src/drop.rs` exports
`pub static __reussir_drop_drained: AtomicPtr<()>` (`#[no_mangle]`, null
by default), the address of an `unsafe extern "C" fn()`. The general drain
loop (`State::drain`) and the one-cell path (`drain_one`) call it after
setting `draining` back to false, when nothing is pending. A drain with
nothing pending, or started inside a drain, returns before and calls
nothing. The cost is one relaxed load per drain that released something.
The function may release values (a new drain, which calls it again) and
switch coroutines.

lean2rr's runtime declares the symbol `#[linkage = "extern_weak"]` and
stores `leanrt::task::drained` there whenever a promise is resolved inside
a drain. Against a Reussir without the patch the weak symbol is null
and nothing is stored: the runtime still builds and works as before.

### Checks

- `cargo test -p reussir-rt --lib drop::` passes: the new test
  `drained_runs_after_the_outermost_drain` (the function runs once per
  outermost drain, after it, through both paths, and not for a drain with
  nothing to do or one started inside a drain) and the existing order
  tests.
- lean2rr against the patched build (`L2R_REUSSIR`): `RtPromiseFreeSync`,
  `RtPromiseFreeGlue`, `RtSyncLostWake` and the task, promise, sync, IO and
  net runtime tests pass. (`RtPromiseFreeGlue` was an expected failure
  without the patch until reference sets released their old value through
  the runtime, round 8; its cases are all references now covered without
  it. A free that the program's own code starts at a record has no test:
  where Lean drops a local is not fixed.)

### Review

Round RV8 (local review notes): no defect.
The hook is called at every drain exit that released something, after
`draining` is false and with nothing pending, as the last statement, so it
may start new drains, re-enter or switch coroutines; not for nested drains
or drains with nothing to do. A panic inside a drain aborts (the steps are
reached only through `extern "C"` frames), so no drain exits by unwinding.
A relaxed `AtomicPtr` is enough (it publishes a code pointer). Weak linking
works both ways: a binary built with 0040 defines the symbol and
`RtPromiseFreeGlue` passes; one built against a Reussir without it shows a
weak undefined symbol and runs. The drop unit tests pass, the new one also
under Miri. Side note (not introduced by 0040): drop glue is marked
`mustprogress nounwind willreturn`, and with the hook (and already before,
through `leanrt::drop::run`) it can run Lean continuations that might not
return; no concrete miscompile was found.

## 0050: tagged opaque handles (one-word `Nat` and `Int`)

Patch file
[`patches/0050-l2r-local-tagged-FFI-objects-an-odd-handle-is-an-imm.patch`](patches/0050-l2r-local-tagged-FFI-objects-an-odd-handle-is-an-imm.patch)
(`l2r-local` commit `a75ed2cf`, applied in `./reussir`; made as commit
`b4ea1ae1` in a scratch checkout on top of 0017). Not a bug fix: a small
feature lean2rr needs to represent `Nat` and `Int` as one word (made on
branch `mem-nat`).

### What it does

An opaque Reussir record (`#[ffi(rust = "path")] pub struct T;`) is a
handle to a foreign, reference-counted box. Reussir copies such a handle by
incrementing the 32-bit count at offset 0 of the box, in line, and releases
it by calling a generated drop hook (the Rust type's `Drop`). The patch
adds an opt-in flag, `#[ffi(rust = "path", tagged)]`: a handle of such a
type may also be an odd word that is not a pointer at all, and Reussir then
increments the count, or calls the hook, only when the handle's low bit is
clear.

lean2rr declares `Nat` and `Int` this way. A small `Nat` `n` (below 2^63) is
the word `2n+1`, a small `Int` (the `int32` range) `lean_box` of its 32
bits; a big one is a pointer to a counted big number (lean2rr's own
layout, one block with the limbs inline). The words are Lean's own
representation, and Lean's C runtime
makes the same low-bit test before every count update (`lean_inc`,
`lean_dec`). Before, `Nat` was a two-word `[value]` enum
`{ Small(u64), Big(LBig) }`: 16 bytes in every record field (natively 8).
lean2rr cannot skip the counting of small values itself: Reussir inserts it
(in records, closures, enums, its drop and acquire glue). Without the flag,
Reussir would increment "the count" of a small `Nat` at address `2n+1`, a
crash. A clone hook would be the same mechanism with a call per copy, and
lean2rr cannot change the drop glue Reussir generates (plan §5.1, "One-word
`Nat` and `Int`", weighs the options).

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
  false (existing IR is unchanged).
- Lowering (`lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp`, the only
  place where `rc.inc` and `rc.dec` of an `ffi_object` become code):
  `beginRealBoxGuard` splits the block on `(ptrtoint p) & 1 == 0`; the
  increment and the call to the cleanup hook go in the guarded block, and
  nothing is loaded from the handle before the test.
- The two other places that read the count of an arbitrary rc value skip
  tagged objects: the optional `--instrument-nonlinear-ffi` check and the
  uniqueness-carrying analysis (`rc.assume_unique` on a carried argument;
  it cannot fire for an FFI object, which Reussir never creates fresh, but
  is excluded anyway). Nothing else reads through an opaque handle: an
  `ffi_object` produces no reuse token, is not deferred by the drop glue,
  and reaches foreign code only as its Rust type, which knows the encoding
  (`leanrt::nat::LNat`'s `Drop` and `Clone` make the same test). Real boxes
  are at least 4-aligned (the count is a `u32` at offset 0), so the low bit
  of a real handle is always clear, and an immediate (odd) is never null.

### Checks and review

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

Reviews: the mem-nat review (local review notes)
and round RV8 (local review notes, Q3) found no
defect in the patch: the guard covers the delta, atomic and
immortal-steering paths of `rc.inc`; `rc.dec` calls the hook only for an
even word (and the hook re-tests it); every other reader or writer of a
count was traced to a guarded path or excludes FFI objects; Reussir puts no
alignment or dereferenceable attributes on FFI handles, so LLVM cannot fold
the low-bit test away. The first review's optional hardening (exclude
tagged objects from `rc.assume_unique`) is in the final patch.

**Effect on lean2rr.** `Nat` and `Int` fields take 8 bytes instead of 16,
small values are never allocated, copying or dropping one is a bit test;
`Array Nat` without the `nat-arrays` pass is `RVec<Nat>` (one word per
element), and an `IO.Ref Nat` is a cell holding the handle. lean2rr's
prelude needs the patch (rrc rejects the `tagged` attribute without it).

**Upstream note.** The feature is general: any foreign type with a
pointer-or-immediate encoding (Lean objects, OCaml values, small-string
optimizations) can use it. A fuller version could let the foreign side
choose the tag bit, or lower the guard to a `select` where branches are
costly.
