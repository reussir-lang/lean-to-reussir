# 45. A polymorphic-FFI type substitution given as an MLIR rc type becomes Rust's `Rc` without drop glue

## Summary

**Kind:** bug (hand-written MLIR only), as [bug 33](33-rc-trailing-text.md).
**Status:** not patched; it does not affect lean2rr (unreachable: only
MLIR written by hand reaches this code).

**Verdict: bug.** A polymorphic FFI function (a *texture*) is Rust
text with placeholders `[:T:]`, which rrc replaces by the Rust spelling of
each instance's types before it compiles the text. The MLIR pass
`CompilePolymorphicFFI` can be given a substitution as an MLIR type
attribute. For a shared `!reussir.rc<…>` it then writes
`type T = ::reussir_rt::rc::Rc<TPointee>`, where `TPointee` is a byte
array of the record's size marked `Copy`. Rust code in the texture that
drops or copies such a value uses `reussir_rt::rc::Rc`'s own `Drop` and
`Clone`, not the record's glue:

- the last release frees the box with `Box::from_raw` and releases none of
  the record's members (they leak);
- a nullary variant (an immediate) is not recognized: its count, the
  dummy box's, is read and changed, and could be freed;
- an atomic rc type gets the non-atomic `Rc` (plain loads and stores of
  the count).

Reussir's front end never writes such a substitution, so no program in the
`.rr` language reaches it. Found by a review of Reussir's runtime crate
(finding HRT-03).

## Symptom and repro

No repro in [`repros/`](repros/). No `.rr` program can show it: the front
end never writes the operation (see [Cause](#cause)). Unlike bug 33,
whose repro is one line that the parser misreads, a repro here would be a
whole module written by hand: a record type with a counted member, a
`reussir.polyffi` operation holding the texture's `[:T:]` text and a type
attribute `!reussir.rc<…>` in its `substitutions`, the import's
declaration, and a caller. And what it would show is silent: the
record's members are never released (a leak), or an immediate's count
changes; both need the program's allocations counted to be seen. As
nothing in lean2rr or in Reussir's front end reaches the path and it gets
no patch, no such module was written.

## Cause

`lib/Conversion/CompilePolymorphicFFI/CompilePolymorphicFFI.cpp`:
`monomorphize` replaces each placeholder by its substitution: a string
attribute is copied as it is; a type attribute goes to `formatInto`. Its
`RcType` case writes `::reussir_rt::rc::Rc<…Pointee>` for the shared
capability (`RigidRc` for rigid), and the `RecordType` case, below the top
level (`isTopLevel` false), writes the record as
`#[derive(Copy, Clone)] struct …([u8; N])` without the `Drop` and `Clone`
that call the record's glue (`drop_in_place`, `acquire_in_place`), which
it writes only for a record at the top level. `reussir_rt::rc::Rc`
(`crates/reussir-rt/src/rc.rs`) decrements a `Cell<u32>` count and, at 1,
frees the box with `Box::from_raw`, dropping only `TPointee` (nothing).

The `.rr` front end substitutes the placeholders itself, as text
(`substitute_placeholders`, `crates/reussir-core/src/full/ffi.rs`): a
shared record becomes `::reussir_rt::bridge::Bridge<…>` over a generated
one-pointer type whose `Drop` and `Clone` call the record's
`…_ffi_release` and `…_ffi_acquire` glue. Those handle immediates, and
atomic counts, as compiled code does. The operation it builds holds only
the substituted text (`polyffi_texture`,
`crates/reussir-backend/src/builders.rs`: a `moduleTexture` and no
`substitutions`), so `formatInto` never runs for it.

## lean2rr

Not affected, and not reachable: lean2rr writes `.rr` source, which the
front end compiles, so every texture of lean2rr's prelude gets the
front end's `Bridge` spelling (leanrt's specializations for records,
`drop::ReleaseValue` and `array::CloneInto`, are written for `Bridge`).
lean2rr never writes MLIR.

## Why it stays unpatched

No patch (the owner's rule since 2026-10-07: Reussir is changed only where
lean2rr has no other way; lean2rr does not reach this code).

## Upstream note

`formatInto` (`CompilePolymorphicFFI.cpp`) renders a shared rc type
attribute as `::reussir_rt::rc::Rc<Pointee>` with a `Copy` byte-array
pointee: Rust code that drops or clones it leaks the record's members,
treats an immediate as a box, and updates an atomic count non-atomically.
Rendering it as the front end does (a pointer type whose `Drop` and
`Clone` call the record's release and acquire glue) would fix all three.
