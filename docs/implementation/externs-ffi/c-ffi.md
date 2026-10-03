# Calling the program's C code (in progress)

**Status:** in progress on branch `ffi-c` (latest commit 1133472, not
merged into `dev`; nothing here is in b299aab). A Lean program may
implement some of its `@[extern "sym"]` declarations in C (written against
`<lean/lean.h>`, built by Lake). The goal is that lean2rr links that C code
and calls it, so the program behaves as its native build does, its C
included. On the branch the design is plan §5.15. When the work is merged,
replace "in progress" with the code locations at that commit and move the
entries that change `dev`'s behaviour into the other files.

### Extern precedence with C code

- **What (planned):** An extern call gets, in this order: lean2rr's own
  implementation (a prelude function, a runtime primitive, glue, the shim,
  or an `@[export]` Lean definition of the symbol); else the C code linked
  with the program, when it defines the symbol; else the extern's Lean
  body, compiled, when it has one; else an error. **On the branch now:**
  the first two steps; a program extern with no implementation at all is a
  lean2rr build-time error (the Lean-body fallback is not there yet).
- **Why:** lean2rr's implementations follow Lean's runtime on lean2rr's own
  representations, so they win; the program's C comes next because the
  native build calls it; a Lean body is the reference semantics when
  neither exists.
- **Where:** in progress: `Lower/CFFI.lean` (`isCExtern`, `cExternCall`),
  `Lower/ExternCall.lean`, `scripts/l2r.py` (`--link-c`,
  `--lake-project`, `--link-arg`; it passes the libraries' symbols to
  lean2rr as `--external-symbols`). The order at b299aab:
  [dispatch.md](dispatch.md#the-order-at-b299aab).
- **Remove only if:** n/a.

### Tier 1: values C sees as they are (zero copy)

- **What (in progress):** The runtime gives some objects exactly Lean's
  layout, so the glue passes the pointer. On the branch: `String` (`LStr`
  is Lean's string object: tag 249, NUL-terminated, `m_size` counting the
  NUL), `ByteArray` and `FloatArray` (`LSArr`, Lean's scalar array object,
  replacing `RVec<u8>`/`RVec<f64>`), and `Array Nat`/`Array Int` blocks
  with Lean's header and tag (7a784e1 made them single blocks; also on
  branch `mem-layout`). Planned: `Array Nat`/`Int` and `Nat` passed without
  conversion (the branch still converts `Nat`).
- **Why:** No copy per call for the data C code typically reads (byte
  buffers); Reussir's count is the `u32` at offset 0, where Lean's `m_rc`
  is, and both allocate with mimalloc. The single blocks also save memory
  (Pf4SmallArrs 431 → 336 MB, native 338).
- **Where:** in progress: `runtime/leanrt/src/string.rs`, `sarray.rs`,
  `tagvec.rs`, `runtime/prelude.rr`.
- **Remove only if:** n/a.

### Tier 2: values converted at the boundary

- **What (in progress, implemented on the branch):** Other values are
  converted to Lean objects for the call and read back: `Nat`/`Int` (a
  small value as `lean_box`, a big one as a GMP object), structures and
  inductives laid out by Lean's `getCtorLayout` (`Option`, `Except`,
  `Prod`, `List`, the program's own types), arrays of other elements, IO
  results. The call goes through a generated texture with the extern's
  impure signature (`getImpureSignature?`), numbers unboxed, and arguments
  Lean borrows released after the call. `leanrt::cffi` exports `lean.h`'s
  runtime functions under their C names, with Lean's semantics.
- **Why:** lean2rr's typed representations differ from Lean's uniform
  objects; converting at the boundary keeps typed code fast. A copy is
  O(size) per call.
- **Where:** in progress: `Lower/CFFI.lean` (`toObj`/`ofObj`),
  `runtime/leanrt/src/cffi.rs`.
- **Remove only if:** n/a.

### Tier 3: bridges for what cannot be copied

- **What (in progress):** Bridges for opaque foreign objects (Lean's
  external objects with their class's finalizer: `lean_external_class`
  exists on the branch), for closures in both directions, and for handles.
  On the branch, `Thunk`, `Task`, `IO.FS.Handle` and references crossing to
  C are still "not supported yet" (a build-time error).
- **Why:** Such values have identity or behaviour that a copy would lose.
- **Where:** in progress: `runtime/leanrt/src/cffi.rs`
  (`lean_register_external_class`), `Lower/CFFI.lean`.
- **Remove only if:** n/a.
