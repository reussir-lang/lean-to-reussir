# Reussir limitations that shape lean2rr's output

Not bugs: a cost of documented Reussir behaviour (issue 3), missed
optimizations (issues 7 and 36), a missing feature (issue 13), or properties of its
FFI and LLVM pipeline, that lean2rr works with. In each case rrc's output
is correct; a local patch for one of these issues is an optimization or a
feature, not a fix. Plan
[§9](../../translation-plan.md#9-open-items) has the probe results and the
candidate Reussir requests. Paths: `lean2rr/LeanToReussir/` for lean2rr's
files, `runtime/` and `scripts/` from the repository root.

### Only some types cross Reussir's FFI boundary

- **What:** Runtime functions receive and return only integers, floats,
  `bool`, opaque runtime types and shared records. lean2rr therefore: puts
  `Box`es in arrays, references and thunk and task cells (one
  representation each); wraps other values in a one-field `ElemBox` for
  once-cells and the type-parameter arguments of externs that do not store
  them in arrays;
  represents unit-like values as `L2RUnit`; gives runtime helpers over
  Lean-defined types the constructors as arguments; and instantiates
  plain-Reussir generic prelude functions (`dbgTrace`, `panic`, …) at the
  value types themselves, since they never cross the boundary.
- **Why:** `[value]` records, closures and `unit` parameters do not cross
  it (probe results). Reussir's `unit` is result-only.
- **Where:** `LowerBase.lean`: `isBoundaryTy`, `cellStorage`;
  `Emit/Program.lean`: `valueGenericPreludeFns`;
  `Lower/ExternCall.lean`: `lowerExternCall`; see
  [../representations/arrays.md](../representations/arrays.md),
  [../representations/records.md](../representations/records.md#unit-like-values-are-the-value-enum-l2runit),
  [../externs-ffi/glue.md](../externs-ffi/glue.md).
- **Remove only if:** Reussir passes `[value]` types across the FFI (a
  feature request).

### An escaping stack slot blocks tail calls, so textures must inline

- **What:** lean2rr passes no Reussir `str` to the runtime (string literals
  come from a table, big literals are parsed from table strings), and the
  runtime is written so that its textures inline into Reussir code: the
  driver compiles textures and `leanrt` for the host CPU without outline
  atomics (a wrapper around rustc), hot paths are `#[inline(always)]`,
  cold paths `#[cold]` `extern "C"` (no landing pads), `make_mut` copies by
  value, and handle operations and the monotonic clock are out of line,
  taking their arguments by value.
- **Why:** A function with a stack slot whose address escapes (a `str`
  argument, a float or 4+ argument FFI call through the packed-argument
  path, a borrowed `&LHandle`, a `timespec` buffer) never has its self tail
  calls turned into loops by LLVM: IO loops over `getLine`, `flush`,
  `monoNanosNow` grew the stack until it overflowed (adv2 N2, 20e54f5);
  loops that print floats overflowed with the plain rustc; an inlined
  `&mut` to a caller's local cost the caller its tail calls (arr benchmark
  0.32 s → 0.03 s, c3cca07). Textures inline only when compiled for the
  same CPU and features as Reussir's code.
- **Where:** `scripts/l2r.py`: `NATIVE_FLAGS`, `rustc_wrapper`,
  `build_leanrt`; `LowerBase.lean`: `strLit`, `strLitTable`;
  `Lower/Values.lean`: `natLiteral`; `runtime/leanrt/src/array.rs`
  (`drop_last`, `copy_shared`, `make_mut`), `fs.rs`, `io.rs`;
  `runtime/README.md` ("Building and linking").
- **Remove only if:** Reussir guarantees tail calls, or passes these
  arguments without an escaping slot.

### Tail calls are not guaranteed

- **What:** lean2rr keeps loops as self tail calls within one function:
  join points are inlined, structured or duplicated before being outlined
  (J1, J2, J1′), a loop through outlined join points is one state machine
  (J4), and `Outline`'s parts of a recursive function return step values
  instead of tail-calling across functions.
- **Why:** LLVM turns a self tail call into a loop, but a mutual tail call
  only becomes a sibling call when all arguments fit in registers, and
  Reussir's reference counting after a call can prevent it.
- **Where:** [../control-flow/join-points.md](../control-flow/join-points.md),
  [../control-flow/state-machines.md](../control-flow/state-machines.md),
  [../control-flow/outline.md](../control-flow/outline.md#recursive-functions-keep-their-loops-step-values).
- **Remove only if:** Reussir guarantees tail calls (a candidate request).

### Applying a shared Reussir closure copies it

- **What:** Lean function values are generated enums dispatched by
  generated application functions, not Reussir closures; Reussir closures
  appear only in the `raw` variant and in prelude callbacks.
- **Why/Where:** see
  [../representations/function-values.md](../representations/function-values.md#function-values-are-generated-enums-not-reussir-closures).
- **Remove only if:** see the linked entry.

### `cell::set` releases the old value before it stores

- **What:** lean2rr's reference sets store first and release after, through
  an FFI call.
- **Why/Where:** see
  [../ownership.md](../ownership.md#reference-sets-store-the-new-value-before-releasing-the-old-one).
- **Remove only if:** see the linked entry.

### Rust allocations are 16-aligned (issue 3, a cost)

- **What:** The runtime allocates strings, arrays and big numbers with
  `mi_malloc`/`mi_realloc` directly, not through Rust's global allocator.
- **Why:** Reussir's global allocator raises every Rust allocation to
  16-byte alignment (intended) through mimalloc's aligned path. Without
  Reussir patch 03-a, a size that is not a multiple of 16 could be moved
  inside a larger block, and every later free in that block's page took
  mimalloc's slow path (up to 5% of a program's instructions, varying
  from run to run). 03-a rounds the size up instead. The runtime's own
  objects need only 8-byte alignment: `mi_malloc` keeps their blocks
  smaller either way
  ([03-global-alloc-align.md](../../../reussir-bugs/03-global-alloc-align.md);
  98f27d2).
- **Where:** `runtime/leanrt/src/alloc.rs`.
- **Remove only if:** never (the blocks would grow to multiples of 16).

### Token reuse picks decrements that never free (issue 7, missed optimization)

- **What:** The optional passes `lazy-fields` and `sink-proj` bind fields
  where they are used, so a value that stays live has no retained fields
  whose releases look like donors; `nullary-scrutinee` rebuilds a matched
  constructor without fields in its arm, so the scrutinee is not kept
  alive by a use there.
- **Why:** A missed optimization, not a bug: rrc's output is correct, only
  slower (allocations where a cell could be reused). Patch 07-a (an
  optimization, applied) covers some shapes (`UInt64` keys) but not a call
  before the branch (`Nat` and `String` comparisons), which the passes do
  ([07-phantom-reuse-donor.md](../../../reussir-bugs/07-phantom-reuse-donor.md)).
  07-a stays because 09-a uses its helper.
- **Where:** [../control-flow/cases.md](../control-flow/cases.md).
- **Remove only if:** Reussir's token reuse handles the call-before-branch
  shape; then measure with the passes off.

### A texture at a cold call site inlines only below cost 45 (issue 36, missed optimization)

- **What:** The runtime's textures on hot paths, the array reads above
  all, are kept small: each costs less than 45 in LLVM's inline cost model
  once its `_ffi` function is inlined into rrc's import trampoline. An
  array read is three textures (`l2r_array_give`, `l2r_view_size`,
  `l2r_view_take`) instead of one. With the one-word `Box`,
  `l2r_view_take<LAny>` costs more than 45: without Reussir patch 36-a,
  `RtReadsDeep`'s `Array` reads stay calls. 36-a marks a texture whose
  cost is at most LLVM's threshold for an ordinary call site (225, 250 at
  `-O aggressive`) and its trampoline `alwaysinline`; 36-b leaves out
  textures with a stack frame over 1024 bytes and textures that cannot
  return.
- **Why:** A missed optimization, not a bug: rrc defines the trampoline
  without an inline attribute, so LLVM inlines it into a caller by its
  ordinary cost model, at a call site it judges cold (deep in branches)
  only below 45. A read texture that checked the bounds (cost 80) stayed a
  call at 279 of lean-zip's array reads; one that decremented first and
  checked after (cost 55) at 41 reads of its LZ77 loop
  ([36-trampoline-inline.md](../../../reussir-bugs/36-trampoline-inline.md)).
- **Where:** [../ownership.md](../ownership.md#reads-give-their-reference-up-first-for-a-view);
  `runtime/prelude.rr` (the read textures).
- **Remove only if:** every Reussir that lean2rr supports has 36-a and
  36-b; then
  the read could be one texture again (measure the reads first).

### Drop glue recursed once per cell (issue 13, missing feature)

- **What:** The runtime frees its containers through the per-thread
  pending stack that patch 13-b adds (`reussir_rt::drop`), and needs it to
  build; 13-a and 13-c complete it.
- **Why:** A missing feature, not a bug: Reussir never promised frees of
  bounded depth (its drop glue recurses, as Rust's does), and Lean frees
  iteratively. Patches 13-a to 13-c (applied) add the feature
  ([13-long-list-drop.md](../../../reussir-bugs/13-long-list-drop.md)).
- **Where:** [../ownership.md](../ownership.md#containers-free-through-the-threads-pending-stack-in-leans-order).
- **Remove only if:** never (required).

### Each texture is its own crate

- **What:** All runtime code and global state live in one Rust crate,
  `leanrt`, linked into every program; the prelude's textures call into it.
  Drop hooks Reussir generates for the prelude's opaque types are textures
  without the prelude's `extern crate leanrt;`, so the driver's rustc
  wrapper adds `--extern leanrt` (and `--edition 2018` when rrc gives none,
  so `::leanrt` resolves).
- **Why:** Statics in the prelude's `extern "rust"` block would be
  duplicated per texture (one stdout buffer, one set of once-cells is
  required); the drop hooks name the containers' types
  (`::leanrt::drop::Vec`, 59b2551).
- **Where:** `runtime/leanrt/src/lib.rs`; `scripts/l2r.py`:
  `rustc_wrapper`.
- **Remove only if:** never.

### rrc writes scratch files into its working directory

- **What:** The driver runs rrc in its temporary directory, with absolute
  paths.
- **Why:** rrc leaves its polymorphic-FFI scratch files
  (`reussir_rust_module_*`) where it runs; two were once committed by
  accident (e746a33).
- **Where:** `scripts/l2r.py`: `main`.
- **Remove only if:** rrc cleans up after itself.

### The driver's choice of rrc flags

- **What:** `-O aggressive` by default; `--reuse-across-call` on unless
  `--no-reuse-across-call` (with the bug-4 retry); `--no-pack-record-members`
  (bug 2); `--no-closure-wpd` (issue 10, a cost); `L2R_RRC_FLAGS` appends
  flags for experiments. rrc runs with `REUSSIR_FFI_CACHE_DIR` set, for
  patch 35-a's texture cache (issue 35, a cost,
  [build-time.md](build-time.md#issue-35-cost-every-texture-is-compiled-again-on-every-build)).
  `leanrt` is built per Reussir checkout (`L2R_REUSSIR`) and cached by a
  hash of its sources, under a file lock for concurrent drivers; rustc
  runs in the crate's directory, so a rebuild gives the same bytes from
  any caller's directory (the texture cache hashes the rlibs).
- **Why:** `-O aggressive` made every classic benchmark faster than native
  (`-O default` left sieve 7% slower; e238a98). Reuse across calls is
  Lean's reset/reuse across calls (444a70a). The runtime rlib links against
  the checkout's runtime crates (e238a98, c3e9d99).
- **Where:** `scripts/l2r.py`: `main`, `leanrt_out`, `build_leanrt`,
  `build_locked`.
- **Remove only if:** n/a (configuration).
