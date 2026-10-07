# Calling the program's C code (parked)

**Status: parked, not supported, not a goal for now.** A Lean program may
implement some of its own `@[extern "sym"]` declarations in C (written
against `<lean/lean.h>`, built by Lake). The owner's decision of
2026-10-03 is to target Lean code with Lean's runtime library as the only
native code, so lean2rr never compiles, links or calls such C: the extern
runs the function its C symbol binds to, else its Lean definition, else
lean2rr rejects the program ([program-externs.md](program-externs.md)).
Where lean2rr's own layouts and Lean's object layouts conflict, lean2rr's
win. The C FFI work is kept on an unmerged branch, described below so it
can be resumed; nothing of it is in the translator. The one piece merged
is the single-block layout of strings and arrays with Lean's header sizes
(mem-layout, 7a784e1), which lean2rr uses for its own sake
([strings](../representations/strings.md#a-string-keeps-its-character-count),
[arrays](../representations/arrays.md#an-array-is-one-block)).

### Branch `ffi-c`: linking and calling the program's C (parked at ffac4f1)

- **What:** `scripts/l2r.py --link-c LIB|OBJ`, `--lake-project DIR`
  (Lake `extern_lib` archives) and `--link-arg` link the program's C,
  whose symbols lean2rr receives as `--external-symbols`. An extern call
  gets lean2rr's own implementation, else the program's C, else the Lean
  body (branch `lean-externs`), else Lean's C/C++ in `libleanshared`,
  else a build error. A program with C links Lean's runtime
  (`libleanshared.so`, one mimalloc) and initializes it. Calls use Lean's
  impure signature, one generated texture per symbol and argument
  representation (`l2r_cffi_call_<sym>_<hash>`). Values cross in three
  tiers: as they are (`String`, `ByteArray`/`FloatArray`, `Array Nat` of
  small elements, with Lean's tags and a NUL terminator in the string
  block); converted to Lean objects and back (`Nat`/`Int`, structures and
  inductives laid out by `getCtorLayout`, other arrays, IO results); or
  through bridges (foreign objects, closures both ways, file handles).
  Thunks, tasks, references and other runtime objects crossing are build
  errors. Tests `tests/ffi/run.sh` (9 programs) pass on the branch.
- **Why parked:** The current targets have no C of their own. The branch
  also changes lean2rr's own layouts for every program (the string
  block's tag and NUL, `ByteArray`/`FloatArray` as one block whose
  `ByteArray.mk`/`data` copy), to be re-evaluated or reverted since
  lean2rr's layouts win; it predates mem-nat's one-word `Nat` and has not
  been reviewed since 406fd6c. Notes: local notes (what is left and how
  to resume); design: plan §5.15 on the branch.
- **Where (on the branch):** `Lower/CFFI.lean` (`isCExtern`,
  `cExternCall`, `toObj`/`ofObj`), `Lower/ExternCall.lean`,
  `runtime/leanrt/src/cffi.rs`, `sarray.rs`, `scripts/l2r.py`,
  `tests/ffi/`.
- **Remove only if:** n/a (not merged).

### Branch `lean-externs`: merged into the Lean-only rule

- **What:** Its Lean-body fallback, missing-extern report, prelude
  function set and library-symbol redirect were ported to Lean 4.34 and
  changed to the Lean-only rule (branch `extern-bodies`):
  [program-externs.md](program-externs.md).
- **Remove only if:** n/a.
