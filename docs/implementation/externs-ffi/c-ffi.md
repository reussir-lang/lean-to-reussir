# Calling the program's C code (parked)

**Status: parked, not supported.** A Lean program may implement some of
its own `@[extern "sym"]` declarations in C (written against
`<lean/lean.h>`, built by Lake). lean2rr links no C code of the program
and does not compile such an extern's Lean body in its place: the
generated code calls a function named after the symbol that the prelude
does not define, so the build fails in rrc with an unknown function
([dispatch.md](dispatch.md#the-order-an-extern-call-takes), step 10; plan
[§10](../../translation-plan.md#10-known-divergences-and-unsupported-features),
"Not supported"). The targets for now are programs that use only `Init`
and `Std`, and where lean2rr's own layouts and Lean's object layouts
conflict, lean2rr's win. The work is kept on two unmerged branches,
described below so it can be resumed; nothing on them is in the
translator. The one piece merged is the single-block layout of strings
and `Array Nat`/`Int` with Lean's header sizes (mem-layout, 7a784e1),
which lean2rr uses for its own sake
([strings](../representations/strings.md#a-string-keeps-its-character-count),
[arrays](../representations/arrays.md#array-nat-and-array-int-store-one-word-per-element)).

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

### Branch `lean-externs`: the Lean body as a fallback (parked at fb3bb77)

- **What:** An `@[extern "sym"]` definition of the program whose symbol
  nothing implements (prelude, `@[export]` definition, glue, linked C) is
  compiled from its Lean body (the definition, or its `_unsafe_rec`
  version); an opaque without one stays an extern. lean2rr then rejects a
  program that still calls an extern nothing implements and lists each
  one with its declaration, instead of leaving them to rrc
  (`L2R_ALLOW_MISSING_EXTERNS=1` only warns). Reviewed through round 3
  (RV8E-01..11 fixed); test `RtExternBody`.
- **Why parked:** It is the third step of `ffi-c`'s precedence and goes
  with it: the two branches overlap (`--external-symbols`, the
  missing-extern error) and are to be merged together, if the C FFI is
  resumed.
- **Where (on the branch):** `Mono.lean`: `externBodyFallback`,
  `externBodyDecl`; `Emit/Program.lean`: `lowerProgram` (the
  missing-extern report).
- **Remove only if:** n/a (not merged).
