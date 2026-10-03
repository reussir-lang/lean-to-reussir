# Which implementation an extern call gets

Paths are relative to `lean2rr/LeanToReussir/` unless they start with
`runtime/` or `lean2rr/`.

### An extern is the prelude function named after its C symbol

- **What:** By default a saturated extern call is a call of the prelude
  function with the extern's C symbol (`lean_xxx`), passing the extern's
  mono parameters without erased ones, proofs and the IO world; a
  polymorphic extern's function gets the storage types of its type
  arguments explicitly (`lean_array_push<E>`). lean2rr does not check that
  the prelude defines the function: for a missing one, rrc reports an
  unknown function at build time.
- **Why:** One naming rule for every extern; the runtime implements
  `lean.h`'s semantics on lean2rr's types.
- **Where:** `Lower/ExternCall.lean`: `lowerExternCall`;
  `Lower/Externs.lean`: `externSymbol`, `externParamPassed`;
  `runtime/prelude.rr`. `lean2rr --emit externs` lists the externs a
  program calls (`Emit/Program.lean`: `externReport`).
- **Remove only if:** never. Plan
  [§5.8](../../translation-plan.md#58-externs-and-runtime-calls) and §10
  ("Not supported").

### Externs that Lean implements in Lean are compiled from Lean

- **What:** Stage 1 redirects a call of an extern whose C symbol some Lean
  definition exports (`@[export sym]`: the `lean_string_*` and
  `lean_substring_*` symbols of `String.Internal.*` and
  `Substring.Raw.Internal.*`, `lean_string_intercalate`, …) to that
  definition, which is then compiled like any other. (Lean's other
  `@[export]`s, such as the `IO.Error` builders its C runtime calls, are
  used by lean2rr's glue directly:
  [glue.md](glue.md#fallible-io-uses-a-last-error-slot-and-leans-own-error-builders).)
- **Why:** Lean's runtime calls back into compiled Lean code there; calling
  the definition directly gives exactly Lean's semantics (runtime request
  10, b9b3375). This takes precedence over a hand-written prelude version.
- **Where:** `Mono.lean`: `redirectTarget`, `exportMap`.
- **Remove only if:** never. It makes a program that declares its own
  `@[export]` able to cast
  ([../types/uniform-types.md](../types/uniform-types.md#whether-the-program-can-cast-at-all-is-a-whole-program-fact)).

### The shim can replace any definition

- **What:** A definition `L2RShim` exports as `l2r_override_<mangled
  name>` is called instead of the definition of that name, wherever the
  program calls it.
- **Why:** For definitions whose native behaviour depends on Lean's
  reference counting in a way the translation does not reproduce
  ([shim.md](shim.md#iopromiseisresolved-is-replaced-borrow-dependent-behaviour)).
- **Where:** `Mono.lean`: `redirectTarget`; `lean2rr/L2RShim.lean` (end
  of file).
- **Remove only if:** no definition needs replacing.

### The order an extern call takes

- **What:** For a call of `f`, in this order: (1) Stage 1 redirects `f` to
  a shim override, else, for an extern, to an `@[export]` Lean
  definition of its symbol (else, only with `MonoConfig.safeSources`, off,
  a type-unsafe implementation to its safe declaration); (2) Stage 4
  replaces a unary call of a definition the configuration replaces
  (`prelude-repr`: `Nat.repr`, `Nat.reprFast`, `Int.repr` →
  `l2r_nat_repr`/`l2r_int_repr`); (3) it lowers a constructor with an
  `@[extern]` as an extern call; (4) generated glue for externs over
  Lean-defined types, thunks, tasks, promises, processes and references;
  (5) a fallible IO extern's runtime primitive with the last-error
  protocol; (6) a `BaseIO` extern's payload primitive, `l2r_` followed by
  the symbol without `lean_`; (7) a generic prelude function in plain
  Reussir, at the value types; (8) the `natarr`/`intarr` function for
  `Array Nat`/`Array Int`; (9) the prelude function named after the
  symbol, with storage types; (10) otherwise rrc reports an unknown
  function.
- **Why:** lean2rr's own implementations first; the more specific glue
  before the generic call.
- **Where:** `Mono.lean`: `redirectTarget`; `Lower/Values.lean`:
  `lowerConstApp`, `preludeReplacement?`; `Lower/Decls.lean`: `calleeOf`;
  `Lower/ExternCall.lean`: `customExtern`, `lowerExternCall`.
- **Remove only if:** n/a (a description). Step (10) is also what a
  program's own `@[extern]` C code gets: lean2rr links no C code of the
  program, so such a program fails at the rrc build. The C FFI work that
  would put the program's C after lean2rr's own implementation, then the
  extern's Lean body, then a lean2rr error naming the extern, is parked
  ([c-ffi.md](c-ffi.md)).

### Every `Init`/`Std` extern is available; `Lean`'s C++ parts are not

- **What:** All 716 externs of Lean 4.34's `Init` and `Std` have an
  implementation (705 checked by programs that call each one, 11 internal
  ones by direct tests). Lean 4.34 added one, `System.Platform.getIsLinux`
  (`lean_system_platform_linux`, test `RtPlatform`), and moved
  `String.extract` to a new symbol, `lean_string_utf8_extract_fast`. The
  `Lean` library's C++-implemented externs (`Expr.mkData`, `evalConst`,
  `Dynlib`, the LLVM bindings, …) are not: for a program that reaches one,
  rrc reports an unknown function.
- **Why:** Every constant is a root, so even an unused one that reaches
  such an extern fails the build
  ([../startup/order.md](../startup/order.md#every-constant-of-the-program-is-a-root)).
- **Where:** `runtime/prelude.rr`, `lean2rr/L2RShim.lean`;
  [`docs/implementation-status.md`](../../implementation-status.md).
- **Remove only if:** n/a.

### Toolchain queries answer the pinned toolchain's constants

- **What:** `Lean.githash`, `Lean.version.*` (so `Lean.versionString`),
  `System.Platform.isWindows/isOSX/isLinux/isEmscripten`, `target` and
  `Lean.Internal.isStage0/hasLLVMBackend` are prelude constants:
  `lean_get_githash` (the toolchain's commit), `lean_version_get_minor`
  (34), …, `lean_system_platform_linux` (`true`).
- **Why:** Natively they are compile-time constants of the toolchain's
  runtime; a program built by lean2rr must answer what the same program
  built natively answers.
- **Where:** `runtime/prelude.rr` (`lean_get_githash` to
  `lean_system_platform_target`); test `RtPlatform`.
- **Remove only if:** never. Update them with every toolchain change
  (`lean2rr/lean-toolchain`); `RtPlatform` fails otherwise.
