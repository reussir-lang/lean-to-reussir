# Which implementation an extern call gets

Paths are relative to `lean2rr/LeanToReussir/` unless they start with
`runtime/` or `lean2rr/`.

### An extern is the prelude function named after its C symbol

- **What:** By default a saturated extern call is a call of the prelude
  function with the extern's C symbol (`lean_xxx`), passing the extern's
  mono parameters without erased ones, proofs and the IO world; a
  polymorphic extern's function gets the storage types of its type
  arguments explicitly (`lean_array_push<E>`). A function the prelude does
  not define makes lean2rr reject the program, naming the extern
  ([program-externs.md](program-externs.md#refusals-are-reported-at-translation-with-the-reason)).
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

- **What:** Stage 1 redirects a call of an extern of Lean's library whose
  C symbol some Lean
  definition exports (`@[export sym]`: the `lean_string_*` and
  `lean_substring_*` symbols of `String.Internal.*` and
  `Substring.Raw.Internal.*`, `lean_string_intercalate`, …) to that
  definition, which is then compiled like any other (an extern of the
  program only when the binding's tests pass,
  [program-externs.md](program-externs.md#a-binding-needs-one-type-and-one-compiled-signature)). (Lean's other
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
  a shim override, else, for an extern of Lean's library, to an
  `@[export]` Lean definition of its symbol, and an extern of the program
  follows its route (its `@[implemented_by]` target; its Lean definition,
  or a `noinline` declaration calling the `@[export]` definition its
  symbol binds to; or it stays an extern, refused:
  [program-externs.md](program-externs.md)) (else, only with
  `MonoConfig.safeSources`, off, a type-unsafe implementation to its safe
  declaration); (2) Stage 4
  replaces a unary call of a definition the configuration replaces
  (`prelude-repr`: `Nat.repr`, `Nat.reprFast`, `Int.repr` →
  `l2r_nat_repr`/`l2r_int_repr`); (3) it lowers a constructor with an
  `@[extern]` as an extern call; (4) generated glue for externs over
  Lean-defined types, thunks, tasks, promises, processes and references;
  (5) a fallible IO extern's runtime primitive with the last-error
  protocol; (6) a `BaseIO` extern's payload primitive, `l2r_` followed by
  the symbol without `lean_`; (7) a generic prelude function in plain
  Reussir, at the value types; (8) the prelude function named after the
  symbol, with storage types (`Box` for an extern over arrays); (9)
  otherwise lean2rr rejects the program, naming the extern. A refused extern of the program gets no glue, and the
  program is rejected.
- **Why:** lean2rr's own implementations first; the more specific glue
  before the generic call.
- **Where:** `Mono.lean`: `redirectTarget`; `Lower/Values.lean`:
  `lowerConstApp`, `preludeReplacement?`; `Lower/Decls.lean`: `calleeOf`;
  `Lower/ExternCall.lean`: `customExtern`, `lowerExternCall`.
- **Remove only if:** n/a (a description). lean2rr never calls the
  program's C code ([program-externs.md](program-externs.md); the C FFI
  work is parked, [c-ffi.md](c-ffi.md)).

### Every `Init`/`Std` extern is available; `Lean`'s C++ parts are not

- **What:** All 717 extern symbols of Lean 4.34's `Init` and `Std` (767
  declarations) have an implementation (706 checked by programs that call
  each one, 11 internal ones by direct tests). Lean 4.34 added two:
  `lean_system_platform_linux` (`System.Platform.getIsLinux`, test
  `RtPlatform`) and `lean_string_utf8_extract_fast` for `String.extract`
  (`lean_string_utf8_extract` remains, for `String.Pos.Raw.extract` and
  `String.Internal.extract`; tests `RtString`, `RtStringExtractBig`). The
  `Lean` library's C++-implemented externs (`Expr.mkData`, `evalConst`,
  `Dynlib`, the LLVM bindings, …) are not: lean2rr rejects a program that
  reaches one, naming each, and does not run their Lean bodies in their
  place (test `RtLeanUnsupported`, expected to fail).
- **Why:** Every constant is a root, so even an unused one that reaches
  such an extern makes lean2rr reject the program
  ([../startup/order.md](../startup/order.md#every-constant-of-the-program-is-a-root)).
- **Where:** `runtime/prelude.rr`, `lean2rr/L2RShim.lean`;
  [`docs/implementation-status.md`](../../implementation-status.md).
- **Remove only if:** n/a.

