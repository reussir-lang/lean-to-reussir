# Externs and FFI

How a Lean `@[extern]` call becomes code: a runtime function named after
the C symbol, generated glue, a Lean definition compiled with the program
(Lean's own `@[export]`s and lean2rr's shim). An extern of the program
runs its Lean definition, or the program's own `@[export]` its C symbol
binds to: lean2rr compiles Lean code plus Lean's runtime library only,
never the program's C (the owner's decision, 2026-10-03), and binds no
extern of the program to Lean's runtime (2026-10-04). Plan
[§5.8](../../translation-plan.md#58-externs-and-runtime-calls); the
runtime's conventions are in [`runtime/README.md`](../../../runtime/README.md)
("Calling convention", "Glue helpers").

- [dispatch.md](dispatch.md): which implementation an extern call gets, in
  which order.
- [program-externs.md](program-externs.md): externs of the program and
  of packages: the binding of their C symbol to an `@[export]` and its two
  tests, their Lean definitions, refusals, why an extern of the program is
  not a cast by itself, the test harness's `.ffi.c`, `.refused`,
  `.l2r-log` and `.l2r-debug`.
- [glue.md](glue.md): storage types, payload primitives, fallible IO,
  streams, processes and the other generated glue.
- [shim.md](shim.md): `L2RShim`, lean2rr's Lean library for
  `Std.Internal.UV`, time, `ShareCommon`, and definitions it replaces.
- [runtime.md](runtime.md): special cases inside the runtime's own
  implementation of single externs (libm, huge array sizes, a read right
  after output, a child's `null` streams, `System.Platform.target`), the
  glue around lean-runtime's rules, and how leanrt is built with the shared
  crate lean-runtime.
- [c-ffi.md](c-ffi.md): calling the program's C code (parked, branch
  `ffi-c`; not a goal for now).
