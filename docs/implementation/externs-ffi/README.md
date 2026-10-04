# Externs and FFI

How a Lean `@[extern]` call becomes code: a runtime function named after
the C symbol, generated glue, a Lean definition compiled with the program
(Lean's own `@[export]`s and lean2rr's shim). Calling the program's own
C code is not supported (the work is parked). Plan
[§5.8](../../translation-plan.md#58-externs-and-runtime-calls); the
runtime's conventions are in [`runtime/README.md`](../../../runtime/README.md)
("Calling convention", "Glue helpers").

- [dispatch.md](dispatch.md): which implementation an extern call gets, in
  which order.
- [glue.md](glue.md): storage types, payload primitives, fallible IO,
  streams, processes and the other generated glue.
- [shim.md](shim.md): `L2RShim`, lean2rr's Lean library for
  `Std.Internal.UV`, time, `ShareCommon`, and definitions it replaces.
- [runtime.md](runtime.md): special cases inside the runtime's own
  implementation of single externs (libm, huge array sizes,
  `System.Platform.target`), the glue around lean-runtime's rules, and how
  leanrt is built with the shared crate lean-runtime.
- [c-ffi.md](c-ffi.md): calling the program's C code (parked, branches
  `ffi-c` and `lean-externs`).
