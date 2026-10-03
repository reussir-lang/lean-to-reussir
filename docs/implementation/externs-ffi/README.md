# Externs and FFI

How a Lean `@[extern]` call becomes code: a runtime function named after
the C symbol, generated glue, a Lean definition compiled with the program
(Lean's own `@[export]`s and lean2rr's shim), and, in progress, the
program's own C code. Plan
[§5.8](../../translation-plan.md#58-externs-and-runtime-calls); the
runtime's conventions are in [`runtime/README.md`](../../../runtime/README.md)
("Calling convention", "Glue helpers").

- [dispatch.md](dispatch.md): which implementation an extern call gets, in
  which order, and the planned order once C code can be linked.
- [glue.md](glue.md): storage types, payload primitives, fallible IO,
  streams, processes and the other generated glue.
- [shim.md](shim.md): `L2RShim`, lean2rr's Lean library for
  `Std.Internal.UV`, time, `ShareCommon`, and definitions it replaces.
- [c-ffi.md](c-ffi.md): calling the program's C code (in progress, branch
  `ffi-c`).
