/-!
# lean2rr's shim: the part over `Init` only

The definitions of lean2rr's shim (`L2RShim`, see its header) that need
nothing but `Init`. `L2RShim` imports this module. lean2rr loads `L2RShim`
with every program, and only this module when the modules of `Std` that
`L2RShim` imports declare a name that the program declares too (natively
the program can declare it, since it does not import them; see
`LeanToReussir.loadEnvironment`). So these definitions are there for every
program.
-/

namespace L2RShim

/-! ## Sharing (`src/runtime/sharecommon.cpp`)

Natively `ShareCommon.Object.eq` compares two objects' headers and bodies
byte by byte (the same constructor and the same fields: scalars equal,
pointers to the same objects) and `hash` hashes them, for the tables of
`ShareCommon.State`. lean2rr's runtime implements `shareCommon` itself as
the identity (it shares nothing; translation plan §5.8), and lean2rr's
objects have no Lean layout to compare, so here objects are compared and
hashed by `ptrAddrUnsafe`, which does not emulate identity (plan §9): at
most the same cell is equal, `false` (natively possibly `true`) for two
distinct objects with the same fields. -/

@[export lean_sharecommon_eq]
unsafe def shareCommonEq (a b : ShareCommon.Object) : Bool :=
  ptrAddrUnsafe a == ptrAddrUnsafe b

@[export lean_sharecommon_hash]
unsafe def shareCommonHash (a : ShareCommon.Object) : UInt64 :=
  hash (ptrAddrUnsafe a).toUInt64

/-! ## Definitions the shim replaces

A definition exported as `l2r_override_<its mangled name>` replaces the
Lean definition wherever the program calls it (`Mono.redirectTarget`). -/

/-- `IO.hasFinished promise.result?`, the promise released after the
question (`leanrt::task::promise_is_resolved`). -/
@[extern "lean_shim_promise_is_resolved"]
opaque primPromiseIsResolved {α : Type} (promise : @& IO.Promise α) : BaseIO Bool

/-- `IO.Promise.isResolved`. Natively its parameter is borrowed (Lean's
borrow inference: `result?` borrows it), so the caller releases the promise
after the question; were this the last reference, which resolves the
promise with `none`, the answer is still the state before. Compiled as
written, the promise would be released inside `result?`, before the
question. -/
@[export l2r_override_IO_Promise_isResolved]
def promiseIsResolved {α : Type} (promise : IO.Promise α) : BaseIO Bool :=
  primPromiseIsResolved promise

end L2RShim
