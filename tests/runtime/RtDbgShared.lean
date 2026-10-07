/-! Runtime test: `dbgTraceIfShared` on a shared array, a shared list and an
unshared array (correctness review of rule 1, finding 1). Natively the first
two print `shared RC arr` and `shared RC list` to stderr. The extern is
generic (`dbgTraceIfShared {α} (s : String) (a : α) : α`); lean2rr passes
`α`'s values in a storage type chosen per type parameter. It once chose
`Box` for every type argument of an extern instantiated at an array type
(its instantiated parameter types mentioned `Array`), so at
`α := Array Nat` the array went into a new box, and the extern looked at
that box's sharing: it never reported the array as shared (and each call
allocated a cell, before the one-word box). The storage is now decided
from the declared signature: `Box` only for a type parameter the extern
stores as array elements (`Array α` in the signature, as `Array.push`). -/
def main (args : List String) : IO Unit := do
  let a := Array.replicate (args.length + 2) (0 : Nat)
  let b := a
  let c := dbgTraceIfShared "arr" a
  IO.println (c.size + b.size)
  let l := List.replicate (args.length + 2) (0 : Nat)
  let m := l
  let k := dbgTraceIfShared "list" l
  IO.println (k.length + m.length)
  let d := Array.replicate (args.length + 2) (0 : Nat)
  let e := dbgTraceIfShared "unique" d
  IO.println e.size
