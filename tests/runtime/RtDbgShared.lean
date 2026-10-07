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
stores as array elements (`Array α` in the signature, as `Array.push`).

The cases after the first three (review HL-01): each storage type has its
own count. A shared `Array String`, `ByteArray`, `FloatArray`, thunk, big
`Nat` and big `Int` are reported, as natively (the big numbers were not:
the check did not know `Nat`'s and `Int`'s Rust types); a unique big `Nat`
and a small `Nat` (a scalar natively) are not; a string literal is (a
persistent object natively, a constant held by the program in lean2rr).
Tasks: RtDbgSharedTask. -/
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
  -- Each storage type's own count (review HL-01).
  let n := args.length
  let xs : Array String := (Array.range (n + 3)).map toString
  let xs2 := xs
  let xs' := dbgTraceIfShared "strarr" xs
  IO.println (xs'.size + xs2.size)
  let bs : ByteArray := ⟨(Array.range (n + 3)).map (·.toUInt8)⟩
  let bs2 := bs
  let bs' := dbgTraceIfShared "bytes" bs
  IO.println (bs'.size + bs2.size)
  let fs : FloatArray := ⟨(Array.range (n + 3)).map (·.toFloat)⟩
  let fs2 := fs
  let fs' := dbgTraceIfShared "floats" fs
  IO.println (fs'.size + fs2.size)
  let big : Nat := 2 ^ (100 + n)
  let big2 := big
  let big' := dbgTraceIfShared "bignat" big
  IO.println (decide (big' + big2 > 0))
  let bi : Int := -((2 ^ (100 + n) : Nat) : Int)
  let bi2 := bi
  let bi' := dbgTraceIfShared "bigint" bi
  IO.println (decide (bi' + bi2 < 0))
  let ub : Nat := 3 ^ (90 + n)
  let ub' := dbgTraceIfShared "unique bignat" ub
  IO.println (decide (ub' > 0))
  let sm : Nat := n + 5
  let sm2 := sm
  let sm' := dbgTraceIfShared "small" sm
  IO.println (sm' + sm2)
  let t : Thunk Nat := Thunk.mk fun _ => n + 1
  let t2 := t
  let t' := dbgTraceIfShared "thunk" t
  IO.println (t'.get + t2.get)
  let lit := "a literal"
  let lit' := dbgTraceIfShared "literal" lit
  IO.println lit'
