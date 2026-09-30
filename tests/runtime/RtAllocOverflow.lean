/-! Runtime test: an array capacity whose size in bytes overflows is
`INTERNAL PANIC: integer overflow in runtime computation` (exit 1), as
`lean_alloc_array`'s checked arithmetic; smaller huge capacities that can
be reserved are fine. -/

def main (args : List String) : IO Unit := do
  let k := args.length
  let a : Array Nat := Array.mkEmpty (2 ^ 30 + k)
  IO.println s!"capacity 2^30 ok {a.size}"
  let b : ByteArray := ByteArray.emptyWithCapacity (2 ^ 20 + k)
  IO.println s!"byte capacity ok {b.size}"
  let c : Array String := Array.mkEmpty (2 ^ 62 + k)
  IO.println s!"never {c.size}"
