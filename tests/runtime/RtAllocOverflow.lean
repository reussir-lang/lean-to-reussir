/-! Runtime test: an array capacity whose size in bytes overflows. The
capacity is only a hint (the Lean definitions give the empty array whatever
it is): lean2rr reserves nothing and gives the empty array (lean-runtime's
LB-37, a lifted limit; `NAME.l2r.*`), where native ends with `INTERNAL
PANIC: integer overflow in runtime computation` (exit 1), as
`lean_alloc_array`'s checked arithmetic (`NAME.native.*`). Smaller huge
capacities that can be reserved are reserved, as natively. -/

def main (args : List String) : IO Unit := do
  let k := args.length
  let a : Array Nat := Array.mkEmpty (2 ^ 30 + k)
  IO.println s!"capacity 2^30 ok {a.size}"
  let b : ByteArray := ByteArray.emptyWithCapacity (2 ^ 20 + k)
  IO.println s!"byte capacity ok {b.size}"
  let c : Array String := Array.mkEmpty (2 ^ 62 + k)
  IO.println s!"capacity 2^62: size {c.size}"
