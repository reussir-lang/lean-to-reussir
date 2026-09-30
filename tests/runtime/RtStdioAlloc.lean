/-! Runtime test (glibc stdio model): huge capacities that mimalloc reserves (MAP_NORESERVE) but
glibc malloc refuses (more than RAM + swap under heuristic overcommit). -/

def main (args : List String) : IO Unit := do
  let k := args.length
  let b : ByteArray := ByteArray.emptyWithCapacity (2 ^ 37 + k)
  IO.println s!"byte capacity 2^37 ok {b.size}"
  let a : Array Nat := Array.mkEmpty (2 ^ 35 + k)
  IO.println s!"array capacity 2^35 ok {a.size}"
  let c : ByteArray := ByteArray.emptyWithCapacity (2 ^ 45 + k)
  IO.println s!"byte capacity 2^45 ok {c.size}"
