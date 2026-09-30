/-! Runtime test: a byte-array capacity that cannot be allocated is
`INTERNAL PANIC: out of memory` (exit 1), as a failed `malloc` in
`lean_alloc_sarray`. -/

def main (args : List String) : IO Unit := do
  IO.println "before"
  let b : ByteArray := ByteArray.emptyWithCapacity (2 ^ 62 + args.length)
  IO.println s!"never {b.size}"
