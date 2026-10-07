/-! Runtime test: a byte-array capacity that cannot be allocated. The
capacity is only a hint (the Lean definition gives the empty array whatever
it is): lean2rr reserves nothing and gives the empty array (lean-runtime's
LB-37, a lifted limit; `NAME.l2r.*`), where native ends with `INTERNAL
PANIC: out of memory` (exit 1), as a failed `malloc` in `lean_alloc_sarray`
(`NAME.native.*`). -/

def main (args : List String) : IO Unit := do
  IO.println "before"
  let b : ByteArray := ByteArray.emptyWithCapacity (2 ^ 62 + args.length)
  IO.println s!"capacity 2^62: size {b.size}"
