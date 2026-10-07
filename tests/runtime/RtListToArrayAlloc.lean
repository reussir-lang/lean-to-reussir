/-! Runtime test (review HA-02): `List.toArray` (`Array.mk`, which lean2rr
lowers itself) makes the array at the list's length in one allocation, as
natively `List.toArrayImpl` reserves `Array.mkEmpty xs.length` once.
lean2rr pushed the elements onto an empty array, which grew about log2 n
times (up to twice the bytes). A list of 1000 small `Nat`s is converted `k`
times (the argument, default 10); tests/runtime/alloc-check.sh compares
the bytes requested at two `k`s (RtListToArrayAlloc.alloc): natively one
array of the list's length per conversion, and so in lean2rr. -/
def main (args : List String) : IO Unit := do
  let k := (args.head? >>= String.toNat?).getD 10
  let xs := List.range (1000 + args.length)
  let mut total := 0
  for i in [0:k] do
    let a := xs.toArray
    total := total + a.size + a[i % a.size]!
  IO.println total
