/-! Runtime test: array allocators asked for a huge size (cross-test XT-5,
the `panics` fixture's rows `array_replicate_nonscalar` and
`array_replicate_huge`). Natively the message depends on the allocator and
on the size (`lean.h`, `object.cpp`):
- `Array.replicate n` (`lean_mk_array`) takes any `n` below 2^64 as a
  `size_t`, also a big `Nat` (2^63 or more), and `lean_alloc_array`'s byte
  size `24 + 8n` then overflows: `integer overflow in runtime computation`;
  2^64 or more is `out of memory`;
- `Array.mkEmpty`, `ByteArray.emptyWithCapacity` and
  `FloatArray.emptyWithCapacity` are `out of memory` for every big `Nat`;
  a small capacity overflows like `replicate` (`24 + elem * n`, elements of
  8 bytes, 1 for `ByteArray`) or fails to allocate (`out of memory`).
lean2rr's `replicate` took the out-of-memory path for every big `Nat`.
A capacity is only a hint (the Lean definitions give the empty array
whatever it is): lean2rr's `mkEmpty`, `ByteArray.emptyWithCapacity` and
`FloatArray.emptyWithCapacity` reserve nothing for a capacity that cannot
be reserved and give the empty array (lean-runtime's LB-37, a lifted limit;
`NAME.l2r.out`), where native ends as above (`NAME.native.out`);
`replicate` ends as natively.
The `.pipe` runs one allocation per process: the allocator and the size
come from the command line. `Array Nat` and `Array Int` have their own
representation in lean2rr (one word per element), so they are separate
cases. -/

def main (args : List String) : IO Unit := do
  let n := args[1]!.toNat!
  match args[0]! with
  | "replicate" => IO.println (Array.replicate n "s").size
  | "replicateNat" => IO.println (Array.replicate n (7 : Nat)).size
  | "replicateInt" => IO.println (Array.replicate n (-7 : Int)).size
  | "replicateFloat" => IO.println (Array.replicate n (1.5 : Float)).size
  | "mkEmpty" => IO.println (Array.mkEmpty (α := String) n).size
  | "mkEmptyNat" => IO.println (Array.mkEmpty (α := Nat) n).size
  | "byteArray" => IO.println (ByteArray.emptyWithCapacity n).size
  | "floatArray" => IO.println (FloatArray.emptyWithCapacity n).size
  | _ => IO.println "unknown case"
