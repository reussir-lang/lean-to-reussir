-- Nested maps that change the element representation (round 6, PRG6-01):
-- the inner map runs split inside the outer split loop. Rows of big Nat values
-- (≥ 2^63 and ≥ 2^64) mapped to Int / String / Bool inside an outer map.
def main : IO Unit := do
  let t : Array (Array Bool) := (Array.range 2000).map fun r => (Array.range 50).map fun c => (r * c) % 3 == 0
  IO.println s!"{t.size} {t.foldl (fun acc r => acc + (r.filter id).size) 0}"
  let rows : Array (Array Nat) := (Array.range 4).map fun r => (Array.range 6).map fun c => 2^62 * (r + 1) + c * 2^63 + 2^64 * (c % 2)
  IO.println s!"rows: {rows}"
  let ints : Array (Array Int) := rows.map fun (row : Array Nat) => row.map fun (x : Nat) => (x : Int) - 2^64
  IO.println s!"ints: {ints}"
  let strs : Array (Array String) := rows.map (·.map fun x => toString (x % 1000000007))
  IO.println s!"strs: {strs}"
  let back : Array (Array Nat) := ints.map (·.map fun i => (i + 2^64).toNat)
  IO.println s!"roundtrip equal: {back == rows}"
  let bytes : Array ByteArray := (Array.range 100).map fun r => ByteArray.mk ((Array.range 16).map fun c => (r + c).toUInt8)
  IO.println s!"bytes: {bytes.foldl (fun a b => a + b.size) 0} {bytes[99]!.data}"
