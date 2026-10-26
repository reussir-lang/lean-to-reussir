/-! Runtime test: reads at a `Nat` index or position from arrays of boxes
(`RtNatIdxWord.opts` turns off `typed-arrays` and `compact-arrays`, so
every array here holds boxes), at small indices and at 2^61, 2^62, 2^63,
2^64 and 2^70: `a[i]` (`fget`), `a[i]!` (`get!`: the panic and the
default), `a[i]?`, of `Nat`, `UInt8`, `UInt32`, `Bool` (read at a type
without a copy of the box: `boxWordRead?`), `Option Nat` and `List UInt8`
elements, `ByteArray` `get`/`get!`, and `String.Pos.Raw` `get`, `get'`,
`next'` and `atEnd`. lean2rr computes the index word first
(`l2r_nat_index`: the value below 2^63, `u64::MAX` from there) and calls
the prelude's `_w` reads (`lean_array_fget_as_w`, `lean_array_get_as_w`
for the reads at a type; tests/runtime/int-backend-check.sh checks it). -/

@[noinline] def idx (n : Nat) : Nat := n

@[noinline] def sumFget (a : Array Nat) : Nat := Id.run do
  let mut s := 0
  for h : i in [:a.size] do
    s := s + a[i]
  return s

@[noinline] def sumU8 (a : Array UInt8) : Nat := Id.run do
  let mut s := 0
  for h : i in [:a.size] do
    s := s + a[i].toNat
  return s

@[noinline] def countTrue (a : Array Bool) : Nat := Id.run do
  let mut s := 0
  for h : i in [:a.size] do
    if a[i] then s := s + 1
  return s

@[noinline] def bangNat (a : Array Nat) (i : Nat) : Nat := a[i]!
@[noinline] def bangU8 (a : Array UInt8) (i : Nat) : UInt8 := a[i]!
@[noinline] def bangU32 (a : Array UInt32) (i : Nat) : UInt32 := a[i]!
@[noinline] def bangBool (a : Array Bool) (i : Nat) : Bool := a[i]!
@[noinline] def bangOpt (a : Array (Option Nat)) (i : Nat) : Option Nat := a[i]!
@[noinline] def bangList (a : Array (List UInt8)) (i : Nat) : List UInt8 := a[i]!
@[noinline] def getOptU32 (a : Array UInt32) (i : Nat) : Option UInt32 := a[i]?

@[noinline] def bytesSum (b : ByteArray) : Nat := Id.run do
  let mut s := 0
  for h : i in [:b.size] do
    s := s + (b[i]'(Membership.get_elem_helper h rfl)).toNat
  return s

@[noinline] def bytesBang (b : ByteArray) (i : Nat) : UInt8 := b.get! i

@[noinline] def strGet (s : String) (p : Nat) : Char := String.Pos.Raw.get s ⟨p⟩
@[noinline] def strEnd (s : String) (p : Nat) : Bool := String.Pos.Raw.atEnd s ⟨p⟩
@[noinline] def countA (s : String) : Nat := s.foldl (fun n c => if c == 'a' then n + 1 else n) 0

def main : IO Unit := do
  let a := Array.range 6
  let u8 : Array UInt8 := a.map (·.toUInt8)
  let u32 : Array UInt32 := a.map (·.toUInt32 * 1000)
  let bs : Array Bool := a.map (· % 2 == 0)
  let o : Array (Option Nat) := a.map fun i => if i == 3 then none else some (i * 7)
  let l : Array (List UInt8) := a.map fun i => [i.toUInt8, 9]
  let b : ByteArray := ⟨u8⟩
  IO.println s!"sums {sumFget a} {sumU8 u8} {countTrue bs} {bytesSum b} {countA "banana"}"
  for n in [0, 2, 5, 6, 2^61 - 1, 2^61, 2^62, 2^63 - 1, 2^63, 2^64, 2^70] do
    let i := idx n
    IO.println s!"{n}: {bangNat a i} {bangU8 u8 i} {bangU32 u32 i} {bangBool bs i} {bangOpt o i} {bangList l i} {getOptU32 u32 i} {bytesBang b i} {strGet "héllo" i} {strEnd "héllo" i}"
