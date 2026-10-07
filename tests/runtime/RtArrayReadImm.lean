/-! Runtime test: reads of an array element at a type a box holds as an
immediate (`UInt8`, `UInt16`, `UInt32`, `Char`, `Bool`, an enumeration) or
as an immediate or a counted big number (`Nat`, `Int`), which lean2rr
reads without a copy of an immediate's box (`boxWordRead?`,
`l2r_view_take_as`): `a[i]` with a proof (a `for` loop over the indices),
`a[i]!` in and out of bounds (the default returned, a big one included,
and `get!`'s panic message), `uget` (`Array.foldl`, `for ... in`), on a
shared array (another reference kept and read afterwards) and on the last
reference (the read frees the array). -/

inductive Dir where
  | n | e | s | w
deriving Repr, Inhabited, BEq

@[noinline] def sumBytes (a : Array UInt8) : Nat := Id.run do
  let mut s := 0
  for h : i in [0:a.size] do
    s := s + a[i].toNat
  return s

@[noinline] def getBang (a : Array UInt16) (i : Nat) : UInt16 := a[i]!

@[noinline] def getLast (a : Array UInt32) : UInt32 := a[a.size - 1]!

@[noinline] def firstFalse (a : Array Bool) : Nat := Id.run do
  let mut k := 0
  for b in a do
    if !b then return k
    k := k + 1
  return k

@[noinline] def countTrue (a : Array Bool) : Nat := a.foldl (fun n b => if b then n + 1 else n) 0

@[noinline] def dirAt (a : Array Dir) (i : Nat) : Dir := a[i]!

@[noinline] def charAt (a : Array Char) (i : Nat) : Char := a[i]!

@[noinline] def mkBytes (n : Nat) : Array UInt8 := (Array.range n).map (fun i => (i * 7).toUInt8)

@[noinline] def natAt (a : Array Nat) (i : Nat) : Nat := a[i]!

@[noinline] def natAtD (a : Array Nat) (d : Nat) (i : Nat) : Nat :=
  haveI : Inhabited Nat := ⟨d⟩
  a[i]!

@[noinline] def intSum (a : Array Int) : Int := Id.run do
  let mut s := 0
  for h : i in [0:a.size] do
    s := s + a[i]
  return s

@[noinline] def mkNats (n : Nat) : Array Nat := (Array.range n).map (fun i => i * 2 ^ (i % 3 * 40))

def main : IO Unit := do
  let bytes := mkBytes 300
  IO.println (sumBytes bytes)
  IO.println (sumBytes (mkBytes 5))
  let ws : Array UInt16 := #[1, 65535, 300]
  IO.println s!"{getBang ws 1} {getBang ws 2} {getBang ws 3} {ws.size}"
  IO.println (getLast #[(7 : UInt32), 4294967295])
  IO.println (getLast ((Array.range 10).map (·.toUInt32)))
  let bs := #[true, false, true, true]
  IO.println s!"{firstFalse bs} {firstFalse #[true, true]} {countTrue bs} {countTrue (bs.push false)}"
  let ds := #[Dir.n, .e, .s, .w]
  IO.println s!"{repr (dirAt ds 2)} {repr (dirAt ds 9)} {repr (dirAt #[Dir.w] 0)}"
  IO.println s!"{charAt #['a', 'λ', '€'] 1} {charAt #['a'] 4} {charAt "xyz".toList.toArray 2}"
  let ns := mkNats 9
  IO.println s!"{natAt ns 2} {natAt ns 3} {natAt ns 20} {natAtD ns (2 ^ 70) 20} {ns.size}"
  IO.println s!"{natAt (mkNats 6) 5} {natAtD (mkNats 3) 7 1} {natAtD #[] (2 ^ 65 + 1) 0}"
  IO.println s!"{intSum #[1, -2, 2 ^ 64, -(2 ^ 66), 7]} {intSum ((Array.range 5).map (fun (i : Nat) => (i : Int) - 2 ^ 63))}"
