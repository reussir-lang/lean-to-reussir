import Std.Data.HashMap
/-! Runtime test: `Array.map` between element types of different
representations (`Nat` to `String`, structures, floats, chars) and
`Array.modify` (whose implementations use `unsafeCast`). -/

structure P where
  x : Nat
  name : String
deriving Repr, BEq, Hashable

def main (args : List String) : IO Unit := do
  let n := args.length + 20
  let a := (Array.range n).map (· * 3 % 17)
  let ps := #[{ x := 1, name := "a" : P }, { x := 2, name := "b" }]
  IO.println s!"eq {a == a} {a == a.pop} strings {#["x", "yy"].map String.length} nested {#[#[1], #[2, 3]].map Array.size}"
  IO.println s!"structs {repr ps} {ps.map (·.x)} {repr (ps.push { x := 3, name := "c" })}"
  IO.println s!"floats {#[1.5, 2.5].map (· * 2.0)} bools {#[true, false].map not} chars {#['a', 'b'].map Char.toUpper} units {#[(), ()].size}"
  -- in-place updates of a unique array in a loop
  let mut b := Array.replicate 1000 0
  for i in [0:100000] do
    b := b.modify (i % 1000) (· + i)
  IO.println s!"modify {b.foldl (· + ·) 0} {b[999]!}"
  let m : Std.HashMap String Nat := (List.range 300).foldl (fun m i => m.insert s!"key{i}" (i * i)) {}
  IO.println s!"hashmap filter {(m.filter fun _ v => v % 7 == 0).size} {(m.filter fun _ v => v % 7 == 0).toList.take 5}"
