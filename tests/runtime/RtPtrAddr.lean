/-! Runtime test: `ptrAddrUnsafe`-based shortcuts (`Array.mapMono`, which
keeps an element when the function returns the same object) give the same
results as natively: equal addresses must never be answered for unequal
values (here: small `Nat`s, which are unboxed values). -/

def mono (xs : Array Nat) : Array Nat := xs.mapMono fun x => if x % 3 == 0 then x else x + 1
def monoS (xs : Array String) : Array String := (xs.map id).mapMono fun x => if x.length > 1 then x else x ++ x
def monoL (xs : List Nat) : List Nat := xs.mapMono fun x => if x < 4 then x else x * 10

def main (args : List String) : IO Unit := do
  let k := args.length
  let xs := (List.range (12 + k)).toArray
  IO.println s!"{mono xs}"
  IO.println s!"{monoS #["a", "bb", "c", "dd", "", "eee"]}"
  IO.println s!"{monoL (List.range (8 + k))}"
  IO.println s!"{mono #[2 ^ 70, 2 ^ 70 + 1, 3 * 2 ^ 70]}"
