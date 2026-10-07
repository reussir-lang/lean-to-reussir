/-! Runtime test: existential packages (a value with its own `ToString`)
at every pair of five types (`Nat`, `Bool`, `Unit`, `Float`, `List Nat`:
25 pair types, each printed through its package), from the translation
scaling cases of the shared dependent-type corpus: A1094 (pairs of 12
types, with the unit value as a leaf and `List`'s printer), D71TesterT24F
(8 types), D71TesterT24H (17) and D71TesterT24E (33). The output is the
total length of the printouts. Dev's lean2rr gives each pair type its own
layout and instances: building the 8-type case takes 4.5 GB, and the
builds of the 12-, 17- and 33-type cases are killed at 12 GB; those cases
stay in the shared corpus, and this one keeps five types so that its build
stays small. Argument: N (default 4). -/
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α

@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let xs : List AnyS := [
    ⟨((n : Nat), (n : Nat))⟩,
    ⟨((n : Nat), (n>2 : Bool))⟩,
    ⟨((n : Nat), (() : Unit))⟩,
    ⟨((n : Nat), (n.toFloat : Float))⟩,
    ⟨((n : Nat), ([n] : List Nat))⟩,
    ⟨((n>2 : Bool), (n : Nat))⟩,
    ⟨((n>2 : Bool), (n>2 : Bool))⟩,
    ⟨((n>2 : Bool), (() : Unit))⟩,
    ⟨((n>2 : Bool), (n.toFloat : Float))⟩,
    ⟨((n>2 : Bool), ([n] : List Nat))⟩,
    ⟨((() : Unit), (n : Nat))⟩,
    ⟨((() : Unit), (n>2 : Bool))⟩,
    ⟨((() : Unit), (() : Unit))⟩,
    ⟨((() : Unit), (n.toFloat : Float))⟩,
    ⟨((() : Unit), ([n] : List Nat))⟩,
    ⟨((n.toFloat : Float), (n : Nat))⟩,
    ⟨((n.toFloat : Float), (n>2 : Bool))⟩,
    ⟨((n.toFloat : Float), (() : Unit))⟩,
    ⟨((n.toFloat : Float), (n.toFloat : Float))⟩,
    ⟨((n.toFloat : Float), ([n] : List Nat))⟩,
    ⟨(([n] : List Nat), (n : Nat))⟩,
    ⟨(([n] : List Nat), (n>2 : Bool))⟩,
    ⟨(([n] : List Nat), (() : Unit))⟩,
    ⟨(([n] : List Nat), (n.toFloat : Float))⟩,
    ⟨(([n] : List Nat), ([n] : List Nat))⟩]
  IO.println ((xs.map (·.show)).foldl (fun a s => a + s.length) 0)
  IO.println ((xs.map (·.show)).take 7)
