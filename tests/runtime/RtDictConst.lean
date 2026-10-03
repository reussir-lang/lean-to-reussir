/-! Runtime test: an instance constant whose value is computed (round 7
RV7F-02). Natively the constant is evaluated once, at startup, and a generic
function that receives it at run time reads its field (Lean does not
specialize `getOr` on an `Inhabited` dictionary: the class is
`weak_specialize`). Stage 1 specialized `getOr` on the dictionary, and
`simp` copied the constant's body (`mkGrid 3`) into the instance, where it
ran at every call: a trace per call, and a cost per call of the constant's
computation (unbounded: 4.3 s for 0.00 s natively with a larger grid). A
constant that computes something is therefore not part of a static
dictionary, also inside one built from it (`Inhabited (Grid × Nat)`); a
constant that is a mere value still is (`Inhabited Nat`). -/

structure Grid where
  cells : Array Nat
  width : Nat

@[noinline] def mkGrid (n : Nat) : Grid :=
  dbgTrace s!"mkGrid {n}" fun _ => ⟨(Array.range (n * n)).map (· % 7), n⟩

instance : Inhabited Grid := ⟨mkGrid 3⟩

@[noinline] def getOr [Inhabited α] (xs : Array α) (i : Nat) : α := xs.getD i default

def main : IO Unit := do
  let gs : Array Grid := #[mkGrid 1, mkGrid 2]
  let mut acc := 0
  for i in [0:6] do
    let g := getOr gs (i % 4)
    acc := acc + g.width + g.cells.size
  IO.println s!"grids {acc}"
  let ps : Array (Grid × Nat) := #[(mkGrid 1, 5)]
  let mut acc2 := 0
  for i in [0:4] do
    let p := getOr ps i
    acc2 := acc2 + p.1.width + p.2
  IO.println s!"pairs {acc2}"
  let ns : Array Nat := #[4, 5]
  let mut acc3 := 0
  for i in [0:4] do
    acc3 := acc3 + getOr ns i
  IO.println s!"nats {acc3}"
