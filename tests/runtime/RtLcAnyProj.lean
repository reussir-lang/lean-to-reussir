/-! Runtime test: projections out of values whose type Stage 3 sees as
`lcAny`. FDepA: a record family indexed by a tag (`Shape.Data : Shape → Type`)
with a getter whose every branch is `d.1` (finding RV7F-01: the `cases` gets
the constructor's parameter types as field types). DZip3/DPhantom2:
`Array.map` with a field projection of a parametric structure (`Pair α β`,
`Nat × Nat × Nat`, Sigma, `R α`, zip/zipIdx then `(·.1)`/`(·.2)`; finding
RV7D-01: the split map loop stores placeholders or panics).
From the round-7 review, areas F (rv7/frontend, RV7F-01 repro FDepA) and D
(rv7/rtdata, RV7D-01 repros DZip3 and DPhantom2). -/

namespace FDepA
-- from rv7/frontend/FDepA.lean
-- A family of record types indexed by a tag, with a getter whose result type
-- depends on the tag too: every branch returns a projection.
inductive Shape where
  | circle | rect

def Shape.Dim : Shape → Type
  | .circle => Float
  | .rect => Float × Float

def Shape.Data : Shape → Type
  | .circle => Float × String
  | .rect => (Float × Float) × String

@[noinline] def Shape.mk : (s : Shape) → s.Data
  | .circle => (1.5, "c")
  | .rect => ((2.0, 3.0), "r")

@[noinline] def Shape.dim : (s : Shape) → s.Data → s.Dim
  | .circle, d => d.1
  | .rect, d => d.1

def main : IO Unit := do
  let r : Float := Shape.dim .circle (Shape.mk .circle)
  let wh : Float × Float := Shape.dim .rect (Shape.mk .rect)
  IO.println s!"circle radius: {r}"
  IO.println s!"rect: {wh.1} x {wh.2}"
end FDepA

namespace DZip3
-- from rv7/rtdata/DZip3.lean
structure Pair (α β : Type) where
  a : α
  b : β

@[noinline] def mkP (k : Nat) : Array (Pair Nat String) := #[⟨k, "x"⟩, ⟨k + 1, "y"⟩]
@[noinline] def mkO (k : Nat) : Array (Option Nat) := #[some k, none, some (k + 1)]
@[noinline] def mkT (k : Nat) : Array (Nat × Nat × Nat) := #[(k, k + 1, k + 2)]
@[noinline] def mkS (k : Nat) : Array (Σ _ : Nat, Nat) := #[⟨k, k + 1⟩]
@[noinline] def mkPairs (k : Nat) : Array (Nat × Nat) := #[(k, k + 1), (k + 2, k + 3)]
@[noinline] def mkL (k : Nat) : Array (List Nat) := #[[k], [k + 1, 2]]

def main : IO Unit := do
  IO.println s!"Pair.a {(mkP 3).map (·.a)} Pair.b {(mkP 3).map Pair.b}"
  IO.println s!"Option match {(mkO 3).map (fun o => match o with | some v => v | none => 0)} getD {(mkO 3).map (·.getD 7)}"
  IO.println s!"triple {(mkT 3).map (·.2.1)} {(mkT 3).map (·.2)}"
  IO.println s!"sigma {(mkS 3).map (·.2)} {(mkS 3).map (·.1)}"
  IO.println s!"pat {(mkPairs 3).map (fun (a, _) => a)} fst {(mkPairs 3).map Prod.fst} swap {(mkPairs 3).map (fun p => (p.2, p.1))}"
  IO.println s!"head {(mkL 3).map (·.headD 0)}"
  let xs := #[1, 2, 3]
  let ys := #["a", "b", "c"]
  IO.println s!"zip {(xs.zip ys).map (·.2)} {(xs.zip ys).map (·.1)} unzip {(xs.zip ys).unzip.1} {(xs.zip ys).unzip.2}"
  IO.println s!"zipIdx {(ys.zipIdx).map (·.2)} {(ys.zipIdx).map (·.1)}"
end DZip3

namespace DPhantom2
-- from rv7/rtdata/DPhantom2.lean
structure R (α : Type) where
  s : String
  y : α

@[noinline] def rs (k : Nat) : Array (R Nat) := #[⟨"a", k⟩, ⟨"bb", k + 1⟩]

def main : IO Unit := do
  IO.println s!"R.y {(rs 3).map (·.y)}"
  IO.println s!"R.s {(rs 3).map (·.s)}"
end DPhantom2

def main : IO Unit := do
  IO.println "=== FDepA"
  FDepA.main
  IO.println "=== DZip3"
  DZip3.main
  IO.println "=== DPhantom2"
  DPhantom2.main
