/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `D71TesterT24L1`: A variant type of depth 2
- `D71TesterT24L2`: A variant type of depth 3
- `D71TesterT24L3`: A variant type of depth 4
- `D71TesterT24L6`: A variant type of depth 7
- `D71TesterT24M63`: B3 guard boundary: a variant type of depth 64
  (allowed), custom instance
- `D71TesterT24N16`: B3 guard boundary: a variant type of depth 64
  (allowed), custom instance
- `D71TesterT24N4`: B3 guard boundary: a variant type of depth 64 (allowed),
  custom instance
- `D71TesterT24N8`: B3 guard boundary: a variant type of depth 64 (allowed),
  custom instance
- `D71TesterT24O`: Control for T24N12: the depth-13 value without a Box
  position
- `D71TesterT25`: Rank-2 handler at two types (FreeM fold with a polymorphic
  handler)
- `D71TesterT26`: B7 values with identity: IO.Ref reached through Box,
  written via an alias and read via the family -/

namespace D71TesterT24L1
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let d : List (Nat) := [n]
  let xs : List AnyS := [⟨d⟩, ⟨n⟩]
  IO.println ((xs.map (·.show)).map (·.length))
end D71TesterT24L1

namespace D71TesterT24L2
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let d : List (List (Nat)) := [[n]]
  let xs : List AnyS := [⟨d⟩, ⟨n⟩]
  IO.println ((xs.map (·.show)).map (·.length))
end D71TesterT24L2

namespace D71TesterT24L3
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let d : List (List (List (Nat))) := [[[n]]]
  let xs : List AnyS := [⟨d⟩, ⟨n⟩]
  IO.println ((xs.map (·.show)).map (·.length))
end D71TesterT24L3

namespace D71TesterT24L6
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let d : List (List (List (List (List (List (Nat)))))) := [[[[[[n]]]]]]
  let xs : List AnyS := [⟨d⟩, ⟨n⟩]
  IO.println ((xs.map (·.show)).map (·.length))
end D71TesterT24L6

namespace D71TesterT24M63
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
abbrev Deep := List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (Nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
instance : ToString Deep := ⟨fun x => s!"deep{x.length}"⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let d : Deep := [[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
  let xs : List AnyS := [⟨d⟩, ⟨n⟩]
  IO.println (xs.map (·.show))
end D71TesterT24M63

namespace D71TesterT24N16
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
abbrev Deep := List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (Nat))))))))))))))))
instance : ToString Deep := ⟨fun x => s!"deep{x.length}"⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let d : Deep := [[[[[[[[[[[[[[[[n]]]]]]]]]]]]]]]]
  let xs : List AnyS := [⟨d⟩, ⟨n⟩]
  IO.println (xs.map (·.show))
end D71TesterT24N16

namespace D71TesterT24N4
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
abbrev Deep := List (List (List (List (Nat))))
instance : ToString Deep := ⟨fun x => s!"deep{x.length}"⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let d : Deep := [[[[n]]]]
  let xs : List AnyS := [⟨d⟩, ⟨n⟩]
  IO.println (xs.map (·.show))
end D71TesterT24N4

namespace D71TesterT24N8
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
abbrev Deep := List (List (List (List (List (List (List (List (Nat))))))))
instance : ToString Deep := ⟨fun x => s!"deep{x.length}"⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let d : Deep := [[[[[[[[n]]]]]]]]
  let xs : List AnyS := [⟨d⟩, ⟨n⟩]
  IO.println (xs.map (·.show))
end D71TesterT24N8

namespace D71TesterT24O
abbrev Deep := List (List (List (List (List (List (List (List (List (List (List (List (Nat))))))))))))
instance : ToString Deep := ⟨fun x => s!"deep{x.length}"⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let d : Deep := [[[[[[[[[[[[n]]]]]]]]]]]]
  IO.println [toString d, toString n]
end D71TesterT24O

namespace D71TesterT25
inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
inductive Op : Type → Type where
  | getN : Op Nat
  | getS : Op String
  | tick : Op Unit
@[noinline] def foldF {F : Type → Type} {α β : Type} (pc : α → β) (h : {ι : Type} → F ι → (ι → β) → β) : FreeM F α → β
  | .pure a => pc a
  | .liftBind op k => h op (fun x => foldF pc h (k x))
@[noinline] def hNat (n : Nat) : {ι : Type} → Op ι → (ι → Nat) → Nat
  | _, .getN, k => k n
  | _, .getS, k => k s!"s{n}"
  | _, .tick, k => 1 + k ()
@[noinline] def hStr (n : Nat) : {ι : Type} → Op ι → (ι → String) → String
  | _, .getN, k => "N" ++ k (n * 2)
  | _, .getS, k => "S" ++ k "q"
  | _, .tick, k => "T" ++ k ()
@[noinline] def prog (m : Nat) : FreeM Op Nat :=
  .liftBind .getN fun a => .liftBind .tick fun _ => .liftBind .getS fun s => .pure (a * m + s.length)
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{foldF id (hNat n) (prog 10)} {foldF toString (hStr n) (prog 2)}"
end D71TesterT25

namespace D71TesterT26
structure RP where
  b : Bool
  r : IO.Ref (if b then Nat else String)
@[noinline] def bump (p : RP) : IO Unit := match p with
  | ⟨true, r⟩ => r.modify (fun (x : Nat) => x + 1)
  | ⟨false, r⟩ => r.modify (fun (x : String) => x ++ "!")
@[noinline] def showRP (p : RP) : IO String := match p with
  | ⟨true, r⟩ => do let x : Nat := (← r.get); return toString x
  | ⟨false, r⟩ => do let x : String := (← r.get); return x
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let rn ← IO.mkRef n
  let rs ← IO.mkRef s!"a{n}"
  let ps : List RP := [⟨true, rn⟩, ⟨false, rs⟩, ⟨true, rn⟩]
  for p in ps do bump p
  rn.modify (· * 10)
  rs.set "reset"
  for p in ps do bump p
  for p in ps do IO.println (← showRP p)
  IO.println s!"{← rn.get} {← rs.get}"
end D71TesterT26

def main : IO Unit := do
  IO.println "-- D71TesterT24L1"
  D71TesterT24L1.caseMain ["3"]
  IO.println "-- D71TesterT24L2"
  D71TesterT24L2.caseMain []
  IO.println "-- D71TesterT24L3"
  D71TesterT24L3.caseMain []
  IO.println "-- D71TesterT24L6"
  D71TesterT24L6.caseMain []
  IO.println "-- D71TesterT24M63"
  D71TesterT24M63.caseMain ["3"]
  IO.println "-- D71TesterT24N16"
  D71TesterT24N16.caseMain ["3"]
  IO.println "-- D71TesterT24N4"
  D71TesterT24N4.caseMain ["3"]
  IO.println "-- D71TesterT24N8"
  D71TesterT24N8.caseMain ["3"]
  IO.println "-- D71TesterT24O"
  D71TesterT24O.caseMain []
  IO.println "-- D71TesterT25"
  D71TesterT25.caseMain ["5"]
  IO.println "-- D71TesterT26"
  D71TesterT26.caseMain ["2"]
