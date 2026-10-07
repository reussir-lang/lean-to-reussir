/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `D71TesterT08`: B2 (i): one type reaches the open position: native (no
  UBox expected)
- `D71TesterT09`: A dead variant (String only unboxed at, never boxed)
- `D71TesterT10`: Unit / placeholder: a family position holding PUnit in one
  instance and Nat in the other
- `D71TesterT11`: B4 rebuild under a by-value constructor: a rigid Nat ×
  String result stored where (Box × String) is typed
- `D71TesterT12`: B7 List conversion: a rigid List Nat stored where List Box
  is typed, read back at List Nat
- `D71TesterT14`: B7 conversion memo: a tree with shared nodes (node t t)
  and an assoc list, converted across Box
- `D71TesterT16`: B7 mapped Task conversion
- `D71TesterT17`: B2 (iii)/B7: a closed term hoisted from generic code, read
  at List (Option α) in generic code at three types
- `D71TesterT18`: A shared reference to a generic declaration / partial
  application read per use at two types
- `D71TesterT19`: B4 wrapper under an arrow: an existential holding a
  function over its own type
- `D71TesterT20`: A cast into a fieldless one-constructor type (castUnit) -/

namespace D71TesterT08
structure Pkg where
  b : Bool
  v : if b then Nat else String
@[noinline] def rd : Pkg → Nat
  | ⟨true, v⟩ => let w : Nat := v; w + 1
  | ⟨false, _⟩ => 0
@[noinline] def mkN (n : Nat) : Pkg := ⟨true, (n : Nat)⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 7
  IO.println s!"{rd (mkN n)} {rd (mkN (n+5))}"
end D71TesterT08

namespace D71TesterT09
structure Pkg where
  b : Bool
  v : if b then Nat else String
@[noinline] def rd2 : Pkg → String
  | ⟨false, v⟩ => let s : String := v; s ++ "!"
  | ⟨true, v⟩ => let n : Nat := v; toString (n + 1)
@[noinline] def mkN (n : Nat) : Pkg := ⟨true, (n : Nat)⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 7
  IO.println s!"{rd2 (mkN n)} {rd2 (mkN 0)}"
end D71TesterT09

namespace D71TesterT10
def F : Bool → Type
  | true => Nat
  | false => Unit
def get : (b : Bool) → Nat → F b
  | true, n => n + 3
  | false, _ => ()
def showU (u : Unit) : String := match u with | () => "unit"
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 7
  let a : Nat := get true n
  let u : Unit := get false n
  IO.println s!"{a} {showU u}"
end D71TesterT10

namespace D71TesterT11
structure Pkg where
  b : Bool
  v : if b then Nat × String else Bool × String
@[noinline] def mkp (n : Nat) : Nat × String := (n * 3, s!"n{n}")
@[noinline] def mkq (n : Nat) : Bool × String := (n % 2 == 0, s!"q{n}")
@[noinline] def mkN (n : Nat) : Pkg := ⟨true, mkp n⟩
@[noinline] def mkB (n : Nat) : Pkg := ⟨false, mkq n⟩
@[noinline] def useP (p : Nat × String) : String := s!"{p.1 + 1}/{p.2}"
@[noinline] def rd : Pkg → String
  | ⟨true, v⟩ => useP v
  | ⟨false, v⟩ => let w : Bool × String := v; s!"{!w.1}/{w.2.length}"
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 7
  IO.println s!"{[mkN n, mkB n, mkN 0, mkB (n+1)].map rd}"
end D71TesterT11

namespace D71TesterT12
structure Pkg where
  b : Bool
  v : if b then List Nat else List String
@[noinline] def mkL (n : Nat) : List Nat := List.range n
@[noinline] def mkSL (n : Nat) : List String := (List.range n).map (s!"s{·}")
@[noinline] def mkN (n : Nat) : Pkg := ⟨true, mkL n⟩
@[noinline] def mkS (n : Nat) : Pkg := ⟨false, mkSL n⟩
@[noinline] def sumL (xs : List Nat) : Nat := xs.foldl (· + ·) 0
@[noinline] def rd : Pkg → String
  | ⟨true, v⟩ => toString (sumL v)
  | ⟨false, v⟩ => let w : List String := v; String.intercalate "," w
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let ps := [mkN n, mkS n, mkN 0, mkS 0, mkN 1]
  IO.println s!"{ps.map rd}"
  -- complexity: a long list converted once per crossing
  IO.println s!"{rd (mkN (n * 50000))}"
end D71TesterT12

namespace D71TesterT14
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
inductive AL (α β : Type) where
  | nil : AL α β
  | cons : α → β → AL α β → AL α β
structure Pkg where
  b : Bool
  v : if b then Tree Nat × AL Nat String else Tree String × AL String Nat
@[noinline] def share {α : Type} (x : α) : Nat → Tree α
  | 0 => .leaf x
  | k+1 => let t := share x k; .node t t
@[noinline] def mkAL (n : Nat) : AL Nat String := (List.range n).foldl (fun a i => .cons i s!"v{i}" a) .nil
@[noinline] def mkAL2 (n : Nat) : AL String Nat := (List.range n).foldl (fun a i => .cons s!"k{i}" i a) .nil
@[noinline] def mkN (n d : Nat) : Pkg := ⟨true, (share n d, mkAL n)⟩
@[noinline] def mkS (n d : Nat) : Pkg := ⟨false, (share s!"x{n}" d, mkAL2 n)⟩
@[noinline] def leftmost {α : Type} : Tree α → α
  | .leaf x => x
  | .node l _ => leftmost l
@[noinline] def depth {α : Type} : Tree α → Nat
  | .leaf _ => 0
  | .node l _ => 1 + depth l
@[noinline] def alLen {α β : Type} : AL α β → Nat
  | .nil => 0
  | .cons _ _ t => 1 + alLen t
@[noinline] def alFirst : AL Nat String → String
  | .nil => "-"
  | .cons k v _ => s!"{k}={v}"
@[noinline] def rd : Pkg → String
  | ⟨true, v⟩ => let w : Tree Nat × AL Nat String := v; s!"{leftmost w.1 + 1} d{depth w.1} {alLen w.2} {alFirst w.2}"
  | ⟨false, v⟩ => let w : Tree String × AL String Nat := v; s!"{leftmost w.1} d{depth w.1} {alLen w.2}"
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let d := (args.tail.head? >>= String.toNat?).getD 4
  IO.println s!"{[mkN n d, mkS n d, mkN 0 0, mkS 0 0].map rd}"
end D71TesterT14

namespace D71TesterT16
structure Pkg where
  b : Bool
  v : if b then Task (List Nat) else Task (List String)
@[noinline] def mkT (n : Nat) : Task (List Nat) := Task.spawn fun _ => List.range n
@[noinline] def mkTS (n : Nat) : Task (List String) := Task.spawn fun _ => (List.range n).map toString
@[noinline] def mkN (n : Nat) : Pkg := ⟨true, mkT n⟩
@[noinline] def mkS (n : Nat) : Pkg := ⟨false, mkTS n⟩
@[noinline] def rd : Pkg → String
  | ⟨true, v⟩ => let w : Task (List Nat) := v; toString (w.get.foldl (· + ·) 0)
  | ⟨false, v⟩ => let w : Task (List String) := v; String.intercalate "," w.get
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  IO.println s!"{[mkN n, mkS n, mkN 0].map rd}"
end D71TesterT16

namespace D71TesterT17
@[noinline] def showAll {α : Type} [ToString α] (x : α) : String :=
  let xs : List (Option α) := [none, none] ++ [some x]
  toString (xs.map fun o => match o with | some v => toString v | none => "_")
@[noinline] def showArr {α : Type} [ToString α] (x : α) : String :=
  let xs : Array (List α) := #[[], []]
  toString ((xs.push [x, x]).map (·.length))
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  IO.println s!"{showAll n} {showAll s!"s{n}"} {showAll (n == 4)} {showArr n} {showArr "a"}"
end D71TesterT17

namespace D71TesterT18
@[noinline] def ap {α β : Type} (f : List α → β) (x : List α) : β := f x
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let a := ap List.head? (List.range n)
  let b := ap List.head? (args ++ ["z"])
  let c := ap (List.take 2) (List.range n)
  let d := ap (List.take 2) (args ++ ["y", "w"])
  let e := ap List.length (List.range n) + ap List.length args
  IO.println s!"{a} {b} {c} {d} {e}"
end D71TesterT18

namespace D71TesterT19
structure AnyF where
  {α : Type}
  f : α → String
  x : α
@[noinline] def showNat (n : Nat) : String := s!"N{n}"
@[noinline] def AnyF.run (s : AnyF) : String := s.f s.x
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let pre := s!"p{n}:"
  let xs : List AnyF := [⟨showNat, n⟩, ⟨fun (s : String) => pre ++ s, "abc"⟩, ⟨fun (b : Bool) => if b then pre else "no", n > 2⟩,
    ⟨fun (p : Nat × Nat) => s!"{p.1 + p.2}", (n, n)⟩, ⟨fun s => String.append pre s, "q"⟩]
  IO.println (xs.map (·.run))
end D71TesterT19

namespace D71TesterT20
structure Tok where
  mk ::
unsafe def toTok (n : Nat) : Tok := unsafeCast n
@[implemented_by toTok, noinline] def toTokS (_ : Nat) : Tok := ⟨⟩
@[noinline] def showTok (t : Tok) : String := match t with | .mk => "tok"
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  IO.println s!"{showTok (toTokS n)} {n}"
end D71TesterT20

def main : IO Unit := do
  IO.println "-- D71TesterT08"
  D71TesterT08.caseMain ["1"]
  IO.println "-- D71TesterT09"
  D71TesterT09.caseMain ["0"]
  IO.println "-- D71TesterT10"
  D71TesterT10.caseMain ["2"]
  IO.println "-- D71TesterT11"
  D71TesterT11.caseMain ["0"]
  IO.println "-- D71TesterT12"
  D71TesterT12.caseMain ["2"]
  IO.println "-- D71TesterT14"
  D71TesterT14.caseMain ["3", "20"]
  IO.println "-- D71TesterT16"
  D71TesterT16.caseMain ["2"]
  IO.println "-- D71TesterT17"
  D71TesterT17.caseMain ["4"]
  IO.println "-- D71TesterT18"
  D71TesterT18.caseMain ["a", "b"]
  IO.println "-- D71TesterT19"
  D71TesterT19.caseMain ["3"]
  IO.println "-- D71TesterT20"
  D71TesterT20.caseMain ["0"]
