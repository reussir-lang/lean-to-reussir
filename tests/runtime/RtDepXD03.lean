import Std.Data.HashMap
/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `D71Breaker3R01`: The always-filled pruning: shared closed values of
  Prod/structure types read at two instantiations.
- `D71Breaker3R02`: The PUnit/Unit split: () inside families, existentials
  over Unit and PUnit, Option Unit, List Unit.
- `D71Breaker3R03`: Forwarders (reordered, dropped, added arguments) and
  partial applications carrying coercions.
- `D71Breaker3R04`: Closed constants of recursive types with shared
  subtrees, cloned and rebuilt in a Box-mode program.
- `D71Breaker3R05`: _redArg-style forwarders: unused type-class and value
  params over Box classes
- `D71Breaker3R06`: Always-filled pruning, harder: nested pairs,
  Option/Sum/Except around pairs, user inductives storing α in every
  constructor, proof fields, reads in generic code.
- `D71Breaker3R07`: PUnit/Unit harder: Unit at always-filled positions of
  shared values, Unit-domain functions and IO actions in families.
- `D71Breaker3R08`: Forwarder chains over Box parameters: reorder, drop (the
  Box argument itself), add
- `D71Breaker3R09`: Statics with shared nodes converted at two
  instantiations
- `D71Breaker3R11`: Partial applications whose remaining domain is a Box
  class, stored in family-typed fields and lists.
- `D71Breaker3R12`: Unit-carrying containers at family positions with
  modify/set!/pop (box(0) placeholder idioms), Option Unit cells. -/

namespace D71Breaker3R01
/- R01: the always-filled pruning: shared closed values of Prod/structure types read at two instantiations. -/
structure Cell (α : Type) where
  val : α
  k : Nat
structure PCell (α : Type) where
  val : α
  k : Nat
  ok : k ≥ 0
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
@[noinline] def Vec.toList : Vec α n → List α
  | .nil => [] | .cons a v => a :: v.toList

def eCell : Cell (List α) := ⟨[], 7⟩
def eOpt : Cell (Option α) := ⟨none, 8⟩
def ePair : Cell (List α × Option β) := ⟨([], none), 9⟩
def eFn : Cell (α → α) := ⟨fun x => x, 10⟩
def ePC : PCell (List α) := ⟨[], 11, Nat.zero_le _⟩
def eSomePair : Option (List α × Nat) := some ([], 12)
def eVec : Cell ((n : Nat) × Vec α n) := ⟨⟨0, .nil⟩, 13⟩
def eNested : Cell (Cell (List α)) := ⟨⟨[], 1⟩, 14⟩
def eThunk : Cell (Thunk (List α)) := ⟨Thunk.pure [], 15⟩
def eArr : Cell (Array α × Nat) := ⟨(#[], 0), 16⟩

@[noinline] def fill (c : Cell (List α)) (x : α) : Cell (List α) := { c with val := x :: c.val }
@[noinline] def fillO (c : Cell (Option α)) (x : α) : Cell (Option α) := { c with val := some x }
@[noinline] def fillP (c : Cell (List α × Option β)) (x : α) (y : β) : Cell (List α × Option β) := { c with val := (x :: c.val.1, some y) }
@[noinline] def apF (c : Cell (α → α)) (x : α) : α × Nat := (c.val x, c.k)
@[noinline] def fillPC (c : PCell (List α)) (x : α) : PCell (List α) := { c with val := x :: c.val }
@[noinline] def fillSP (o : Option (List α × Nat)) (x : α) : Option (List α × Nat) := o.map (fun (xs, k) => (x :: xs, k + 1))
@[noinline] def push (c : Cell ((n : Nat) × Vec α n)) (x : α) : Cell ((n : Nat) × Vec α n) := { c with val := ⟨c.val.1 + 1, .cons x c.val.2⟩ }
@[noinline] def fillN (c : Cell (Cell (List α))) (x : α) : Cell (Cell (List α)) := { c with val := { c.val with val := x :: c.val.val } }
@[noinline] def fillT (c : Cell (Thunk (List α))) (x : α) : Cell (Thunk (List α)) := { c with val := Thunk.mk (fun _ => x :: c.val.get) }
@[noinline] def fillA (c : Cell (Array α × Nat)) (x : α) : Cell (Array α × Nat) := { c with val := (c.val.1.push x, c.val.2 + 1) }

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let s := toString n
  IO.println s!"{(fill eCell n).val} {(fill eCell s).val} {(eCell : Cell (List Nat)).k + (eCell : Cell (List String)).k}"
  IO.println s!"{(fillO eOpt n).val} {(fillO eOpt s).val} {(eOpt : Cell (Option Nat)).val} {(eOpt : Cell (Option String)).val}"
  IO.println s!"{(fillP ePair n s).val} {(fillP ePair s n).val} {(ePair : Cell (List Nat × Option String)).val} {(ePair : Cell (List String × Option Nat)).val}"
  IO.println s!"{apF eFn n} {apF eFn s}"
  IO.println s!"{(fillPC ePC n).val} {(fillPC ePC s).val} {(ePC : PCell (List Nat)).k}"
  IO.println s!"{fillSP eSomePair n} {fillSP eSomePair s} {(eSomePair : Option (List Nat × Nat))} {(eSomePair : Option (List String × Nat))}"
  IO.println s!"{(push (push eVec n) (n+1)).val.2.toList} {(push eVec s).val.2.toList} {(eVec : Cell ((n : Nat) × Vec Nat n)).val.1}"
  IO.println s!"{(fillN eNested n).val.val} {(fillN eNested s).val.val} {(eNested : Cell (Cell (List Nat))).val.k}"
  IO.println s!"{(fillT eThunk n).val.get} {(fillT eThunk s).val.get} {(eThunk : Cell (Thunk (List Nat))).val.get}"
  IO.println s!"{(fillA eArr n).val} {(fillA eArr s).val} {(eArr : Cell (Array String × Nat)).val}"
end D71Breaker3R01

namespace D71Breaker3R02
/- R02: the PUnit/Unit split: () inside families, existentials over Unit and PUnit, Option Unit, List Unit. -/
structure P where
  b : Bool
  v : if b then Unit else Nat
structure Q where
  b : Bool
  v : if b then List Unit else String
structure R where
  b : Bool
  v : if b then Option Unit else Option Nat
structure Any where
  {α : Type}
  val : α
  sh : α → String
@[noinline] def mkP (n : Nat) : P := if n % 2 = 0 then ⟨true, ()⟩ else ⟨false, n⟩
@[noinline] def rdP : P → Nat
  | ⟨true, v⟩ => let u : Unit := v; let _ := u; 1000
  | ⟨false, v⟩ => let k : Nat := v; k
@[noinline] def mkQ (n : Nat) : Q := if n % 2 = 0 then ⟨true, List.replicate n ()⟩ else ⟨false, s!"q{n}"⟩
@[noinline] def rdQ : Q → Nat
  | ⟨true, v⟩ => let us : List Unit := v; us.length
  | ⟨false, v⟩ => let s : String := v; s.length + 100
@[noinline] def mkR (n : Nat) : R := if n % 2 = 0 then ⟨true, if n % 4 = 0 then some () else none⟩ else ⟨false, if n % 3 = 0 then some n else none⟩
@[noinline] def rdR : R → Nat
  | ⟨true, v⟩ => let o : Option Unit := v; if o.isSome then 1 else 2
  | ⟨false, v⟩ => let o : Option Nat := v; o.getD 0 + 10
@[noinline] def mkAny (n : Nat) : Any := match n % 4 with
  | 0 => { α := Unit, val := (), sh := fun _ => "unit" }
  | 1 => { α := PUnit, val := PUnit.unit, sh := fun _ => "punit" }
  | 2 => { α := Nat, val := n, sh := toString }
  | _ => { α := Option Unit, val := some (), sh := fun o => toString o.isSome }
@[noinline] def rdAny (a : Any) : String := a.sh a.val
@[noinline] def unitList (n : Nat) : List P := (List.range n).map mkP
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let xs := List.range (n + 4)
  IO.println (xs.map (fun i => rdP (mkP i)))
  IO.println (xs.map (fun i => rdQ (mkQ i)))
  IO.println (xs.map (fun i => rdR (mkR i)))
  IO.println (xs.map (fun i => rdAny (mkAny i)))
  IO.println ((unitList (n + 2)).map rdP)
  let arr := (unitList (n + 2)).toArray
  IO.println ((arr.modify 0 (fun _ => ⟨false, (42 : Nat)⟩)).map rdP)
end D71Breaker3R02

namespace D71Breaker3R03
/- R03: forwarders (reordered, dropped, added arguments) and partial applications carrying coercions. -/
structure Pkg where
  b : Bool
  v : if b then Nat else String
@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
@[noinline] def rd : Pkg → Nat
  | ⟨true, v⟩ => let w : Nat := v; w + 1
  | ⟨false, v⟩ => let s : String := v; s.length
@[noinline] def mkL (d : Bool) (n : Nat) : List (if d then Nat else String) :=
  match d with
  | true => (List.range n : List Nat)
  | false => ((List.range n).map toString : List String)
@[noinline] def rdL (d : Bool) (xs : List (if d then Nat else String)) : Nat :=
  if h : d = true then (cast (by simp [h]) xs : List Nat).foldl (· + ·) 0
  else (cast (by simp [h]) xs : List String).foldl (fun a s => a + s.length) 0
-- forwarders
def fwdA (k : Nat) (p : Pkg) : Nat := rd p + k                      -- added arg
def fwdB (p : Pkg) (_unused : String) : Nat := rd p                 -- dropped arg
def fwdC (xs : List (if d then Nat else String)) (d' : Bool) (h : d' = d) : Nat := rdL d (h ▸ xs)   -- reordered
def fwdD (k : Nat) (d : Bool) (xs : List (if d then Nat else String)) : Nat := rdL d xs * k
def fwdE (d : Bool) (n : Nat) : List (if d then Nat else String) := mkL d n
def fwdF (n : Nat) (d : Bool) : List (if d then Nat else String) := fwdE d n
@[noinline] def ap (f : α → β) (x : α) : β := f x
@[noinline] def ap2 (f : α → β → γ) (x : α) (y : β) : γ := f x y
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ps := (List.range (n + 2)).map mk
  IO.println s!"{ps.map (fwdA n)} {ps.map (fwdB · "z")} {ps.map (ap (fwdA 1))} {ps.map (ap2 fwdA 2)}"
  for d in [true, false] do
    let xs := fwdF n d
    IO.println s!"{fwdC xs d rfl} {fwdD 2 d xs} {ap (fwdD 3 d) xs} {ap2 (fun k (ys : List (if d then Nat else String)) => fwdD k d ys) 4 xs} {rdL d (fwdE d (n + 1))} {rdL d (fwdF n d)}"
    let g := fwdD n d
    let h := fwdD (n + 1) d
    IO.println s!"{g xs} {g (fwdE d 1)} {h xs} {(ps.map (fwdA n ·)).length}"
end D71Breaker3R03

namespace D71Breaker3R04
/- R04: closed constants of recursive types with shared subtrees, cloned and rebuilt in a Box-mode program. -/
structure Pkg where
  b : Bool
  v : if b then Nat else String
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
  | empty : Tree α
@[noinline] def Tree.sum (f : α → Nat) : Tree α → Nat
  | .leaf a => f a
  | .node l r => l.sum f + r.sum f
  | .empty => 0
@[noinline] def Tree.map (f : α → β) : Tree α → Tree β
  | .leaf a => .leaf (f a)
  | .node l r => .node (l.map f) (r.map f)
  | .empty => .empty
@[noinline] def Tree.size : Tree α → Nat
  | .leaf _ => 1 | .node l r => l.size + r.size | .empty => 0
@[noinline] def rd : Pkg → Nat
  | ⟨true, v⟩ => let w : Nat := v; w + 1
  | ⟨false, v⟩ => let s : String := v; s.length
def kTree : Tree Pkg := let t := Tree.node (.leaf ⟨true, (1 : Nat)⟩) (.leaf ⟨false, "ab"⟩); .node t (.node t t)
def kList : List Pkg := [⟨true, (5 : Nat)⟩, ⟨false, "xyz"⟩]
def kArr : Array (List Pkg) := #[kList, [], kList]
def kEmpty : Tree α := .empty
def kNatTree : Tree Nat := let t := Tree.node (.leaf 1) (.leaf 2); .node t t
structure Big where
  t : Tree Pkg
  l : List Pkg
  a : Array (List Pkg)
  th : Thunk (Tree Pkg)
def kBig : Big := ⟨kTree, kList, kArr, Thunk.pure kTree⟩
@[noinline] def mkPk (k : Nat) : Pkg := if k % 2 == 0 then ⟨true, k⟩ else ⟨false, toString k⟩
@[noinline] def grow (t : Tree Pkg) (n : Nat) : Tree Pkg := match n with
  | 0 => t
  | k + 1 => grow (.node t (.leaf (mkPk k))) k
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{kTree.sum rd} {kTree.size} {(grow kTree n).sum rd} {(grow kTree n).size} {kTree.sum rd}"
  IO.println s!"{(kTree.map rd).sum id} {kList.map rd} {(kArr.map (·.map rd))} {(kEmpty : Tree Pkg).size} {(kEmpty : Tree Nat).sum id}"
  IO.println s!"{kNatTree.sum id} {(kNatTree.map toString).sum String.length} {(grow kBig.t n).size} {kBig.l.map rd} {kBig.a.size} {kBig.th.get.sum rd}"
  let bs := List.replicate n kBig
  IO.println s!"{bs.foldl (fun a b => a + b.t.sum rd + (grow b.t 1).size) 0} {(bs.map (·.l.map rd))}"
  let t2 := kTree
  let t3 := grow t2 1
  IO.println s!"{t2.size} {t3.size} {kTree.size}"
end D71Breaker3R04

namespace D71Breaker3R05
/- R05: _redArg-style forwarders: unused type-class and value params over Box classes; partial applications of them. -/
structure Pkg where
  b : Bool
  v : if b then Nat else String
@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
@[noinline] def rd : Pkg → Nat
  | ⟨true, v⟩ => let w : Nat := v; w + 1
  | ⟨false, v⟩ => let s : String := v; s.length
def rdWith [ToString α] (_tag : α) (unused : Nat) (p : Pkg) : Nat := rd p
def rdWith2 (f : Pkg → Nat) (_k : Nat) (p : Pkg) (_q : Pkg) : Nat := f p
@[noinline] def loop (f : Pkg → Nat) (ps : List Pkg) : Nat := ps.foldl (fun a p => a + f p) 0
@[noinline] def mkMany (d : Bool) (n : Nat) : List Pkg := (List.range n).map (fun i => if d then ⟨true, (i : Nat)⟩ else ⟨false, (toString i : String)⟩)
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ps := (List.range (n + 2)).map mk
  IO.println s!"{loop (rdWith "t" 0) ps} {loop (rdWith n 1) ps} {loop (rdWith2 rd 2 · (mk 0)) ps} {loop (fun p => rdWith2 (rdWith 'c' 3) 4 p p) ps}"
  IO.println s!"{loop rd (mkMany true n)} {loop rd (mkMany false n)} {loop (rdWith 1.5 9) (mkMany (n % 2 == 0) n)}"
end D71Breaker3R05

namespace D71Breaker3R06
/- R06: always-filled pruning, harder: nested pairs, Option/Sum/Except around pairs, user inductives storing α in every constructor, proof fields, reads in generic code. -/
inductive Both (α β : Type) where
  | mk : α → β → Both α β
inductive Two (α : Type) where
  | l : α → Two α
  | r : α → Two α
structure Ix (α : Type) (n : Nat) where
  val : α
  i : Fin (n + 1)
  h : i.val ≤ n
def e3 : (List α × Nat) × (Option β × List γ) := (([], 1), (none, []))
def eOP : Option (List α × List β) := some ([], [])
def eSum : Sum (List α) (List β) × Nat := (.inl [], 2)
def eExc : Except String (List α × Nat) := .ok ([], 3)
def eBoth : Both (List α) (Option β) := .mk [] none
def eTwo : Two (List α) := .r []
def eIx : Ix (List α) 4 := ⟨[], ⟨2, by omega⟩, by decide⟩
def eDeep : List (List α × Nat) × Option (Option β) := ([], some none)
@[noinline] def ap (f : α → β) (x : α) : β := f x
@[noinline] def viaGen (x : (List α × Nat) × (Option β × List γ)) (a : α) (b : β) (c : γ) : (List α × Nat) × (Option β × List γ) :=
  ((a :: x.1.1, x.1.2 + 1), (some b, c :: x.2.2))
@[noinline] def fillOP (o : Option (List α × List β)) (a : α) (b : β) : Option (List α × List β) := o.map (fun (xs, ys) => (a :: xs, b :: ys))
@[noinline] def fillSum (s : Sum (List α) (List β) × Nat) (a : α) (b : β) : Sum (List α) (List β) × Nat :=
  match s with | (.inl xs, k) => (.inr (b :: (xs.map (fun _ => b))), k + 1) | (.inr ys, k) => (.inl [a], k + ys.length)
@[noinline] def fillExc (e : Except String (List α × Nat)) (a : α) : Except String (List α × Nat) := e.map (fun (xs, k) => (a :: xs, k * 2))
@[noinline] def fillBoth (b : Both (List α) (Option β)) (a : α) (y : β) : Both (List α) (Option β) := match b with | .mk xs o => .mk (a :: xs) (o <|> some y)
@[noinline] def fillTwo (t : Two (List α)) (a : α) : Two (List α) := match t with | .l xs => .r (a :: xs) | .r xs => .l (a :: a :: xs)
@[noinline] def fillIx (x : Ix (List α) 4) (a : α) : Ix (List α) 4 := { x with val := a :: x.val }
@[noinline] def showTwo (t : Two (List α)) (sh : α → String) : String := match t with | .l xs => "L" ++ toString (xs.map sh) | .r xs => "R" ++ toString (xs.map sh)
@[noinline] def fillDeep (d : List (List α × Nat) × Option (Option β)) (a : α) (b : β) : List (List α × Nat) × Option (Option β) := (([a], 1) :: d.1, d.2.map (fun o => o <|> some b))
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let s := toString n
  IO.println s!"{ap (fun x => viaGen x n s true) e3} {viaGen (viaGen e3 s n 'c') s n 'd'} {(e3 : (List Nat × Nat) × (Option String × List Bool))}"
  IO.println s!"{fillOP eOP n s} {fillOP eOP s n} {ap (fillOP eOP n) s} {(eOP : Option (List Nat × List String))}"
  IO.println s!"{(fillSum eSum n s).2} {(fillSum (fillSum eSum n s) n s).2} {(eSum : Sum (List Nat) (List String) × Nat).2}"
  IO.println s!"{fillExc eExc n |>.toOption} {fillExc eExc s |>.toOption} {(eExc : Except String (List Nat × Nat)).toOption}"
  IO.println s!"{match fillBoth eBoth n s with | .mk xs o => s!"{xs} {o}"} {match fillBoth eBoth s n with | .mk xs o => s!"{xs} {o}"}"
  IO.println s!"{showTwo (fillTwo eTwo n) toString} {showTwo (fillTwo (fillTwo eTwo s) s) id} {showTwo (eTwo : Two (List Nat)) toString}"
  IO.println s!"{(fillIx eIx n).val} {(fillIx eIx s).val} {(eIx : Ix (List Nat) 4).i} {(fillIx eIx s).i.val}"
  IO.println s!"{fillDeep eDeep n s} {fillDeep eDeep s n} {(eDeep : List (List Nat × Nat) × Option (Option String))}"
end D71Breaker3R06

namespace D71Breaker3R07
/- R07: PUnit/Unit harder: Unit at always-filled positions of shared values, Unit-domain functions and IO actions in families. -/
structure Pkg where
  b : Bool
  v : if b then (Unit → Nat) else (Unit → String)
structure Act where
  b : Bool
  v : if b then IO Unit else IO Nat
structure UU where
  b : Bool
  v : if b then Unit else PUnit.{1}
def ePU : Unit × List α := ((), [])
def ePU2 : PUnit.{1} × Option α := (PUnit.unit, none)
@[noinline] def fillPU (p : Unit × List α) (a : α) : Unit × List α := (p.1, a :: p.2)
@[noinline] def fillPU2 (p : PUnit.{1} × Option α) (a : α) : PUnit.{1} × Option α := (p.1, some a)
@[noinline] def mkPkg (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, fun _ => n⟩ else ⟨false, fun _ => s!"u{n}"⟩
@[noinline] def rdPkg : Pkg → Nat
  | ⟨true, v⟩ => let f : Unit → Nat := v; f () + f ()
  | ⟨false, v⟩ => let f : Unit → String := v; (f ()).length
@[noinline] def mkAct (n : Nat) : Act := if n % 2 = 0 then ⟨true, IO.println s!"act {n}"⟩ else ⟨false, ((do IO.println s!"ret {n}"; return n * 2) : IO Nat)⟩
@[noinline] def runAct : Act → IO Nat
  | ⟨true, v⟩ => do let a : IO Unit := v; a; a; return 0
  | ⟨false, v⟩ => do let a : IO Nat := v; let x ← a; let y ← a; return x + y
@[noinline] def mkUU (n : Nat) : UU := if n % 2 = 0 then ⟨true, ()⟩ else ⟨false, PUnit.unit⟩
@[noinline] def rdUU : UU → Nat
  | ⟨true, v⟩ => let u : Unit := v; match u with | () => 1
  | ⟨false, v⟩ => let u : PUnit.{1} := v; match u with | PUnit.unit => 2
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let s := toString n
  IO.println s!"{(fillPU ePU n).2} {(fillPU ePU s).2} {(ePU : Unit × List Nat).2.length} {(fillPU2 ePU2 n).2} {(fillPU2 ePU2 s).2}"
  let xs := List.range (n + 2)
  IO.println (xs.map (fun i => rdPkg (mkPkg i)))
  IO.println (← xs.mapM (fun i => runAct (mkAct i)))
  IO.println (xs.map (fun i => rdUU (mkUU i)))
end D71Breaker3R07

namespace D71Breaker3R08
/- R08: forwarder chains over Box parameters: reorder, drop (the Box argument itself), add; partial applications at every level; specialization. -/
structure Pkg where
  b : Bool
  v : if b then Nat else String
@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
@[noinline] def rd : Pkg → Nat
  | ⟨true, v⟩ => let w : Nat := v; w + 1
  | ⟨false, v⟩ => let s : String := v; s.length
@[noinline] def base (k : Nat) (p : Pkg) (q : Pkg) (tag : String) : Nat := rd p * k + rd q + tag.length
def f1 (q : Pkg) (p : Pkg) (k : Nat) : Nat := base k p q "f1"          -- reorder + add
def f2 (p : Pkg) (_dropped : Pkg) (k : Nat) : Nat := f1 p p k            -- drop the Box argument
def f3 (k : Nat) (p : Pkg) : Nat := f2 p (mk 0) k                        -- drop + reorder
def f4 (p : Pkg) : Nat := f3 7 p                                          -- fix the Nat
def g1 (xs : List Pkg) (f : Pkg → Nat) : List Nat := xs.map f
def g2 (f : Pkg → Nat) (xs : List Pkg) : List Nat := g1 xs f              -- reorder a function argument
@[specialize] def spec (f : Pkg → Nat) (xs : List Pkg) : Nat := xs.foldl (fun a p => a + f p) 0
@[inline] def inl (p : Pkg) (k : Nat) : Nat := f3 k p
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ps := (List.range (n + 2)).map mk
  IO.println s!"{ps.map f4} {ps.map (f3 n)} {ps.map (f2 · (mk 1) n)} {ps.map (f1 (mk 1) · n)}"
  IO.println s!"{g2 f4 ps} {g2 (f3 n) ps} {g1 ps (fun p => f1 p p n)} {g2 (inl · n) ps}"
  IO.println s!"{spec f4 ps} {spec (f3 n) ps} {spec rd ps} {spec (fun p => base n p p "x") ps}"
  let h := f3 (n + 1)
  let h2 := f1 (mk n)
  IO.println s!"{ps.map h} {ps.map (h2 · n)} {(ps.map (fun p => h2 p)).length}"
end D71Breaker3R08

namespace D71Breaker3R09
/- R09: statics with shared nodes converted at two instantiations; static arrays/maps/thunks mutated after a read. -/
open Std
structure Pkg where
  b : Bool
  v : if b then Nat else String
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
  | empty : Tree α
@[noinline] def Tree.fill (t : Tree α) (x : α) : Tree α := match t with
  | .leaf a => .node (.leaf a) (.leaf x)
  | .node l r => .node (l.fill x) r
  | .empty => .leaf x
@[noinline] def Tree.toList : Tree α → List α
  | .leaf a => [a] | .node l r => l.toList ++ r.toList | .empty => []
@[noinline] def Tree.size : Tree α → Nat
  | .leaf _ => 1 | .node l r => l.size + r.size + 1 | .empty => 1
def shape : Tree α := let e := Tree.empty; let n := Tree.node e e; .node n n
def shapeL : Tree (List α) := let e := Tree.leaf []; let n := Tree.node e e; .node n (.node n e)
@[noinline] def rd : Pkg → Nat
  | ⟨true, v⟩ => let w : Nat := v; w + 1
  | ⟨false, v⟩ => let s : String := v; s.length
def kArr : Array Pkg := #[⟨true, (1 : Nat)⟩, ⟨false, "ab"⟩, ⟨true, (3 : Nat)⟩]
def kMap : HashMap Nat Pkg := (({} : HashMap Nat Pkg).insert 1 ⟨true, (10 : Nat)⟩).insert 2 ⟨false, "twenty"⟩
def kThunk : Thunk (List Pkg) := Thunk.mk (fun _ => [⟨false, "lazy"⟩])
def kE [BEq α] [Hashable α] : HashMap α (List β) := {}
@[noinline] def useMap (m : HashMap Nat Pkg) (k : Nat) : Nat := (m.getD k ⟨true, (0 : Nat)⟩ |> rd) + m.size
@[noinline] def bump (a : Array Pkg) (i : Nat) : Array Pkg := a.modify (i % a.size) (fun p => match p with
  | ⟨true, v⟩ => let w : Nat := v; ⟨false, toString w⟩
  | ⟨false, v⟩ => let s : String := v; ⟨true, s.length⟩)
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let s := toString n
  IO.println s!"{(shape : Tree Nat).size} {((shape : Tree Nat).fill n).toList} {((shape : Tree String).fill s).toList} {(((shape : Tree String).fill s).fill "b").size}"
  IO.println s!"{((shapeL : Tree (List Nat)).fill [n]).toList} {((shapeL : Tree (List String)).fill [s]).toList} {(shapeL : Tree (List Nat)).size}"
  IO.println s!"{kArr.map rd} {(bump kArr n).map rd} {(bump (bump kArr n) (n + 1)).map rd} {kArr.map rd} {(kArr.push ⟨true, n⟩).map rd} {kArr.size}"
  IO.println s!"{useMap kMap n} {useMap (kMap.insert n ⟨true, n⟩) n} {useMap kMap 1} {kMap.size}"
  IO.println s!"{kThunk.get.map rd} {kThunk.get.length} {(kThunk.get ++ kArr.toList).map rd}"
    let m1 : HashMap Nat (List String) := kE
  let m2 : HashMap String (List Nat) := kE
  IO.println s!"{(m1.insert n [s]).size} {(m2.insert s [n]).getD s []} {m1.size}"
end D71Breaker3R09

namespace D71Breaker3R11
/- R11: partial applications whose remaining domain is a Box class, stored in family-typed fields and lists. -/
structure Pkg where
  b : Bool
  v : if b then Nat else String
@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
@[noinline] def rd : Pkg → Nat
  | ⟨true, v⟩ => let w : Nat := v; w + 1
  | ⟨false, v⟩ => let s : String := v; s.length
@[noinline] def mkL (d : Bool) (n : Nat) : List (if d then Nat else String) :=
  match d with
  | true => (List.range n : List Nat)
  | false => ((List.range n).map toString : List String)
@[noinline] def rdL (d : Bool) (xs : List (if d then Nat else String)) : Nat :=
  if h : d = true then (cast (by simp [h]) xs : List Nat).foldl (· + ·) 0
  else (cast (by simp [h]) xs : List String).foldl (fun a s => a + s.length) 0
def fw1 (d : Bool) (xs : List (if d then Nat else String)) (p : Pkg) : Nat := rd p + rdL d xs   -- remaining domain Pkg
def fw2 (p : Pkg) (d : Bool) (xs : List (if d then Nat else String)) : Nat := fw1 d xs p         -- remaining domain the family list
def fw3 {d : Bool} (_xs : List (if d then Nat else String)) (p : Pkg) : Nat := rd p                            -- dropped family arg
structure Op where
  b : Bool
  f : if b then (Pkg → Nat) else (List (if true then Nat else String) → Nat)
@[noinline] def mkOp (d : Bool) (n : Nat) : Op := if n % 2 = 0 then ⟨true, fw1 d (mkL d n)⟩ else ⟨false, fw2 (mk n) true⟩
@[noinline] def apOp (o : Op) (p : Pkg) (n : Nat) : Nat := match o with
  | ⟨true, f⟩ => let g : Pkg → Nat := f; g p
  | ⟨false, f⟩ => let g : List Nat → Nat := f; g (List.range n)
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ps := (List.range (n + 2)).map mk
  for d in [true, false] do
    let xs := mkL d n
    let fs : List (Pkg → Nat) := [fw1 d xs, fw3 (d := d) xs, fun p => fw2 p d xs, rd]
    IO.println (fs.map (fun f => ps.map f))
    let gs : List (List (if d then Nat else String) → Nat) := [fw2 (mk n) d, rdL d, fun ys => fw1 d ys (mk 1)]
    IO.println (gs.map (fun g => g xs + g (mkL d (n + 1))))
    IO.println (((List.range (n + 2)).map (mkOp d)).map (fun o => apOp o (mk n) n))
end D71Breaker3R11

namespace D71Breaker3R12
/- R12: Unit-carrying containers at family positions with modify/set!/pop (box(0) placeholder idioms), Option Unit cells. -/
structure AU where
  b : Bool
  v : if b then Array Unit else Array Nat
structure OU where
  b : Bool
  v : if b then Option Unit else Option (Option Unit)
@[noinline] def mkAU (n : Nat) : AU := if n % 2 = 0 then ⟨true, Array.replicate n ()⟩ else ⟨false, Array.range n⟩
@[noinline] def stepAU : AU → AU
  | ⟨true, v⟩ => let a : Array Unit := v; ⟨true, (a.push ()).modify 0 (fun _ => ())⟩
  | ⟨false, v⟩ => let a : Array Nat := v; ⟨false, (a.push a.size).modify 0 (· + 100)⟩
@[noinline] def rdAU : AU → Nat
  | ⟨true, v⟩ => let a : Array Unit := v; a.size
  | ⟨false, v⟩ => let a : Array Nat := v; a.foldl (· + ·) 0
@[noinline] def mkOU (n : Nat) : OU := match n % 4 with
  | 0 => ⟨true, none⟩ | 1 => ⟨true, some ()⟩ | 2 => ⟨false, none⟩ | _ => ⟨false, some (if n % 8 == 3 then none else some ())⟩
@[noinline] def rdOU : OU → Nat
  | ⟨true, v⟩ => let o : Option Unit := v; if o.isSome then 1 else 0
  | ⟨false, v⟩ => let o : Option (Option Unit) := v; match o with | none => 10 | some none => 20 | some (some ()) => 30
@[noinline] def flipOU : OU → OU
  | ⟨true, v⟩ => let o : Option Unit := v; ⟨false, some o⟩
  | ⟨false, v⟩ => let o : Option (Option Unit) := v; ⟨true, o.bind id⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let xs := List.range (n + 4)
  IO.println (xs.map (fun i => rdAU (mkAU i)))
  IO.println (xs.map (fun i => rdAU (stepAU (stepAU (mkAU i)))))
  IO.println (xs.map (fun i => rdOU (mkOU i)))
  IO.println (xs.map (fun i => rdOU (flipOU (mkOU i))))
  IO.println (xs.map (fun i => rdOU (flipOU (flipOU (mkOU i)))))
  let arr := (xs.map mkOU).toArray
  IO.println ((arr.modify 1 flipOU).map rdOU)
  IO.println ((arr.pop.push ⟨true, some ()⟩).map rdOU)
end D71Breaker3R12

def main : IO Unit := do
  IO.println "-- D71Breaker3R01"
  D71Breaker3R01.caseMain ["3"]
  IO.println "-- D71Breaker3R02"
  D71Breaker3R02.caseMain ["5"]
  IO.println "-- D71Breaker3R03"
  D71Breaker3R03.caseMain ["4"]
  IO.println "-- D71Breaker3R04"
  D71Breaker3R04.caseMain ["4"]
  IO.println "-- D71Breaker3R05"
  D71Breaker3R05.caseMain ["4"]
  IO.println "-- D71Breaker3R06"
  D71Breaker3R06.caseMain ["3"]
  IO.println "-- D71Breaker3R07"
  D71Breaker3R07.caseMain ["4"]
  IO.println "-- D71Breaker3R08"
  D71Breaker3R08.caseMain ["4"]
  IO.println "-- D71Breaker3R09"
  D71Breaker3R09.caseMain ["4"]
  IO.println "-- D71Breaker3R11"
  D71Breaker3R11.caseMain ["4"]
  IO.println "-- D71Breaker3R12"
  D71Breaker3R12.caseMain ["5"]
