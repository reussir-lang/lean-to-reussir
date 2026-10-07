import Std.Data.HashMap
/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `D71BreakerP10`: IO.Ref through Box positions: refs in existentials and
  dependent records, aliasing, Ref Pkg.
- `D71BreakerP11`: CPS / continuation handlers at two answer types
- `D71BreakerP11A`: CPS / continuation handlers at two answer types
- `D71BreakerP11D`: Cont alias at two answer types, ret/run only
- `D71BreakerP11F`: Cont alias at one answer type, bind changing alpha
- `D71BreakerP12`: HashMap and an own AssocList at several key/value types
  with shared empties and a generic tally.
- `D71BreakerP13`: Thunks, tasks, options and nested containers at family
  positions
- `D71BreakerP14A`: P14A
- `D71BreakerP14AD`: P14A
- `D71BreakerP14AE`: P14A
- `D71BreakerP14B`: P14B -/

namespace D71BreakerP10
/- P10: IO.Ref through Box positions: refs in existentials and dependent records, aliasing, Ref Pkg. -/
structure Pkg where
  b : Bool
  v : if b then Nat else String

structure RB where
  b : Bool
  r : IO.Ref (if b then Nat else String)

structure AnyRef where
  {α : Type}
  r : IO.Ref α
  sh : α → String
  bump : α → α

@[noinline] def mkRB (n : Nat) : IO RB := do
  if n % 2 = 0 then return RB.mk true (← IO.mkRef (n : Nat)) else return RB.mk false (← IO.mkRef (toString n : String))

@[noinline] def incRB : RB → IO Unit
  | ⟨true, r⟩ => r.modify (fun (x : Nat) => x + 1)
  | ⟨false, r⟩ => r.modify (fun (x : String) => x ++ "+")

@[noinline] def showRB : RB → IO String
  | ⟨true, r⟩ => do let x : Nat := ← r.get; return toString x
  | ⟨false, r⟩ => do let x : String := ← r.get; return x

@[noinline] def AnyRef.step (a : AnyRef) : IO String := do
  a.r.modify a.bump
  return a.sh (← a.r.get)

@[noinline] def swapPkg : Pkg → Pkg
  | ⟨true, v⟩ => let w : Nat := v; ⟨false, toString w⟩
  | ⟨false, v⟩ => let s : String := v; ⟨true, s.length⟩
@[noinline] def showPkg : Pkg → String
  | ⟨true, v⟩ => let w : Nat := v; s!"N{w}"
  | ⟨false, v⟩ => let s : String := v; s!"S{s}"

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let rbs ← (List.range (n + 2)).mapM mkRB
  for rb in rbs do incRB rb
  for rb in rbs do incRB rb
  for rb in rbs do IO.println (← showRB rb)
  -- a native ref aliased into RB
  let rn ← IO.mkRef (n : Nat)
  let rb : RB := RB.mk true rn
  incRB rb; rn.modify (· * 10); incRB rb
  IO.println s!"{← rn.get} {← showRB rb}"
  -- existential refs sharing one cell with a native alias
  let rs ← IO.mkRef (toString n)
  let a1 : AnyRef := { r := rn, sh := toString, bump := (· + 100) }
  let a2 : AnyRef := { r := rs, sh := id, bump := (· ++ "!") }
  let a3 : AnyRef := { r := rn, sh := fun x => s!"<{x}>", bump := (· + 1) }
  let anys : List AnyRef := [a1, a2, a3]
  for a in anys do IO.println (← a.step)
  IO.println s!"{← rn.get} {← rs.get}"
  -- a ref holding a dependent record
  let rp ← IO.mkRef (⟨true, n⟩ : Pkg)
  rp.modify swapPkg
  IO.println (showPkg (← rp.get))
  rp.modify swapPkg
  IO.println (showPkg (← rp.get))
  let rl ← IO.mkRef ([] : List Pkg)
  for i in List.range n do rl.modify (fun l => (if i % 2 = 0 then ⟨true, i⟩ else ⟨false, toString i⟩) :: l)
  IO.println ((← rl.get).map showPkg)
end D71BreakerP10

namespace D71BreakerP11
/- P11: CPS / continuation handlers at two answer types; function-typed family positions; partial applications. -/
def Cont (r α : Type) := (α → r) → r

@[noinline] def Cont.ret (a : α) : Cont r α := fun k => k a
@[noinline] def Cont.bind (m : Cont r α) (f : α → Cont r β) : Cont r β := fun k => m (fun a => f a k)
@[noinline] def Cont.run (m : Cont r r) : r := m id

@[noinline] def sumTo (n : Nat) : Cont r Nat :=
  match n with
  | 0 => Cont.ret 0
  | k + 1 => (sumTo k).bind (fun s => Cont.ret (s + k + 1))

@[noinline] def earlyExit (n : Nat) (stop : Nat) : Cont String Nat := fun k =>
  if n > stop then s!"stopped at {n}" else k n

structure Op where
  b : Bool
  f : if b then (Nat → Nat) else (String → String → String)

@[noinline] def mkOp (n : Nat) : Op := if n % 2 = 0 then ⟨true, (· + n)⟩ else ⟨false, fun a b => a ++ toString n ++ b⟩
@[noinline] def apOp (o : Op) (n : Nat) : String := match o with
  | ⟨true, f⟩ => let g : Nat → Nat := f; toString (g n)
  | ⟨false, f⟩ => let g : String → String → String := f; g "<" (toString n)

@[noinline] def mapOp (o : Op) : Op := match o with
  | ⟨true, f⟩ => let g : Nat → Nat := f; ⟨true, fun x => g (g x)⟩
  | ⟨false, f⟩ => let g : String → String → String := f; ⟨false, fun a b => g b a⟩

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println ((sumTo n).run)
  IO.println (((sumTo n).bind (fun s => Cont.ret (toString s ++ "!"))).run)
  IO.println (((earlyExit n 2).bind (fun x => Cont.ret (toString (x * 2)))) id)
  IO.println (((earlyExit n 5).bind (fun x => Cont.ret (toString (x * 2)))) id)
  let ops := (List.range (n + 2)).map mkOp
  IO.println (ops.map (apOp · n))
  IO.println ((ops.map mapOp).map (apOp · n))
  IO.println (((ops.map mapOp).map mapOp).map (apOp · 1))
end D71BreakerP11

namespace D71BreakerP11A
/- P11: CPS / continuation handlers at two answer types; function-typed family positions; partial applications. -/
def Cont (r α : Type) := (α → r) → r

@[noinline] def Cont.ret (a : α) : Cont r α := fun k => k a
@[noinline] def Cont.bind (m : Cont r α) (f : α → Cont r β) : Cont r β := fun k => m (fun a => f a k)
@[noinline] def Cont.run (m : Cont r r) : r := m id

@[noinline] def sumTo (n : Nat) : Cont r Nat :=
  match n with
  | 0 => Cont.ret 0
  | k + 1 => (sumTo k).bind (fun s => Cont.ret (s + k + 1))

@[noinline] def earlyExit (n : Nat) (stop : Nat) : Cont String Nat := fun k =>
  if n > stop then s!"stopped at {n}" else k n

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println ((sumTo n).run)
  IO.println (((sumTo n).bind (fun s => Cont.ret (toString s ++ "!"))).run)
  IO.println (((earlyExit n 2).bind (fun x => Cont.ret (toString (x * 2)))) id)
  IO.println (((earlyExit n 5).bind (fun x => Cont.ret (toString (x * 2)))) id)
end D71BreakerP11A

namespace D71BreakerP11D
/- P11D: Cont alias at two answer types, ret/run only -/
def Cont (r α : Type) := (α → r) → r
@[noinline] def Cont.ret (a : α) : Cont r α := fun k => k a
@[noinline] def Cont.run (m : Cont r r) : r := m id
@[noinline] def Cont.mapK (m : Cont r α) (g : r → r) : Cont r α := fun k => g (m k)
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println ((Cont.ret n).run)
  IO.println ((Cont.ret (toString n)).run)
  IO.println (((Cont.ret n).mapK (· * 2)).run)
  IO.println (((Cont.ret (toString n)).mapK (· ++ "!")).run)
end D71BreakerP11D

namespace D71BreakerP11F
/- P11F: Cont alias at one answer type, bind changing alpha -/
def Cont (r α : Type) := (α → r) → r
@[noinline] def Cont.ret (a : α) : Cont r α := fun k => k a
@[noinline] def Cont.bind (m : Cont r α) (f : α → Cont r β) : Cont r β := fun k => m (fun a => f a k)
@[noinline] def Cont.run (m : Cont r r) : r := m id
@[noinline] def sumTo (n : Nat) : Cont String Nat :=
  match n with
  | 0 => Cont.ret 0
  | k + 1 => (sumTo k).bind (fun s => Cont.ret (s + k + 1))
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println (((sumTo n).bind (fun s => Cont.ret (toString s ++ "!"))).run)
  IO.println (((sumTo n).bind (fun s => Cont.ret (toString (s * 2)))).run)
end D71BreakerP11F

namespace D71BreakerP12
/- P12: HashMap and an own AssocList at several key/value types with shared empties and a generic tally. -/
open Std

structure Point where
  x : Nat
  y : Nat
  deriving BEq, Hashable, Repr

inductive AList (κ ν : Type) where
  | nil : AList κ ν
  | cons : κ → ν → AList κ ν → AList κ ν

@[noinline] def AList.insert [BEq κ] (k : κ) (v : ν) : AList κ ν → AList κ ν
  | .nil => .cons k v .nil
  | .cons k' v' r => if k == k' then .cons k v r else .cons k' v' (r.insert k v)
@[noinline] def AList.find? [BEq κ] (k : κ) : AList κ ν → Option ν
  | .nil => none
  | .cons k' v r => if k == k' then some v else r.find? k
@[noinline] def AList.size : AList κ ν → Nat
  | .nil => 0
  | .cons _ _ r => 1 + r.size

@[noinline] def tally [BEq κ] [Hashable κ] (xs : List κ) : HashMap κ Nat :=
  xs.foldl (fun m k => m.insert k (m.getD k 0 + 1)) {}

@[noinline] def tallyA [BEq κ] (xs : List κ) : AList κ Nat :=
  xs.foldl (fun m k => m.insert k ((m.find? k).getD 0 + 1)) .nil

@[noinline] def emptyA : AList κ ν := .nil

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let pts := (List.range n).map (fun i => Point.mk (i % 2) (i % 3))
  let mp := tally pts
  let mn := tally ((List.range n).map (· % 3))
  let ms := tally ((List.range n).map (fun i => toString (i % 2)))
  IO.println s!"{mp.size} {mn.size} {ms.size} {mp.getD ⟨0,0⟩ 0} {mn.getD 1 0} {ms.getD "1" 0}"
  let e1 : HashMap Point Nat := {}
  let e2 : HashMap Nat PUnit := {}
  let e3 : HashMap String (List Nat) := {}
  IO.println s!"{e1.size} {e2.size} {e3.size} {(e1.insert ⟨n,n⟩ n).size} {(e2.insert n ()).size} {(e3.insert "k" [n]).getD "k" []}"
  let ap := tallyA pts
  let an := tallyA ((List.range n).map (· % 3))
  let as := tallyA ((List.range n).map (fun i => toString (i % 2)))
  IO.println s!"{ap.size} {an.size} {as.size} {ap.find? ⟨0,0⟩} {an.find? 1} {as.find? "1"}"
  let f1 : AList Point Nat := emptyA
  let f2 : AList Nat PUnit := emptyA
  let f3 : AList String String := emptyA
  IO.println s!"{f1.size} {f2.size} {f3.size} {(f1.insert ⟨n,n⟩ n).find? ⟨n,n⟩} {(f2.insert n ()).size} {(f3.insert "k" "v").find? "k"}"
end D71BreakerP12

namespace D71BreakerP13
/- P13: thunks, tasks, options and nested containers at family positions; never-forced thunks; scalar payloads. -/
structure TQ where
  b : Bool
  t : Thunk (Option (List (if b then Nat else String)))

structure SC where
  b : Bool
  v : if b then UInt8 else Float
  w : if b then Char else UInt64
  u : if b then Unit else Bool

@[noinline] def mkTQ (n : Nat) : TQ :=
  if n % 2 = 0 then ⟨true, Thunk.mk (fun _ => if n > 1000 then none else some (List.range n))⟩
  else ⟨false, Thunk.mk (fun _ => if n == 7 then panic! "forced 7" else some ((List.range n).map toString))⟩

@[noinline] def sizeTQ : TQ → Nat
  | ⟨true, t⟩ => let o : Option (List Nat) := t.get; (o.getD []).foldl (· + ·) 0
  | ⟨false, t⟩ => let o : Option (List String) := t.get; (o.getD []).foldl (fun a s => a + s.length) 0

@[noinline] def mkSC (n : Nat) : SC :=
  if n % 2 = 0 then ⟨true, (n.toUInt8 + 250), Char.ofNat (65 + n % 26), ()⟩ else ⟨false, (n.toFloat / 4.0), (n.toUInt64 * 1000000000000), n % 3 == 0⟩

@[noinline] def showSC : SC → String
  | ⟨true, v, w, u⟩ => let a : UInt8 := v; let c : Char := w; let _ : Unit := u; s!"{a} {c}"
  | ⟨false, v, w, u⟩ => let f : Float := v; let k : UInt64 := w; let b : Bool := u; s!"{f} {k} {b}"

structure TK where
  b : Bool
  t : Task (List (if b then Nat else String))

@[noinline] def mkTK (n : Nat) : TK :=
  if n % 2 = 0 then ⟨true, Task.spawn (fun _ => List.range n)⟩ else ⟨false, (Task.spawn (fun _ => List.range n)).map (·.map toString)⟩
@[noinline] def sizeTK : TK → Nat
  | ⟨true, t⟩ => let l : List Nat := t.get; l.foldl (· + ·) 0
  | ⟨false, t⟩ => let l : List String := t.get; l.foldl (fun a s => a + s.length) 0

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let tqs := (List.range (n + 2)).map mkTQ
  IO.println (tqs.map sizeTQ)
  let never := mkTQ 7   -- never forced
  IO.println (tqs.length + (if never.b then 1 else 0))
  IO.println ((List.range (n + 2)).map (fun i => showSC (mkSC i)))
  IO.println ((List.range (n + 2)).map (fun i => sizeTK (mkTK i)))
end D71BreakerP13

namespace D71BreakerP14A
/- P14A -/
@[noinline] def ap (f : α → β) (x : α) : β := f x
@[noinline] def apL (f : List α → List α) (x : List α) : List α := f x
@[noinline] def ap2 (f : α → α → α) (x y : α) : α := f x y
def flipPair : α × β → β × α := fun (a, b) => (b, a)
def revAll : List α → List α := fun xs => xs.reverse
def dupHead : List α → List α := fun xs => match xs with | [] => [] | x :: r => x :: x :: r
def pickFst : α → α → α := fun a _ => a
def wrapOpt : α → Option α := some
def constNone : α → Option β := fun _ => none
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let s := toString n
  IO.println s!"{ap flipPair (n, s)} {ap flipPair (s, n)} {ap flipPair (n, n)}"
end D71BreakerP14A

namespace D71BreakerP14AD
/- P14A -/
@[noinline] def ap (f : α → β) (x : α) : β := f x
@[noinline] def apL (f : List α → List α) (x : List α) : List α := f x
@[noinline] def ap2 (f : α → α → α) (x y : α) : α := f x y
def flipPair : α × β → β × α := fun (a, b) => (b, a)
def revAll : List α → List α := fun xs => xs.reverse
def dupHead : List α → List α := fun xs => match xs with | [] => [] | x :: r => x :: x :: r
def pickFst : α → α → α := fun a _ => a
def wrapOpt : α → Option α := some
def constNone : α → Option β := fun _ => none
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let s := toString n
  IO.println s!"{ap flipPair (n, s)} {ap flipPair (s, n)} {ap flipPair (n, n)}"
  IO.println s!"{ap (List.map toString) (List.range n)} {ap (List.map String.length) [s, "abc"]}"
  IO.println s!"{ap (fun xs => (xs.reverse, xs.length)) (List.range n)} {ap (fun xs => (xs.reverse, xs.length)) [s]}"
end D71BreakerP14AD

namespace D71BreakerP14AE
/- P14A -/
@[noinline] def ap (f : α → β) (x : α) : β := f x
@[noinline] def apL (f : List α → List α) (x : List α) : List α := f x
@[noinline] def ap2 (f : α → α → α) (x y : α) : α := f x y
def flipPair : α × β → β × α := fun (a, b) => (b, a)
def revAll : List α → List α := fun xs => xs.reverse
def dupHead : List α → List α := fun xs => match xs with | [] => [] | x :: r => x :: x :: r
def pickFst : α → α → α := fun a _ => a
def wrapOpt : α → Option α := some
def constNone : α → Option β := fun _ => none
structure Fns where
  b : Bool
  g : if b then (List Nat → List Nat) else (List String → List String)

@[noinline] def mkFns (n : Nat) : Fns := if n % 2 = 0 then ⟨true, fun xs => xs.reverse⟩ else ⟨false, fun xs => xs ++ xs⟩
@[noinline] def useFns (f : Fns) : String := match f with
  | ⟨true, g⟩ => let h : List Nat → List Nat := g; toString (h [1, 2, 3])
  | ⟨false, g⟩ => let h : List String → List String := g; toString (h ["a", "b"])

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let s := toString n
  IO.println s!"{ap flipPair (n, s)} {ap flipPair (s, n)} {ap flipPair (n, n)}"
  IO.println (((List.range (n + 2)).map mkFns).map useFns)
end D71BreakerP14AE

namespace D71BreakerP14B
/- P14B -/
@[noinline] def ap (f : α → β) (x : α) : β := f x
@[noinline] def apL (f : List α → List α) (x : List α) : List α := f x
@[noinline] def ap2 (f : α → α → α) (x y : α) : α := f x y
def flipPair : α × β → β × α := fun (a, b) => (b, a)
def revAll : List α → List α := fun xs => xs.reverse
def dupHead : List α → List α := fun xs => match xs with | [] => [] | x :: r => x :: x :: r
def pickFst : α → α → α := fun a _ => a
def wrapOpt : α → Option α := some
def constNone : α → Option β := fun _ => none
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let s := toString n
  IO.println s!"{apL revAll (List.range n)} {apL revAll [s, "x"]} {apL dupHead (List.range n)} {apL dupHead [s]}"
end D71BreakerP14B

def main : IO Unit := do
  IO.println "-- D71BreakerP10"
  D71BreakerP10.caseMain ["4"]
  IO.println "-- D71BreakerP11"
  D71BreakerP11.caseMain ["7"]
  IO.println "-- D71BreakerP11A"
  D71BreakerP11A.caseMain ["3"]
  IO.println "-- D71BreakerP11D"
  D71BreakerP11D.caseMain ["3"]
  IO.println "-- D71BreakerP11F"
  D71BreakerP11F.caseMain ["3"]
  IO.println "-- D71BreakerP12"
  D71BreakerP12.caseMain ["6"]
  IO.println "-- D71BreakerP13"
  D71BreakerP13.caseMain ["5"]
  IO.println "-- D71BreakerP14A"
  D71BreakerP14A.caseMain ["3"]
  IO.println "-- D71BreakerP14AD"
  D71BreakerP14AD.caseMain ["3"]
  IO.println "-- D71BreakerP14AE"
  D71BreakerP14AE.caseMain ["3"]
  IO.println "-- D71BreakerP14B"
  D71BreakerP14B.caseMain ["3"]
