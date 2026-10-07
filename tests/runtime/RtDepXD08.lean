/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `D71BreakerP30C`: Closed shared terms holding functions whose results or
  arguments are the reader's type
- `D71ReviewerC1`: A same-layout structure cast into a family position that
  other values make Box (B5/B6 cast arm)
- `D71Tester8e9R01`: B5 always-filled pruning: pair and structure clashes at
  always-filled positions (no arm) beside may-be-empty positions (List,
  Option, Array, Thunk, Task, arrow) whose arms stay
- `D71Tester8e9R02`: A value Lean shares between two instantiations at a
  may-be-empty position (a closed (0, []) read at Nat × List Nat and Nat ×
  List String) boxed and unboxed
- `D71Tester8e9R03`: B3/B5: ()'s own variant beside Unit: () boxed directly,
  inside Option and pairs, and a family position read at Unit
- `D71Tester8e9R04`: B4 forwarder move locations: calls and partial
  applications of user forwarders (reordered, added arguments) at Box
  positions
- `D71Tester8e9R05`: A forwarder partial application stored at a Box
  position whose remaining domain needs a coercion (fail closed allowed,
  never wrong)
- `D71Tester8e9R06`: Print-rebuildable statics whose Clone needs a Link-
  reached UBox (FreeM continuation domain), read several times, in a loop,
  and through a generic
- `D71TesterF33N01`: Site rule (h): a projection of a family field off a
  cell, then a later refinement types it
- `D71TesterF33N02`: Site rule (c), (g): a local function value applied to
  an unboxed list, and an over-application's result
- `D71TesterF33N03`: Site rule: call result into let, return at the family
  type, producer chains (reverse, append, map) before the refined read -/

namespace D71BreakerP30C
/- P30: closed shared terms holding functions whose results or arguments are the reader's type -/
structure Gen (σ : Type) where
  next : Nat → σ
  tag : Nat
structure Accum (σ : Type) where
  step : σ → σ
  seed : Option σ
def emptyGen {α : Type} : Gen (List α) := ⟨fun _ => [], 7⟩
def idAccumum {σ : Type} : Accum σ := ⟨fun s => s, none⟩
def pairFn {α : Type} : (α → α × α) × Nat := (fun a => (a, a), 1)

@[noinline] def useGen (g : Gen (List α)) (x : α) (n : Nat) : List α := x :: g.next n ++ g.next (n + 1)
@[noinline] def useAccumum (a : Accum σ) (x : σ) (n : Nat) : σ := (List.range n).foldl (fun s _ => a.step s) (a.seed.getD x)
@[noinline] def usePair (p : (α → α × α) × Nat) (x : α) : α × α × Nat := let (a, b) := p.1 x; (a, b, p.2)

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{usePair pairFn n} {usePair pairFn (toString n)}"
end D71BreakerP30C

namespace D71ReviewerC1
structure P where
  a : Nat
  b : Nat
structure Q where
  x : Nat
  y : Nat
inductive Pkg where
  | mk (b : Bool) (v : if b then Q else Nat)
@[noinline] unsafe def mk1 (n : Nat) : Pkg := ⟨true, unsafeCast (P.mk n 2)⟩
@[noinline] def mk2 (n : Nat) : Pkg := ⟨false, n⟩
@[noinline] def mk3 (n : Nat) : Pkg := ⟨true, Q.mk n 5⟩
def rd : Pkg → Nat
  | ⟨true, v⟩ => v.x + v.y + 1
  | ⟨false, v⟩ => v
unsafe def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 7
  IO.println s!"{rd (mk1 n)} {rd (mk2 n)} {rd (mk3 n)}"
end D71ReviewerC1

namespace D71Tester8e9R01
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
structure P2 (α β : Type) where
  a : α
  b : β
instance {α β : Type} [ToString α] [ToString β] : ToString (P2 α β) := ⟨fun p => s!"<{p.a}|{p.b}>"⟩
instance {α : Type} [ToString α] : ToString (Thunk α) := ⟨fun t => s!"T{t.get}"⟩
instance {α : Type} [ToString α] : ToString (Task α) := ⟨fun t => s!"K{t.get}"⟩
instance : ToString (Nat → Nat) := ⟨fun f => s!"F{f 1}"⟩
instance : ToString (String → Nat) := ⟨fun f => s!"G{f "ab"}"⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let xs : List AnyS := [⟨((n : Nat), s!"s{n}")⟩, ⟨(decide (n > 2), s!"t{n}")⟩, ⟨(P2.mk n "x" : P2 Nat String)⟩, ⟨(P2.mk (decide (n > 1)) "y" : P2 Bool String)⟩,
    ⟨(some n : Option Nat)⟩, ⟨(some s!"o{n}" : Option String)⟩, ⟨(none : Option Nat)⟩, ⟨(none : Option String)⟩,
    ⟨(#[n] : Array Nat)⟩, ⟨(#[] : Array String)⟩, ⟨(Thunk.mk fun _ => n * 3 : Thunk Nat)⟩, ⟨(Thunk.mk fun _ => s!"h{n}" : Thunk String)⟩,
    ⟨(Task.spawn fun _ => n + 7 : Task Nat)⟩, ⟨(Task.spawn fun _ => s!"k{n}" : Task String)⟩, ⟨((· + n) : Nat → Nat)⟩, ⟨((·.length + n) : String → Nat)⟩]
  IO.println (xs.map (·.show))
end D71Tester8e9R01

namespace D71Tester8e9R02
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
@[noinline] def emptyPair {α : Type} : Nat × List α := (0, [])
@[noinline] def emptyOpt {α : Type} : Option α × Nat := (none, 3)
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let xs : List AnyS := [⟨(emptyPair : Nat × List Nat)⟩, ⟨(emptyPair : Nat × List String)⟩, ⟨(emptyOpt : Option Nat × Nat)⟩, ⟨(emptyOpt : Option String × Nat)⟩, ⟨n⟩]
  IO.println (xs.map (·.show))
end D71Tester8e9R02

namespace D71Tester8e9R03
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def F : Bool → Type
  | true => Nat
  | false => Unit
@[noinline] def get : (b : Bool) → Nat → F b
  | true, n => n + 3
  | false, _ => ()
@[noinline] def unitOf (n : Nat) : Unit := if n > 100 then () else ()
@[noinline] def showU (u : Unit) : String := match u with | () => "unit"
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let xs : List AnyS := [⟨()⟩, ⟨unitOf n⟩, ⟨(some () : Option Unit)⟩, ⟨((), n)⟩, ⟨n⟩, ⟨(none : Option Unit)⟩]
  let a : Nat := get true n
  let u : Unit := get false n
  IO.println s!"{xs.map (·.show)} {a} {showU u}"
end D71Tester8e9R03

namespace D71Tester8e9R04
structure AnyF where
  {α : Type}
  f : α → String
  x : α
@[noinline] def tgt {α : Type} [ToString α] (k : Nat) (x : α) (sep : String) : String := s!"{x}{sep}{k}"
def fwd {α : Type} [ToString α] (x : α) (k : Nat) : String := tgt k x "#"
def fwd2 {α : Type} [ToString α] (k : Nat) : α → String := fun x => fwd x k
@[noinline] def AnyF.run (s : AnyF) : String := s.f s.x
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let xs : List AnyF := [⟨fun (x : Nat) => fwd x n, n⟩, ⟨fun (s : String) => fwd s (n + 1), "a"⟩, ⟨fwd2 (n + 2), n * 2⟩, ⟨fwd2 7, "bc"⟩,
    ⟨fun (b : Bool) => tgt n b "!", decide (n > 1)⟩]
  IO.println (xs.map (·.run))
end D71Tester8e9R04

namespace D71Tester8e9R05
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
structure Box2 (α : Type) where
  v : α
instance {α : Type} [ToString α] : ToString (Box2 α) := ⟨fun b => s!"[{b.v}]"⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let xs : List AnyS := [⟨(Box2.mk n : Box2 Nat)⟩, ⟨n⟩, ⟨(Box2.mk s!"s{n}" : Box2 String)⟩, ⟨(Box2.mk (Box2.mk n) : Box2 (Box2 Nat))⟩]
  IO.println (xs.map (·.show))
end D71Tester8e9R05

namespace D71Tester8e9R06
inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
def FreeM.lift {F : Type → Type} {ι : Type} (op : F ι) : FreeM F ι := .liftBind op .pure
inductive Op : Type → Type where
  | getN : Op Nat
  | getS : Op String
@[noinline] def run : FreeM Op Nat → Nat
  | .pure a => a
  | .liftBind .getN k => run (k 5)
  | .liftBind .getS k => run (k "abc")
def getN : FreeM Op Nat := .lift .getN
def lenS : FreeM Op Nat := .liftBind .getS fun s => .pure s.length
@[noinline] def twiceOf.{u} {β : Type u} (x : β) : β × β := (x, x)
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let mut acc := 0
  for _ in [0:n] do
    acc := acc + run getN + run lenS
  let (p, q) := twiceOf (β := FreeM Op Nat) getN
  IO.println s!"{acc} {run getN} {run p + run q} {run lenS}"
end D71Tester8e9R06

namespace D71TesterF33N01
structure W where
  b : Bool
  v : List (if b then Nat else String)
@[noinline] def mkW : (c d : Bool) → if c then W else Nat
  | true, true => (⟨true, ([1, 2, 3] : List Nat)⟩ : W)
  | true, false => (⟨false, (["a", "bc"] : List String)⟩ : W)
  | false, _ => (5 : Nat)
@[noinline] def getW : (c : Bool) → (if c then W else Nat) → Nat
  | true, w => match w with
    | ⟨true, xs⟩ => (let ys : List Nat := xs; ys.foldl (· + ·) 0)
    | ⟨false, xs⟩ => xs.length * 10
  | false, n => n
@[noinline] def getP : (c : Bool) → (if c then W else Nat) → Nat
  | true, w => let xs := w.v; match hb : w.b with
    | true => (let ys : List Nat := cast (by rw [hb]; rfl) xs; ys.length + 100)
    | false => xs.length + 200
  | false, n => n
def caseMain (a : List String) : IO Unit := do
  let c := a.length < 100
  for d in [a.isEmpty, !a.isEmpty] do
    IO.println s!"{getW c (mkW c d)} {getP c (mkW c d)} {getW false (mkW false d)}"
end D71TesterF33N01

namespace D71TesterF33N02
@[noinline] def mkQ : (c d : Bool) → if c then List (if d then Nat else String) else Nat
  | true, true => ([1, 2] : List Nat) | true, false => (["a"] : List String) | false, _ => (5 : Nat)
@[noinline] def pick (k : Nat) : Nat → Nat → Nat := if k % 2 == 0 then (· + ·) else (· * ·)
@[noinline] def getF : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, d, xs =>
    let f : List (if d then Nat else String) → Nat := fun ys => match d, ys with
      | true, zs => (let ws : List Nat := zs; ws.foldl (· + ·) 1) | false, zs => zs.length
    f xs + pick xs.length 3 4
  | false, _, n => n
def caseMain (a : List String) : IO Unit := do
  let c := a.length < 100
  for d in [a.isEmpty, !a.isEmpty] do
    IO.println s!"{getF c d (mkQ c d)}"
end D71TesterF33N02

namespace D71TesterF33N03
@[noinline] def mkQ : (c d : Bool) → if c then List (if d then Nat else String) else Nat
  | true, true => ([1, 2, 5] : List Nat) | true, false => (["a", "b"] : List String) | false, _ => (5 : Nat)
@[noinline] def headF (d : Bool) (xs : List (if d then Nat else String)) (dflt : if d then Nat else String) : if d then Nat else String :=
  match xs with | [] => dflt | h :: _ => h
@[noinline] def getR : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → String
  | true, d, xs =>
    let xs0 : List (if d then Nat else String) := xs
    let ys := xs0.reverse ++ xs0
    let h := headF d ys (match d with | true => (0 : Nat) | false => ("z" : String))
    match d, h with
    | true, n => toString ((show Nat from n) * 2)
    | false, s => (show String from s) ++ "!"
  | false, _, n => toString (show Nat from n)
def caseMain (a : List String) : IO Unit := do
  let c := a.length < 100
  for d in [a.isEmpty, !a.isEmpty] do
    IO.println s!"{getR c d (mkQ c d)}"
end D71TesterF33N03

unsafe def main : IO Unit := do
  IO.println "-- D71BreakerP30C"
  D71BreakerP30C.caseMain ["3"]
  IO.println "-- D71ReviewerC1"
  D71ReviewerC1.caseMain []
  IO.println "-- D71Tester8e9R01"
  D71Tester8e9R01.caseMain ["4"]
  IO.println "-- D71Tester8e9R02"
  D71Tester8e9R02.caseMain ["4"]
  IO.println "-- D71Tester8e9R03"
  D71Tester8e9R03.caseMain ["4"]
  IO.println "-- D71Tester8e9R04"
  D71Tester8e9R04.caseMain ["4"]
  IO.println "-- D71Tester8e9R05"
  D71Tester8e9R05.caseMain ["4"]
  IO.println "-- D71Tester8e9R06"
  D71Tester8e9R06.caseMain ["4"]
  IO.println "-- D71TesterF33N01"
  D71TesterF33N01.caseMain ["a", "b"]
  IO.println "-- D71TesterF33N02"
  D71TesterF33N02.caseMain ["a", "b"]
  IO.println "-- D71TesterF33N03"
  D71TesterF33N03.caseMain ["a", "b"]
