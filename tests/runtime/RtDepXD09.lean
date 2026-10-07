/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `D71TesterF33N05`: NS34 probes: generic unboxing sites instantiated from a
  closure's domain, through a structure, at Option A / A × A / Array A
- `D71TesterF33N06`: NS34 probes: a generic chain (getG calls getG') and a
  generic read under a let-bound continuation
- `D71TesterF33N07`: U2 rule (a): clones of generated generic types holding
  a list through Option, a pair, Except, Array (need the list's Clone)
- `D71TesterF33N08`: U2 rule (a): clones of types holding a list only under
  IO.Ref, Thunk, Task, IO.Promise (no Clone of the list needed)
- `D71TesterF33N09`: U2 rule (a): a clone of a value holding a Box-typed
  FreeM continuation (FreeM<F, A, UBox> counts UBox), a Deep/Inline-holding
  record
- `D71TesterF33N10`: D2 'static: generic code storing closures that capture
  a generic value into an unscoped class (an existential reaching Box, a
  Thunk)
- `D71TesterF33N11`: Site rule (a)/(b): an unboxed list passed into a
  constructor's field and a callee's parameter at the family type
- `D71TesterF33N13`: D2 'static: a Task closure and a stored closure
  capturing a generic value with its instance, reaching Box through a
  generic chain
- `D71TesterF33T24G1`: Pairs of ['Nat', 'Int'] in an existential
- `D71TesterF33T24G2`: Pairs of ['Nat', 'Unit'] in an existential
- `D71TesterF33T24G3`: Pairs of ['Nat', 'Option Nat'] in an existential -/

namespace D71TesterF33N05
@[noinline] def mkQ : (c d : Bool) → if c then List (if d then Nat else String) else Nat
  | true, true => ([1, 2] : List Nat) | true, false => (["a"] : List String) | false, _ => (5 : Nat)
structure K (A : Type) where
  k : List A → Nat
@[noinline] def getS {A : Type} (c : Bool) (x : if c then List A else Nat) (kk : K A) : Nat :=
  match c, x with | true, xs => kk.k xs | false, n => n
@[noinline] def getO {A : Type} (c : Bool) (x : if c then List A else Nat) (k : Option A → Nat) : Nat :=
  match c, x with | true, xs => k xs.head? | false, n => n
@[noinline] def getA {A : Type} (c : Bool) (x : if c then List A else Nat) (k : Array A → Nat) : Nat :=
  match c, x with | true, xs => k xs.toArray | false, n => n
@[noinline] def rdL (d : Bool) (xs : List (if d then Nat else String)) : Nat :=
  match d, xs with | true, ys => (let zs : List Nat := ys; zs.foldl (· + ·) 0) | false, _ => 0
@[noinline] def rdO (d : Bool) (o : Option (if d then Nat else String)) : Nat :=
  match d, o with | true, some n => (show Nat from n) + 1 | _, _ => 0
@[noinline] def rdA (d : Bool) (a : Array (if d then Nat else String)) : Nat :=
  match d with | true => a.size + 50 | false => a.size
def caseMain (a : List String) : IO Unit := do
  let c := a.length < 100
  for d in [a.isEmpty, !a.isEmpty] do
    IO.println s!"{getS (A := if d then Nat else String) c (mkQ c d) ⟨rdL d⟩} {getO (A := if d then Nat else String) c (mkQ c d) (rdO d)} {getA (A := if d then Nat else String) c (mkQ c d) (rdA d)}"
end D71TesterF33N05

namespace D71TesterF33N06
@[noinline] def mkR : (c d : Bool) → if c then (if d then Nat else String) else Nat
  | true, true => (7 : Nat) | true, false => ("a" : String) | false, _ => (5 : Nat)
@[noinline] def inner {A : Type} (c : Bool) (x : if c then A else Nat) (k : A → Nat) : Nat :=
  match c, x with | true, y => k y | false, n => n
@[noinline] def outer {B : Type} (c : Bool) (x : if c then B else Nat) (k : B → Nat) : Nat :=
  let g := fun (z : B) => k z + 1
  inner (A := B) c x g
@[noinline] def rdN (d : Bool) (x : if d then Nat else String) : Nat :=
  match d, x with | true, n => (show Nat from n) + 1 | false, s => (show String from s).length + 10
def caseMain (a : List String) : IO Unit := do
  let c := a.length < 100
  for d in [a.isEmpty, !a.isEmpty] do
    IO.println s!"{outer (B := if d then Nat else String) c (mkR c d) (rdN d)}"
end D71TesterF33N06

namespace D71TesterF33N07
structure SO (α : Type) where
  o : Option α
  tag : Nat
structure SP (α : Type) where
  p : α × Nat
structure SE (α : Type) where
  e : Except String α
structure SA (α : Type) where
  a : Array α
@[noinline] def dupO {α : Type} (s : SO α) : SO α × SO α := (s, s)
@[noinline] def dupP {α : Type} (s : SP α) : SP α × SP α := (s, s)
@[noinline] def dupE {α : Type} (s : SE α) : SE α × SE α := (s, s)
@[noinline] def dupA {α : Type} (s : SA α) : SA α × SA α := (s, s)
@[noinline] def lenO : SO (List Nat) → Nat | ⟨some l, t⟩ => l.length + t | ⟨none, t⟩ => t
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let l := List.range n
  let (a, b) := dupO ⟨some l, n⟩
  let (c, d) := dupP ⟨(l, n)⟩
  let (e, f) := dupE ⟨.ok l⟩
  let (g, h) := dupA ⟨#[l, l.reverse]⟩
  let ev : Nat := match e.e, f.e with | .ok x, .ok y => x.length + y.length | _, _ => 0
  IO.println s!"{lenO a + lenO b} {c.p.1.length + d.p.2} {ev} {g.a.size + (h.a.map (·.length)).foldl (· + ·) 0}"
end D71TesterF33N07

namespace D71TesterF33N08
structure Cache (α : Type) where
  r : IO.Ref α
  n : Nat
structure Lazy (α : Type) where
  t : Thunk α
  k : Task α
structure Pr (α : Type) where
  p : IO.Promise α
@[noinline] def dupC {α : Type} (c : Cache α) : Cache α × Cache α := (c, c)
@[noinline] def dupL {α : Type} (c : Lazy α) : Lazy α × Lazy α := (c, c)
@[noinline] def dupP {α : Type} (c : Pr α) : Pr α × Pr α := (c, c)
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let r ← IO.mkRef (List.range n)
  let (c1, c2) := dupC ⟨r, n⟩
  c1.r.modify (· ++ [100])
  let x ← c2.r.get
  let (l1, l2) := dupL ⟨Thunk.mk fun _ => List.range (n + 1), Task.spawn fun _ => List.range (n + 2)⟩
  let p ← IO.Promise.new
  let (p1, p2) := dupP (α := List Nat) ⟨p⟩
  p1.p.resolve (List.range (n + 3))
  IO.println s!"{x} {c1.n + c2.n} {l1.t.get.length + l2.t.get.length} {l1.k.get.length + l2.k.get.length} {p2.p.result!.get}"
end D71TesterF33N08

namespace D71TesterF33N09
inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
inductive Op : Type → Type where
  | n : Op Nat
  | s : Op String
@[noinline] def run : FreeM Op Nat → Nat
  | .pure a => a
  | .liftBind .n k => run (k 3)
  | .liftBind .s k => run (k "ab")
@[noinline] def prog (m : Nat) : FreeM Op Nat := .liftBind .n fun a => .liftBind .s fun s => .pure (a * m + s.length)
structure Holder where
  p : FreeM Op Nat
  l : List (List Nat)
@[noinline] def dupH (h : Holder) : Holder × Holder := (h, h)
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let (a, b) := dupH ⟨prog n, [List.range n, [n]]⟩
  IO.println s!"{run a.p + run b.p} {a.l.length + b.l.length} {(dupH a).1.l}"
end D71TesterF33N09

namespace D71TesterF33N10
structure AnyF where
  {α : Type}
  f : Unit → α
  sh : α → String
@[noinline] def pack {β : Type} [ToString β] (x : β) : AnyF := ⟨fun _ => x, toString⟩
@[noinline] def packL {β : Type} [ToString β] (xs : List β) : AnyF := ⟨fun _ => xs.reverse, toString⟩
@[noinline] def thunkOf {β : Type} (x : β) (k : β → String) : Thunk String := Thunk.mk fun _ => k x
@[noinline] def AnyF.run (a : AnyF) : String := a.sh (a.f ())
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let xs : List AnyF := [pack n, pack s!"s{n}", packL (List.range n), packL [s!"a{n}"], pack (n, decide (n > 2))]
  IO.println (xs.map (·.run))
  IO.println s!"{(thunkOf (List.range n) toString).get} {(thunkOf s!"q{n}" id).get}"
end D71TesterF33N10

namespace D71TesterF33N11
structure F2 (d : Bool) where
  xs : List (if d then Nat else String)
  k : Nat
@[noinline] def mkQ : (c d : Bool) → if c then List (if d then Nat else String) else Nat
  | true, true => ([1, 2, 9] : List Nat) | true, false => (["a"] : List String) | false, _ => (5 : Nat)
@[noinline] def useF (d : Bool) (f : F2 d) : Nat :=
  match d, f with | true, ⟨ys, k⟩ => (let zs : List Nat := ys; zs.foldl (· + ·) k) | false, ⟨ys, k⟩ => ys.length + k * 10
@[noinline] def getC : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, d, xs =>
    let ys := List.map id (xs : List (if d then Nat else String))
    useF d ⟨ys, 3⟩ + useF d ⟨(xs : List (if d then Nat else String)).take 1, 4⟩
  | false, _, n => n
def caseMain (a : List String) : IO Unit := do
  let c := a.length < 100
  for d in [a.isEmpty, !a.isEmpty] do
    IO.println s!"{getC c d (mkQ c d)}"
end D71TesterF33N11

namespace D71TesterF33N13
structure AnyT where
  {α : Type}
  [inst : ToString α]
  t : Task α
@[noinline] def spawnOf {β : Type} [ToString β] (x : β) (f : β → β) : AnyT := ⟨Task.spawn fun _ => f x⟩
@[noinline] def twice {γ : Type} [ToString γ] (x : γ) (f : γ → γ) : List AnyT := [spawnOf x f, spawnOf (f x) f]
@[noinline] def AnyT.show (a : AnyT) : String := a.inst.toString a.t.get
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let pre := s!"p{n}"
  let xs := twice n (· * 2) ++ twice "a" (· ++ pre) ++ twice (n, decide (n > 1)) (fun p => (p.1 + 1, !p.2))
  IO.println (xs.map (·.show))
end D71TesterF33N13

namespace D71TesterF33T24G1
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let xs : List AnyS := [
    ⟨((n : Nat), (n : Nat))⟩,
    ⟨((n : Nat), ((n : Int) : Int))⟩,
    ⟨(((n : Int) : Int), (n : Nat))⟩,
    ⟨(((n : Int) : Int), ((n : Int) : Int))⟩]
  IO.println (xs.map (·.show))
end D71TesterF33T24G1

namespace D71TesterF33T24G2
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let xs : List AnyS := [
    ⟨((n : Nat), (n : Nat))⟩,
    ⟨((n : Nat), (() : Unit))⟩,
    ⟨((() : Unit), (n : Nat))⟩,
    ⟨((() : Unit), (() : Unit))⟩]
  IO.println (xs.map (·.show))
end D71TesterF33T24G2

namespace D71TesterF33T24G3
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let xs : List AnyS := [
    ⟨((n : Nat), (n : Nat))⟩,
    ⟨((n : Nat), (some n : Option Nat))⟩,
    ⟨((some n : Option Nat), (n : Nat))⟩,
    ⟨((some n : Option Nat), (some n : Option Nat))⟩]
  IO.println (xs.map (·.show))
end D71TesterF33T24G3

def main : IO Unit := do
  IO.println "-- D71TesterF33N05"
  D71TesterF33N05.caseMain ["a", "b"]
  IO.println "-- D71TesterF33N06"
  D71TesterF33N06.caseMain ["a", "b"]
  IO.println "-- D71TesterF33N07"
  D71TesterF33N07.caseMain ["4"]
  IO.println "-- D71TesterF33N08"
  D71TesterF33N08.caseMain ["4"]
  IO.println "-- D71TesterF33N09"
  D71TesterF33N09.caseMain ["4"]
  IO.println "-- D71TesterF33N10"
  D71TesterF33N10.caseMain ["4"]
  IO.println "-- D71TesterF33N11"
  D71TesterF33N11.caseMain ["a", "b"]
  IO.println "-- D71TesterF33N13"
  D71TesterF33N13.caseMain ["4"]
  IO.println "-- D71TesterF33T24G1"
  D71TesterF33T24G1.caseMain ["3"]
  IO.println "-- D71TesterF33T24G2"
  D71TesterF33T24G2.caseMain ["3"]
  IO.println "-- D71TesterF33T24G3"
  D71TesterF33T24G3.caseMain ["3"]
