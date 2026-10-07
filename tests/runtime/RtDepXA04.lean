import Std.Data.HashMap
import Std.Data.HashSet
/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `A1074`: The D71 breaker's probe P11C (068c02704).
- `A1075`: The D71 breaker's probe P30A (068c02704).
- `A1076`: The D71 breaker's probe P31 (068c02704). Each line is Lean's
  output.
- `A1077`: The D71 breaker's probe P23 (068c02704). Each line is Lean's
  output.
- `A1078`: The D71 breaker's probe P14 (068c02704). Each line is Lean's
  output.
- `A1079`: The D71 breaker's probe P16 (068c02704). Each line is Lean's
  output.
- `A1080`: Check at a generic unboxing site: `getG {A}` unboxes `x` at `List
  A`
- `A1081`: Check at a bare generic unboxing site: `getG2 {A}` unboxes `x` at
  `A` itself
- `A1082`: (ii)'s site rule at value-refined reads: each function unboxes a
  list whose element's Lean type at the reading site is the family `if d
  then Nat else ...
- `A1083`: (ii)'s site rule at generic reads: `getG5 {A}` returns the head
  of a list it unboxes at `List A`, instantiated at `if d then Nat else
  String` by a ...
- `A1084`: The benchmark's L18 (`hashmap`, lean2rr's classic corpus) at
  small sizes: T15 step B2 (iii) at one empty map `{}`, a closed term Lean
  shares between `HashMap Nat Nat`, `HashMap String Nat`, `HashMap Point ... -/

namespace A1074

/- P11C: minimal Cont at two answer types -/
def Cont (r α : Type) := (α → r) → r
@[noinline] def Cont.ret (a : α) : Cont r α := fun k => k a
@[noinline] def Cont.bind (m : Cont r α) (f : α → Cont r β) : Cont r β := fun k => m (fun a => f a k)
@[noinline] def Cont.run (m : Cont r r) : r := m id
@[noinline] def sumTo (n : Nat) : Cont r Nat :=
  match n with
  | 0 => Cont.ret 0
  | k + 1 => (sumTo k).bind (fun s => Cont.ret (s + k + 1))
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println ((sumTo n).run)
  IO.println (((sumTo n).bind (fun s => Cont.ret (toString s ++ "!"))).run)
end A1074

namespace A1075

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
  IO.println s!"{useGen emptyGen n n} {useGen emptyGen (toString n) n}"
end A1075

namespace A1076

/- P31: closed shared containers inside records (maps, arrays, thunks, tasks) read at two types -/
open Std
structure Bag (κ ν : Type) [BEq κ] [Hashable κ] where
  m : HashMap κ ν
  a : Array ν
  t : Thunk (List κ)
  k : Task (Option ν)
def emptyBag {κ ν : Type} [BEq κ] [Hashable κ] : Bag κ ν := ⟨{}, #[], Thunk.pure [], Task.pure none⟩
@[noinline] def fillBag [BEq κ] [Hashable κ] (b : Bag κ ν) (k : κ) (v : ν) : Bag κ ν :=
  ⟨b.m.insert k v, b.a.push v, Thunk.mk (fun _ => k :: b.t.get), b.k.map (fun _ => some v)⟩
@[noinline] def showBag [BEq κ] [Hashable κ] [ToString κ] [ToString ν] (b : Bag κ ν) : String :=
  s!"{b.m.size} {b.a} {b.t.get} {b.k.get}"
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let b1 : Bag Nat String := (List.range n).foldl (fun b i => fillBag b i (toString i)) emptyBag
  let b2 : Bag String Nat := (List.range n).foldl (fun b i => fillBag b (toString i) i) emptyBag
  let b3 : Bag Nat Nat := emptyBag
  IO.println (showBag b1)
  IO.println (showBag b2)
  IO.println (showBag b3)
  IO.println (showBag (fillBag (emptyBag : Bag String String) "k" "v"))
end A1076

namespace A1077

/- P23: HashMaps inside dependent records and existentials (L18 shape through Box). -/
open Std
structure Point where
  x : Nat
  y : Nat
  deriving BEq, Hashable, Repr

structure Idx where
  b : Bool
  m : if b then HashMap Point Nat else HashMap String Nat

@[noinline] def mkIdx (n : Nat) : Idx :=
  if n % 2 = 0 then
    let m : HashMap Point Nat := (List.range n).foldl (fun m i => m.insert (Point.mk i (i % 2)) i) {}
    ⟨true, m⟩
  else
    let m : HashMap String Nat := (List.range n).foldl (fun m i => m.insert (toString i) (i * 2)) {}
    ⟨false, m⟩

@[noinline] def sizeIdx : Idx → Nat
  | ⟨true, m⟩ => let h : HashMap Point Nat := m; h.size + h.getD ⟨0, 0⟩ 100
  | ⟨false, m⟩ => let h : HashMap String Nat := m; h.size + h.getD "1" 100

@[noinline] def addIdx (n : Nat) : Idx → Idx
  | ⟨true, m⟩ => let h : HashMap Point Nat := m; ⟨true, h.insert ⟨n, n⟩ n⟩
  | ⟨false, m⟩ => let h : HashMap String Nat := m; ⟨false, h.insert s!"k{n}" n⟩

structure AnyMap where
  {κ : Type}
  [beq : BEq κ]
  [hsh : Hashable κ]
  m : HashMap κ Nat
  keyOf : Nat → κ

@[noinline] def AnyMap.add (n : Nat) (a : AnyMap) : AnyMap :=
  let k := a.keyOf n
  { a with m := @HashMap.insert a.κ Nat a.beq a.hsh a.m k (@HashMap.getD a.κ Nat a.beq a.hsh a.m k 0 + n) }
@[noinline] def AnyMap.total (a : AnyMap) : Nat := @HashMap.fold a.κ Nat a.beq a.hsh Nat (fun acc _ v => acc + v) 0 a.m
@[noinline] def AnyMap.size (a : AnyMap) : Nat := @HashMap.size a.κ Nat a.beq a.hsh a.m

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ids := (List.range (n + 2)).map mkIdx
  IO.println (ids.map sizeIdx)
  IO.println ((ids.map (addIdx n)).map sizeIdx)
  let ams : List AnyMap := [AnyMap.mk (κ := Point) {} (fun i => ⟨i % 2, 0⟩), AnyMap.mk (κ := String) {} (fun i => toString (i % 3)), AnyMap.mk (κ := Nat) {} id]
  let ams := (List.range n).foldl (fun as i => as.map (AnyMap.add i)) ams
  IO.println (ams.map AnyMap.total)
  IO.println (ams.map AnyMap.size)
end A1077

namespace A1078

/- P14: closed function values and partial applications shared at two types; closed data in let-bound lambdas. -/
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

@[noinline] def mkFns (n : Nat) : Fns := if n % 2 = 0 then ⟨true, revAll⟩ else ⟨false, dupHead⟩
@[noinline] def useFns (f : Fns) : String := match f with
  | ⟨true, g⟩ => let h : List Nat → List Nat := g; toString (h [1, 2, 3])
  | ⟨false, g⟩ => let h : List String → List String := g; toString (h ["a", "b"])

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let s := toString n
  IO.println s!"{ap flipPair (n, s)} {ap flipPair (s, n)} {ap flipPair (n, n)}"
  IO.println s!"{apL revAll (List.range n)} {apL revAll [s, "x"]} {apL dupHead (List.range n)} {apL dupHead [s]}"
  IO.println s!"{ap2 pickFst n 1} {ap2 pickFst s "y"} {ap wrapOpt n} {ap wrapOpt s}"
  IO.println s!"{(ap constNone n : Option String)} {(ap constNone s : Option Nat)}"
  IO.println s!"{ap (List.map toString) (List.range n)} {ap (List.map String.length) [s, "abc"]}"
  IO.println s!"{ap (fun xs => (xs.reverse, xs.length)) (List.range n)} {ap (fun xs => (xs.reverse, xs.length)) [s]}"
  IO.println (((List.range (n + 2)).map mkFns).map useFns)
end A1078

namespace A1079

/- P16: a type universe with arrows: denote (arrow a b) = a.denote → b.denote; typed evaluator with environments. -/
inductive Ty where
  | nat | str
  | arrow : Ty → Ty → Ty
  | pair : Ty → Ty → Ty

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat | .str => String
  | .arrow a b => a.denote → b.denote
  | .pair a b => a.denote × b.denote

inductive Tm : Ty → Type where
  | lit : Nat → Tm .nat
  | slit : String → Tm .str
  | lam : (a.denote → Tm b) → Tm (.arrow a b)
  | app : Tm (.arrow a b) → Tm a → Tm b
  | mk : Tm a → Tm b → Tm (.pair a b)
  | fst : Tm (.pair a b) → Tm a
  | plus : Tm .nat → Tm .nat → Tm .nat
  | len : Tm .str → Tm .nat
  | rep : Tm .nat → Tm .str → Tm .str

@[noinline] def Tm.eval : Tm t → t.denote
  | .lit n => n
  | .slit s => s
  | .lam f => fun x => (f x).eval
  | .app f a => f.eval a.eval
  | .mk a b => (a.eval, b.eval)
  | .fst p => p.eval.1
  | .plus a b => a.eval + b.eval
  | .len s => s.eval.length
  | .rep n s => String.join (List.replicate n.eval s.eval)

@[noinline] def Ty.show : (t : Ty) → t.denote → String
  | .nat, n => toString n
  | .str, s => s
  | .arrow _ _, _ => "<fn>"
  | .pair a b, (x, y) => s!"({a.show x}, {b.show y})"

def Any := (t : Ty) × t.denote

@[noinline] def twice : Tm (.arrow (.arrow .nat .nat) (.arrow .nat .nat)) :=
  .lam fun f => .lam fun x => .lit (f (f x))

@[noinline] def mkAny (n : Nat) : Any :=
  match n % 4 with
  | 0 => ⟨.nat, (Tm.app (.app twice (.lam fun x => .plus (.lit x) (.lit n))) (.lit 1)).eval⟩
  | 1 => ⟨.arrow .nat .str, (Tm.lam fun x => .rep (.lit x) (.slit (toString n))).eval⟩
  | 2 => ⟨.pair .nat .str, (Tm.mk (.len (.slit "abc")) (.slit s!"n{n}")).eval⟩
  | _ => ⟨.arrow .str .nat, fun s => s.length + n⟩

@[noinline] def useAny (a : Any) : String :=
  match a with
  | ⟨.arrow .nat .str, f⟩ => (f : Nat → String) 3
  | ⟨.arrow .str .nat, f⟩ => toString ((f : String → Nat) "hello")
  | ⟨t, v⟩ => t.show v

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println ((Tm.app (.app twice (.lam fun x => .plus (.lit x) (.lit n))) (.lit 1)).eval)
  for i in List.range (n + 4) do IO.println (useAny (mkAny i))
  let fs : List Any := [mkAny 1, mkAny 3, mkAny 1]
  IO.println (fs.map useAny)
end A1079

namespace A1080

@[noinline] def rdL (d : Bool) (xs : List (if d then Nat else String)) : Nat :=
  match d, xs with | true, ys => (let zs : List Nat := ys; zs.foldl (· + ·) 0) | false, _ => 0
@[noinline] def mkQ : (c d : Bool) → if c then List (if d then Nat else String) else Nat
  | true, true => ([1, 2] : List Nat) | true, false => (["a"] : List String) | false, _ => (5 : Nat)
@[noinline] def getG {A : Type} (c : Bool) (x : if c then List A else Nat) (k : List A → Nat) : Nat :=
  match c, x with | true, xs => k xs | false, n => n
def caseMain (a : List String) : IO Unit :=
  let c := a.length < 100
  let d := a.isEmpty
  IO.println (getG (A := if d then Nat else String) c (mkQ c d) (rdL d))
end A1080

namespace A1081

@[noinline] def rdN (d : Bool) (x : if d then Nat else String) : Nat :=
  match d, x with | true, n => (show Nat from n) + 1 | false, _ => 0
@[noinline] def mkR : (c d : Bool) → if c then (if d then Nat else String) else Nat
  | true, true => (7 : Nat) | true, false => ("a" : String) | false, _ => (5 : Nat)
@[noinline] def getG2 {A : Type} (c : Bool) (x : if c then A else Nat) (k : A → Nat) : Nat :=
  match c, x with | true, y => k y | false, n => n
def caseMain (a : List String) : IO Unit :=
  let c := a.length < 100
  let d := a.isEmpty
  IO.println (getG2 (A := if d then Nat else String) c (mkR c d) (rdN d))
end A1081

namespace A1082

@[noinline] def mkQ : (c d : Bool) → if c then List (if d then Nat else String) else Nat
  | true, true => ([1, 2] : List Nat) | true, false => (["a"] : List String) | false, _ => (5 : Nat)
-- (1) match on d after the read
@[noinline] def getH : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, d, xs => match xs with
    | [] => 0
    | h :: _ => match d, h with | true, n => (let m : Nat := n; m + 1) | false, _ => 7
  | false, _, n => n
-- (2) the read under d's refinement (typed read)
@[noinline] def getH2 : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, true, xs => match xs with
    | [] => 0
    | h :: _ => (let m : Nat := h; m + 1)
  | true, false, _ => 7
  | false, _, n => n
-- (3) dependent if (dite) after the read
@[noinline] def getI : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, d, xs => match xs with
    | [] => 0
    | h :: _ => if hd : d = true then (let m : Nat := (by subst hd; exact h); m + 2) else 8
  | false, _, n => n
-- (4) decide with a cast after the read
@[noinline] def getD : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, d, xs => match xs with
    | [] => 0
    | h :: _ => match hd : decide (d = true) with
      | true => (let m : Nat := cast (by rw [of_decide_eq_true hd]; rfl) h; m + 3)
      | false => 9
  | false, _, n => n
-- (5) a dependent pair read by dependent pattern matching
@[noinline] def mkS : (c d : Bool) → if c then ((e : Bool) × List (if e then Nat else String)) else Nat
  | true, true => ⟨true, ([4, 5] : List Nat)⟩ | true, false => ⟨false, (["b"] : List String)⟩ | false, _ => (6 : Nat)
@[noinline] def getS : (c : Bool) → (if c then ((e : Bool) × List (if e then Nat else String)) else Nat) → Nat
  | true, ⟨e, xs⟩ => match xs with
    | [] => 0
    | h :: _ => match e, h with | true, n => (let m : Nat := n; m + 4) | false, _ => 10
  | false, n => n
-- (6) a subtype
@[noinline] def mkT : (c d : Bool) → if c then {xs : List (if d then Nat else String) // xs.length > 0} else Nat
  | true, true => ⟨([7] : List Nat), by decide⟩ | true, false => ⟨(["c"] : List String), by decide⟩ | false, _ => (8 : Nat)
@[noinline] def getT : (c d : Bool) → (if c then {xs : List (if d then Nat else String) // xs.length > 0} else Nat) → Nat
  | true, d, ⟨xs, _⟩ => match xs with
    | [] => 0
    | h :: _ => match d, h with | true, n => (let m : Nat := n; m + 5) | false, _ => 11
  | false, _, n => n
-- (7) a Nat-indexed family
def T : Nat → Type | 0 => Nat | n + 1 => List (T n)
@[noinline] def mkF : (k : Nat) → T k
  | 0 => (3 : Nat) | 1 => ([(4 : Nat)] : List Nat) | n + 2 => ([[]] : List (List (T n)))
@[noinline] def getF : (k : Nat) → T (k + 1) → Nat
  | k, x => match (x : List (T k)) with
    | [] => 0
    | h :: _ => match k, h with | 0, n => (let m : Nat := n; m + 6) | _ + 1, _ => 12
-- a lambda typing the element under a refinement, mapped over the read list
@[noinline] def getL : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, d, xs => ((show List (if d then Nat else String) from xs).map (fun h => match d, h with | true, n => (let m : Nat := n; m + 1) | false, _ => 7)).foldl (· + ·) 0
  | false, _, n => n
-- a fold whose step types the element under a refinement
@[noinline] def getL2 : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, d, xs => (show List (if d then Nat else String) from xs).foldl (fun acc h => match d, h with | true, n => acc + (show Nat from n) | false, _ => acc + 7) 0
  | false, _, n => n
-- a local helper taking the element at its family type
@[noinline] def elemVal (d : Bool) (h : if d then Nat else String) : Nat :=
  match d, h with | true, n => (show Nat from n) + 3 | false, s => (show String from s).length
@[noinline] def getL3 : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, d, xs => match xs with | [] => 0 | h :: _ => elemVal d h
  | false, _, n => n
-- an element passed on through a let-bound list (upstream chain), read under a refinement
@[noinline] def getL4 : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, d, xs => let ys := (show List (if d then Nat else String) from xs).reverse; match ys with | [] => 0 | h :: _ => match d, h with | true, n => (show Nat from n) + 4 | false, _ => 8
  | false, _, n => n
-- an empty list of a family type appended to the read list, the element typed downstream
@[noinline] def getL5 : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, d, xs =>
    let e : List (if d then Nat else String) := []
    match (show List (if d then Nat else String) from xs) ++ e with | [] => 0 | h :: _ => match d, h with | true, n => (show Nat from n) + 5 | false, _ => 9
  | false, _, n => n
def main2 (a : List String) : IO Unit := do
  let c := a.length < 100
  for d in [a.isEmpty, !a.isEmpty] do
    IO.println s!"{getL c d (mkQ c d)} {getL2 c d (mkQ c d)} {getL3 c d (mkQ c d)} {getL4 c d (mkQ c d)} {getL5 c d (mkQ c d)}"
structure P2 (α : Type) where
  fst : List α
  snd : Nat
@[noinline] def mkP : (c d : Bool) → if c then P2 (if d then Nat else String) else Nat
  | true, true => (⟨[1, 2], 3⟩ : P2 Nat) | true, false => (⟨["a"], 4⟩ : P2 String) | false, _ => (5 : Nat)
-- a projection off the read structure, its element typed under a later refinement
@[noinline] def getP : (c d : Bool) → (if c then P2 (if d then Nat else String) else Nat) → Nat
  | true, d, p => (show P2 (if d then Nat else String) from p).snd + (match (show P2 (if d then Nat else String) from p).fst with
      | [] => 0 | h :: _ => match d, h with | true, n => (show Nat from n) + 1 | false, _ => 7)
  | false, _, n => n
-- a local function value applied to the read list
@[noinline] def getK : (c d : Bool) → (k : List (if d then Nat else String) → Nat) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, _, k, xs => k xs
  | false, _, _, n => n
@[noinline] def headK (d : Bool) (xs : List (if d then Nat else String)) : Nat :=
  match xs with | [] => 0 | h :: _ => match d, h with | true, n => (show Nat from n) + 2 | false, _ => 8
-- a pair projection of a read pair
@[noinline] def mkR : (c d : Bool) → if c then (List (if d then Nat else String) × Nat) else Nat
  | true, true => (([3] : List Nat), 1) | true, false => ((["b"] : List String), 2) | false, _ => (6 : Nat)
@[noinline] def getR : (c d : Bool) → (if c then (List (if d then Nat else String) × Nat) else Nat) → Nat
  | true, d, p => match (show List (if d then Nat else String) × Nat from p).1 with
      | [] => 0 | h :: _ => match d, h with | true, n => (show Nat from n) + 3 | false, _ => 9
  | false, _, n => n
def main3 (a : List String) : IO Unit := do
  let c := a.length < 100
  for d in [a.isEmpty, !a.isEmpty] do
    IO.println s!"{getP c d (mkP c d)} {getK c d (headK d) (mkQ c d)} {getR c d (mkR c d)}"
-- a join point parameter whose `true` jump passes a list refined to `List Nat`
@[noinline] def getJ : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, d, xs =>
    let ys : List (if d then Nat else String) := match d, xs with
      | true, zs => (show List Nat from zs).map (· + 1)
      | false, zs => zs
    match ys with | [] => 0 | h :: _ => match d, h with | true, n => (show Nat from n) + 1 | false, _ => 7
  | false, _, n => n
-- a function value at the family type mapped over the read list (a wrapper unboxing at its domain)
@[noinline] def getW : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, d, xs => ((show List (if d then Nat else String) from xs).map (elemVal d)).foldl (· + ·) 0
  | false, _, n => n
@[noinline] def rdL (d : Bool) (xs : List (if d then Nat else String)) : Nat :=
  match d, xs with | true, ys => (let zs : List Nat := ys; zs.foldl (· + ·) 0) | false, _ => 0
@[noinline] def app {α : Type} (f : α → Nat) (x : α) : Nat := f x
-- `rdL d` passed as a function value to a generic `app`
@[noinline] def getA : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, d, xs => app (rdL d) xs
  | false, _, n => n
def main4 (a : List String) : IO Unit := do
  let c := a.length < 100
  for d in [a.isEmpty, !a.isEmpty] do
    IO.println s!"{getJ c d (mkQ c d)} {getW c d (mkQ c d)} {getA c d (mkQ c d)}"
def caseMain (a : List String) : IO Unit := do
  let c := a.length < 100
  for d in [a.isEmpty, !a.isEmpty] do
    IO.println s!"{getH c d (mkQ c d)} {getH2 c d (mkQ c d)} {getI c d (mkQ c d)} {getD c d (mkQ c d)} {getS c (mkS c d)} {getT c d (mkT c d)}"
  let k := a.length
  IO.println s!"{getF k (mkF (k + 1))} {getF (k + 1) (mkF (k + 2))}"
  main2 a
  main3 a
  main4 a
end A1082

namespace A1083

@[noinline] def mkQ : (c d : Bool) → if c then List (if d then Nat else String) else Nat
  | true, true => ([1, 2] : List Nat) | true, false => (["a"] : List String) | false, _ => (5 : Nat)
-- (1) a generic read whose instantiation is value-dependent, read inline under d
@[noinline] def getG5 {A : Type} (c : Bool) (x : if c then List A else Nat) : Option A :=
  match c, x with | true, xs => xs.head? | false, _ => none
-- (2) a family inside a generic, its result typed only under d
@[noinline] def getG7 {A : Type} (c d : Bool) (x : if c then List (if d then A else String) else Nat) : List A :=
  match c, x with
  | true, xs => (match d, xs.head? with | true, some a => [a, a] | _, _ => [])
  | false, _ => []
-- (3) a generic read whose instantiation is closed
@[noinline] def viaClosed (c : Bool) : Nat :=
  match getG5 (A := Nat) c (mkQ c true) with | some n => n + 1 | none => 0
-- (4) a generic caller passing its own type parameter
@[noinline] def viaGen {B : Type} (c : Bool) (x : if c then List B else Nat) (f : B → Nat) : Nat :=
  match getG5 (A := B) c x with | some b => f b | none => 0
mutual
@[noinline] def mf {A : Type} : Nat → (c : Bool) → (if c then List A else Nat) → Option A
  | 0, c, x => mg 0 c x
  | n + 1, c, x => mf n c x
@[noinline] def mg {B : Type} : Nat → (c : Bool) → (if c then List B else Nat) → Option B
  | 0, true, xs => xs.head?
  | 0, false, _ => none
  | n + 1, c, x => mf n c x
end
def main2 (a : List String) : IO Unit := do
  let c := a.length < 100
  let k := a.length
  for d in [a.isEmpty, !a.isEmpty] do
    let r := match d, mf (A := if d then Nat else String) k c (mkQ c d) with
      | true, some n => toString ((show Nat from n) + 1)
      | _, _ => "other"
    let r2 := match d, mg (B := if d then Nat else String) (k + 1) c (mkQ c d) with
      | true, some n => toString ((show Nat from n) + 2)
      | _, _ => "other"
    IO.println s!"{r} {r2}"
@[noinline] def mkS : (c : Bool) → if c then List String else Nat
  | true => (["a", "b"] : List String) | false => (3 : Nat)
@[noinline] def fstL {α : Type} (p : List α × Nat) : List α := p.1
-- a closed pair Lean shares between `List String × Nat` and `List Nat × Nat`, appended to a read list
@[noinline] def getS2 : (c : Bool) → (if c then List String else Nat) → Nat
  | true, xs => ((show List String from xs) ++ fstL (([] : List String), 0)).length + (fstL (([] : List Nat), 0)).length
  | false, n => n
@[noinline] def mkE {A : Type} (c : Bool) : if c then List A else Nat := match c with | true => ([] : List A) | false => (0 : Nat)
@[noinline] def useN (o : Option Nat) : Nat := match o with | some n => n + 1 | none => 10
@[noinline] def useS (o : Option String) : Nat := match o with | some s => s.length | none => 20
-- a call Lean merges between `A := Nat` and `A := String`
@[noinline] def merged (c : Bool) : Nat := useN (getG5 (A := Nat) c (mkE c)) + useS (getG5 (A := String) c (mkE c))
def main3 (a : List String) : IO Unit := do
  let c := a.length < 100
  IO.println s!"{getS2 c (mkS c)} {merged c}"
def caseMain (a : List String) : IO Unit := do
  let c := a.length < 100
  for d in [a.isEmpty, !a.isEmpty] do
    let r1 := match d, getG5 (A := if d then Nat else String) c (mkQ c d) with
      | true, some n => toString ((show Nat from n) + 1)
      | _, _ => "other"
    let r2 := match d, getG7 (A := Nat) c d (mkQ c d) with
      | true, [n, _] => toString (n + 2)
      | _, _ => "none"
    let r4 := match d with
      | true => viaGen (B := Nat) c (mkQ c true) (· + 3)
      | false => viaGen (B := String) c (mkQ c false) String.length
    IO.println s!"{r1} {r2} {viaClosed c} {r4}"
  main2 a
  main3 a
end A1083

namespace A1084

open Std

structure Point where
  x : Int
  y : Int
deriving BEq, Hashable, Repr

/-- A bijection on [0, n) when `gcd(a, n) = 1`: `i ↦ (a * i + b) % n`. -/
def perm (a b n i : Nat) : Nat := (a * i + b) % n

def check (b : Bool) : String := if b then "ok" else "FAIL"

def caseMain (args : List String) : IO UInt32 := do
  let n := 40 + args.length * 13
  -- keys k = perm i are a permutation of [0, n) (7919 is prime and does not divide n
  -- unless n is a multiple of 7919; then use 7907)
  let a := if n % 7919 == 0 then 7907 else 7919

  -- 1. Insert n keys (value = 3k + 1), then overwrite every third key.
  let mut m : HashMap Nat Nat := {}
  for i in [0:n] do
    let k := perm a 12345 n i
    m := m.insert k (3 * k + 1)
  for i in [0:n:3] do
    m := m.insert i (2 * i)
  let overwritten := (n + 2) / 3
  -- expected sum of values: sum over k of (3k+1), with k ≡ 0 mod 3 replaced by 2k
  let mut expected := 0
  for k in [0:n] do
    expected := expected + (if k % 3 == 0 then 2 * k else 3 * k + 1)
  let total := m.fold (fun acc _ v => acc + v) 0
  IO.println s!"insert: size={m.size} (n={n}) sum={total} {check (total == expected && m.size == n)} overwritten={overwritten}"

  -- 2. Lookups: hits on every key, misses on [n, 2n).
  let mut hits := 0
  let mut hitSum := 0
  let mut misses := 0
  for k in [0:2 * n] do
    match m[k]? with
    | some v => hits := hits + 1; hitSum := hitSum + v
    | none => misses := misses + 1
  IO.println s!"lookup: hits={hits} misses={misses} {check (hits == n && misses == n && hitSum == expected)} contains={m.contains (n / 2)} {m.contains (n + 7)} getD={m.getD (n + 1) 77} get!={m.get! 3}"

  -- 3. Erase every key divisible by 5 (in a scrambled order), modify the rest.
  for i in [0:n] do
    let k := perm a 999 n i
    if k % 5 == 0 then m := m.erase k
  let erased := (n + 4) / 5
  m := m.modify 1 (· + 1000000)
  m := m.alter 2 (fun | some v => some (v * 10) | none => some 0)
  m := m.alter 5 (fun | some v => some v | none => some 555)     -- 5 was erased: re-inserted
  m := m.alter 7 (fun _ => none)                                -- deletes 7
  m := m.insertIfNew 1 0                                        -- 1 exists: unchanged
  m := m.insertIfNew (n + 3) 42                                 -- new key
  -- erased multiples of 5, then +1 (key 5 re-inserted), -1 (key 7 deleted), +1 (key n+3)
  let expectedSize := n - erased + 1 - 1 + 1
  IO.println s!"erase: size={m.size} {check (m.size == expectedSize)} v1={m[1]?} v2={m[2]?} v5={m[5]?} v7={m[7]?} vnew={m[n + 3]?} v10={m[10]?}"

  -- 4. Iterate with `for`, and check keys/values against the rule.
  let mut bad := 0
  let mut keySum := 0
  let mut orderHash : UInt64 := 0   -- depends on the iteration order
  for (k, v) in m do
    keySum := keySum + k
    orderHash := orderHash * 1000003 + k.toUInt64
    let want :=
      if k == 1 then 3 * 1 + 1 + 1000000
      else if k == 2 then (3 * 2 + 1) * 10
      else if k == 5 then 555
      else if k == n + 3 then 42
      else if k % 3 == 0 then 2 * k
      else 3 * k + 1
    if v != want then bad := bad + 1
  IO.println s!"iterate: keySum={keySum} bad={bad} {check (bad == 0)} orderHash={orderHash}"

  -- 5. String keys: word counts over a generated text.
  let vocab := #["the", "quick", "brown", "fox", "jumps", "over", "lazy", "dog", "λ", "ünïcode", "日本", ""]
  let mut counts : HashMap String Nat := {}
  let mut s : UInt64 := 7
  let words := n / 4
  let mut direct := Array.replicate vocab.size 0
  for _ in [0:words] do
    s := s * 6364136223846793005 + 1442695040888963407
    let j := ((s >>> 33) % vocab.size.toUInt64).toNat
    let w := vocab[j]!
    counts := counts.alter w (fun | some c => some (c + 1) | none => some 1)
    direct := direct.modify j (· + 1)
  let mut agree := true
  for h : j in [0:vocab.size] do
    if counts.getD vocab[j] 0 != direct[j]! then agree := false
  let sorted := counts.toList.toArray.qsort (fun p q => p.1 < q.1)
  IO.println s!"words: distinct={counts.size} total={counts.fold (fun acc _ c => acc + c) 0} agree={check agree} counts={sorted.toList}"

  -- 6. Structure keys and a HashSet.
  let mut grid : HashMap Point Nat := {}
  let side := Nat.sqrt (n / 4) + 1
  for x in [0:side] do
    for y in [0:side] do
      grid := grid.insert ⟨x - side / 2, (y : Int) * 3 - 5⟩ (x * side + y)
  let probe := grid.get? ⟨0, -5⟩
  let mut set : HashSet Nat := {}
  for i in [0:n] do
    set := set.insert ((i * i) % 1009)
  let mut qr := 0
  for i in [0:1009] do
    if set.contains i then qr := qr + 1
  IO.println s!"struct keys: size={grid.size} {check (grid.size == side * side)} probe={probe} set={set.size} qr={qr} {check (qr == set.size)} gridOrder={grid.fold (fun (acc : UInt64) _ v => acc * 31 + v.toUInt64) 0}"
  pure 0
end A1084

def main : IO Unit := do
  IO.println "-- A1074"
  A1074.caseMain ["3"]
  IO.println "-- A1075"
  A1075.caseMain ["3"]
  IO.println "-- A1076"
  A1076.caseMain ["3"]
  IO.println "-- A1077"
  A1077.caseMain ["5"]
  IO.println "-- A1078"
  A1078.caseMain ["2"]
  IO.println "-- A1079"
  A1079.caseMain ["5"]
  IO.println "-- A1080"
  A1080.caseMain ["x"]
  IO.println "-- A1081"
  A1081.caseMain ["x"]
  IO.println "-- A1082"
  A1082.caseMain ["x"]
  IO.println "-- A1083"
  A1083.caseMain ["x"]
  IO.println "-- A1084"
  let c ← A1084.caseMain ["x"]
  IO.println s!"exit {c}"
