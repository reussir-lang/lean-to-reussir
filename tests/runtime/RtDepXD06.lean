/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `D71BreakerP14BC`: P14A
- `D71BreakerP14C`: P14C
- `D71BreakerP14D`: P14D
- `D71BreakerP14E`: Closed function values and partial applications shared
  at two types
- `D71BreakerP15`: Function-type aliases at two instantiations: state-as-
  function, reader, Church lists.
- `D71BreakerP16B`: A function type against Nat at one family position
- `D71BreakerP17`: Closed thunks, tasks, arrays, nested structures shared
  between instantiations
- `D71BreakerP18`: Dependent records in Arrays with modify/set!/swap/pop
  (Lean's box(0) placeholder idioms).
- `D71BreakerP19`: Fin-indexed vectors with get by Fin, function tables Fin
  n → α in a family position.
- `D71BreakerP20`: Existentials with Type fields holding functions and
  nested existentials
- `D71BreakerP21`: Polymorphic recursion whose growing value is a dependent
  record / holds Box positions. -/

namespace D71BreakerP14BC
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
  IO.println s!"{apL revAll (List.range n)} {apL revAll [s, "x"]} {apL dupHead (List.range n)} {apL dupHead [s]}"
  IO.println s!"{ap2 pickFst n 1} {ap2 pickFst s "y"} {ap wrapOpt n} {ap wrapOpt s}"
  IO.println s!"{(ap constNone n : Option String)} {(ap constNone s : Option Nat)}"
end D71BreakerP14BC

namespace D71BreakerP14C
/- P14C -/
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
  IO.println s!"{ap2 pickFst n 1} {ap2 pickFst s "y"} {ap wrapOpt n} {ap wrapOpt s}"
  IO.println s!"{(ap constNone n : Option String)} {(ap constNone s : Option Nat)}"
end D71BreakerP14C

namespace D71BreakerP14D
/- P14D -/
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
  IO.println s!"{ap (List.map toString) (List.range n)} {ap (List.map String.length) [s, "abc"]}"
  IO.println s!"{ap (fun xs => (xs.reverse, xs.length)) (List.range n)} {ap (fun xs => (xs.reverse, xs.length)) [s]}"
end D71BreakerP14D

namespace D71BreakerP14E
/- P14: closed function values and partial applications shared at two types; closed data in let-bound lambdas. -/
@[noinline] def ap (f : α → β) (x : α) : β := f x
@[noinline] def apL (f : List α → List α) (x : List α) : List α := f x
@[noinline] def ap2 (f : α → α → α) (x y : α) : α := f x y

structure Fns where
  b : Bool
  g : if b then (List Nat → List Nat) else (List String → List String)

@[noinline] def mkFns (n : Nat) : Fns := if n % 2 = 0 then ⟨true, fun xs => xs.reverse⟩ else ⟨false, fun xs => xs ++ xs⟩
@[noinline] def useFns (f : Fns) : String := match f with
  | ⟨true, g⟩ => let h : List Nat → List Nat := g; toString (h [1, 2, 3])
  | ⟨false, g⟩ => let h : List String → List String := g; toString (h ["a", "b"])

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println (((List.range (n + 2)).map mkFns).map useFns)
end D71BreakerP14E

namespace D71BreakerP15
/- P15: function-type aliases at two instantiations: state-as-function, reader, Church lists. -/
def StateFn (σ α : Type) := σ → α × σ
@[noinline] def StateFn.pure (a : α) : StateFn σ α := fun s => (a, s)
@[noinline] def StateFn.bind (m : StateFn σ α) (f : α → StateFn σ β) : StateFn σ β := fun s => let (a, s') := m s; f a s'
@[noinline] def StateFn.get : StateFn σ σ := fun s => (s, s)
@[noinline] def StateFn.put (s : σ) : StateFn σ Unit := fun _ => ((), s)
@[noinline] def StateFn.run (m : StateFn σ α) (s : σ) : α × σ := m s

@[noinline] def tick (f : σ → σ) : Nat → StateFn σ (List σ)
  | 0 => StateFn.pure []
  | n + 1 => StateFn.get.bind (fun s => (StateFn.put (f s)).bind (fun _ => (tick f n).bind (fun r => StateFn.pure (s :: r))))

def Church (α : Type) := {r : Type} → (α → r → r) → r → r
@[noinline] def toChurch (xs : List α) : (α → r → r) → r → r := fun c n => xs.foldr c n
@[noinline] def lenC (c : (α → Nat → Nat) → Nat → Nat) : Nat := c (fun _ k => k + 1) 0
@[noinline] def strC (c : (α → String → String) → String → String) (sh : α → String) : String := c (fun a acc => sh a ++ "," ++ acc) "."

def Reader (ρ α : Type) := ρ → α
@[noinline] def Reader.ask : Reader ρ ρ := id
@[noinline] def Reader.local (f : ρ → ρ) (m : Reader ρ α) : Reader ρ α := fun r => m (f r)
@[noinline] def Reader.map (g : α → β) (m : Reader ρ α) : Reader ρ β := fun r => g (m r)

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println ((tick (· + 2) n).run n)
  IO.println ((tick (· ++ "a") n).run (toString n))
  IO.println ((tick (fun (p : Nat × String) => (p.1 + 1, p.2 ++ "x")) n).run (n, "p"))
  IO.println s!"{lenC (toChurch (List.range n))} {lenC (toChurch [toString n])} {strC (toChurch (List.range n)) toString} {strC (toChurch ["a", toString n]) id}"
  IO.println s!"{(Reader.local (· + 1) (Reader.map toString Reader.ask)) n} {(Reader.local (· ++ "!") (Reader.map String.length Reader.ask)) (toString n)}"
end D71BreakerP15

namespace D71BreakerP16B
/- P16B: a function type against Nat at one family position -/
structure F where
  b : Bool
  v : if b then Nat else (Nat → Nat)
@[noinline] def mkF (n : Nat) : F := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, (· + n)⟩
@[noinline] def rdF : F → Nat
  | ⟨true, v⟩ => let k : Nat := v; k
  | ⟨false, v⟩ => let g : Nat → Nat := v; g 10
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 2
  IO.println ((List.range (n + 2)).map (fun i => rdF (mkF i)))
end D71BreakerP16B

namespace D71BreakerP17
/- P17: closed thunks, tasks, arrays, nested structures shared between instantiations; read through generics. -/
@[noinline] def forceLen (t : Thunk (List α)) : Nat := t.get.length
@[noinline] def taskLen (t : Task (List α)) : Nat := t.get.length
@[noinline] def arrLen (a : Array α) : Nat := a.size
@[noinline] def trip (p : Option α × List β × Array γ) : Nat := (if p.1.isSome then 1 else 0) + p.2.1.length + p.2.2.size
@[noinline] def pushT (t : Thunk (List α)) (x : α) : Thunk (List α) := Thunk.mk (fun _ => x :: t.get)
@[noinline] def pushTask (t : Task (List α)) (x : α) : Task (List α) := t.map (x :: ·)
@[noinline] def fill (p : Option α × List β × Array γ) (a : α) (b : β) (c : γ) : Option α × List β × Array γ := (some a, b :: p.2.1, p.2.2.push c)

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let s := toString n
  IO.println s!"{forceLen (Thunk.mk fun _ => ([] : List Nat))} {forceLen (Thunk.mk fun _ => ([] : List String))}"
  IO.println s!"{forceLen (pushT (Thunk.mk fun _ => []) n)} {forceLen (pushT (Thunk.mk fun _ => []) s)}"
  IO.println s!"{(pushT (pushT (Thunk.pure []) n) (n+1)).get} {(pushT (pushT (Thunk.pure []) s) "t").get}"
  IO.println s!"{taskLen (Task.pure ([] : List Nat))} {taskLen (Task.pure ([] : List String))}"
  IO.println s!"{(pushTask (Task.pure []) n).get} {(pushTask (Task.pure []) s).get}"
  IO.println s!"{arrLen (#[] : Array Nat)} {arrLen (#[] : Array String)} {(#[] : Array Nat).push n} {(#[] : Array String).push s}"
  IO.println s!"{trip ((none, [], #[]) : Option Nat × List String × Array Nat)} {trip ((none, [], #[]) : Option String × List Nat × Array String)}"
  IO.println s!"{fill (none, [], #[]) n s n} {fill (none, [], #[]) s n s}"
  let e1 : Option Nat × List String × Array Nat := (none, [], #[])
  let e2 : Option String × List Nat × Array String := (none, [], #[])
  IO.println s!"{fill e1 n s n} {fill e2 s n s} {trip e1} {trip e2}"
end D71BreakerP17

namespace D71BreakerP18
/- P18: dependent records in Arrays with modify/set!/swap/pop (Lean's box(0) placeholder idioms). -/
structure Pkg where
  b : Bool
  v : if b then Nat else String

instance : Inhabited Pkg := ⟨⟨true, (0 : Nat)⟩⟩

@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
@[noinline] def swap : Pkg → Pkg
  | ⟨true, v⟩ => let w : Nat := v; ⟨false, toString w⟩
  | ⟨false, v⟩ => let s : String := v; ⟨true, s.length⟩
@[noinline] def showP : Pkg → String
  | ⟨true, v⟩ => let w : Nat := v; s!"N{w}"
  | ⟨false, v⟩ => let s : String := v; s!"S{s}"

@[noinline] def step (a : Array Pkg) (i : Nat) : Array Pkg :=
  let a := a.modify (i % a.size) swap
  let a := if a.size > 1 then a.swapIfInBounds 0 (a.size - 1) else a
  let a := a.set! (i % a.size) (swap a[i % a.size]!)
  a

@[noinline] partial def popAll (a : Array Pkg) : List String :=
  match a.back? with
  | none => []
  | some p => showP p :: popAll a.pop

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let mut a := (List.range (n + 1)).toArray.map mk
  for i in List.range n do a := step a i
  IO.println (a.map showP)
  IO.println (popAll a)
  let b := a.push ⟨false, "end"⟩
  IO.println (b.map showP)
  let c := a.modify 0 (fun _ => ⟨true, (77 : Nat)⟩)
  IO.println (c.map showP)
  IO.println ((a.modify 0 swap).map showP)
  let shared := a
  let d := a.modify 0 swap
  IO.println s!"{shared.map showP} {d.map showP}"
end D71BreakerP18

namespace D71BreakerP19
/- P19: Fin-indexed vectors with get by Fin, function tables Fin n → α in a family position. -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

@[noinline] def Vec.get : Vec α n → Fin n → α
  | .cons a _, ⟨0, _⟩ => a
  | .cons _ v, ⟨i + 1, h⟩ => v.get ⟨i, Nat.lt_of_succ_lt_succ h⟩

@[noinline] def Vec.ofFn : (n : Nat) → (Fin n → α) → Vec α n
  | 0, _ => .nil
  | n + 1, f => .cons (f 0) (Vec.ofFn n (fun i => f i.succ))

@[noinline] def Vec.toList : Vec α n → List α
  | .nil => []
  | .cons a v => a :: v.toList

structure Table where
  b : Bool
  n : Nat
  f : Fin n → (if b then Nat else String)

@[noinline] def mkTable (n : Nat) : Table :=
  if n % 2 = 0 then ⟨true, n, fun i => i.val * i.val⟩ else ⟨false, n, fun i => s!"<{i.val}>"⟩

@[noinline] def showTable : Table → String
  | ⟨true, n, f⟩ => let g : Fin n → Nat := f; toString (Vec.ofFn n g).toList
  | ⟨false, n, f⟩ => let g : Fin n → String := f; toString (Vec.ofFn n g).toList

@[noinline] def sumTable : Table → Nat
  | ⟨true, n, f⟩ => let g : Fin n → Nat := f; (Vec.ofFn n g).toList.foldl (· + ·) 0
  | ⟨false, n, f⟩ => let g : Fin n → String := f; (Vec.ofFn n g).toList.foldl (fun a s => a + s.length) 0

@[noinline] def ends : (n : Nat) → Vec Nat n → Vec String n → String
  | k + 1, v, w => s!"{v.get ⟨k, Nat.lt_succ_self k⟩} {w.get ⟨0, Nat.zero_lt_succ k⟩}"
  | 0, _, _ => "empty"

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let v := Vec.ofFn n (fun i => i.val * 2)
  let w := Vec.ofFn n (fun i => toString i.val)
  IO.println s!"{v.toList} {w.toList}"
  IO.println (ends n v w)
  for i in List.range (n + 2) do IO.println s!"{showTable (mkTable i)} {sumTable (mkTable i)}"
end D71BreakerP19

namespace D71BreakerP20
/- P20: existentials with Type fields holding functions and nested existentials; mapping over them. -/
structure Dyn where
  {α : Type}
  val : α
  sh : α → String
  step : α → α

@[noinline] def Dyn.show (d : Dyn) : String := d.sh d.val
@[noinline] def Dyn.next (d : Dyn) : Dyn := { d with val := d.step d.val }
@[noinline] def Dyn.nest (d : Dyn) : Dyn := { α := List (d.α) × Nat, val := ([d.val], 0), sh := fun (xs, k) => "[" ++ ",".intercalate (xs.map d.sh) ++ s!"]{k}", step := fun (xs, k) => (xs.map d.step ++ xs, k + 1) }
@[noinline] def Dyn.pairUp (d e : Dyn) : Dyn := { α := d.α × e.α, val := (d.val, e.val), sh := fun (x, y) => d.sh x ++ "&" ++ e.sh y, step := fun (x, y) => (d.step x, e.step (e.step y)) }

@[noinline] def mkDyn (n : Nat) : Dyn :=
  match n % 3 with
  | 0 => { val := n, sh := toString, step := (· + 1) }
  | 1 => { val := toString n, sh := id, step := (· ++ "'") }
  | _ => { val := (List.range (n % 4)), sh := toString, step := fun xs => xs.map (· * 2) }

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ds := (List.range (n + 3)).map mkDyn
  IO.println (ds.map Dyn.show)
  IO.println ((ds.map Dyn.next).map Dyn.show)
  IO.println ((ds.map Dyn.nest).map Dyn.show)
  IO.println (((ds.map Dyn.nest).map Dyn.next).map Dyn.show)
  match ds with
  | a :: b :: _ => IO.println s!"{(a.pairUp b).show} {(a.pairUp b).next.show} {(a.pairUp b).next.next.nest.next.show}"
  | _ => IO.println "short"
  let deep := (List.range n).foldl (fun d _ => d.nest.next) (mkDyn n)
  IO.println deep.show
end D71BreakerP20

namespace D71BreakerP21
/- P21: polymorphic recursion whose growing value is a dependent record / holds Box positions. -/
structure Pkg where
  b : Bool
  v : if b then Nat else String
@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
@[noinline] def showP : Pkg → String
  | ⟨true, v⟩ => let w : Nat := v; s!"N{w}"
  | ⟨false, v⟩ => let s : String := v; s!"S{s}"

@[noinline] def grow (n : Nat) (x : α) (sh : α → String) : String :=
  match n with
  | 0 => sh x
  | n + 1 => grow n (x, mk n) (fun (a, p) => sh a ++ "," ++ showP p)

@[noinline] def growL (n : Nat) (xs : List α) (sh : α → String) : List String :=
  match n with
  | 0 => xs.map sh
  | n + 1 => growL n (xs.map (fun x => (x, mk (n + xs.length)))) (fun (a, p) => sh a ++ "/" ++ showP p)

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println (grow n (mk n) showP)
  IO.println (grow (n % 2) n toString)
  IO.println (growL n [mk n, mk (n + 1)] showP)
  IO.println (growL (n % 3) [toString n] id)
end D71BreakerP21

def main : IO Unit := do
  IO.println "-- D71BreakerP14BC"
  D71BreakerP14BC.caseMain ["3"]
  IO.println "-- D71BreakerP14C"
  D71BreakerP14C.caseMain ["3"]
  IO.println "-- D71BreakerP14D"
  D71BreakerP14D.caseMain ["3"]
  IO.println "-- D71BreakerP14E"
  D71BreakerP14E.caseMain ["3"]
  IO.println "-- D71BreakerP15"
  D71BreakerP15.caseMain ["4"]
  IO.println "-- D71BreakerP16B"
  D71BreakerP16B.caseMain ["3"]
  IO.println "-- D71BreakerP17"
  D71BreakerP17.caseMain ["3"]
  IO.println "-- D71BreakerP18"
  D71BreakerP18.caseMain ["5"]
  IO.println "-- D71BreakerP19"
  D71BreakerP19.caseMain ["4"]
  IO.println "-- D71BreakerP20"
  D71BreakerP20.caseMain ["5"]
  IO.println "-- D71BreakerP21"
  D71BreakerP21.caseMain ["4"]
