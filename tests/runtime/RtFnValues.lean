/-! Runtime test: function values. LwFn1: the plan's mkAdder arity example;
traced partial and over-application; closure-returning functions with work
between arguments; structures and arrays of closures; a 2000-function
composition; applyN 10^5; a fixpoint combinator; partial applications of
externs and constructors (Nat.succ, Nat.add 5, Prod.mk, some, String.length,
toString); IO actions in arrays; StateT/ReaderT/ExceptT; erased, proof and
type parameters; closures of closures through Thunk/Task. LwFn2: function
values through uniform code: existentials whose payload is Nat → Nat,
Nat → Nat → Nat (arity-2 targets and closure-returning targets with traced
work), String × (Nat → String), arrays and Options of closures; polymorphic
recursion over closures; Dynamic; a StateT tower with function-valued state.
From the round-7 review, area L (rv7/lowering), checks 12 and 13 (LwFn1,
LwFn2). -/

namespace LwFn1
-- from rv7/lowering/LwFn1.lean
-- Function values: partial/over application, closures in data, compositions, externs
def mkAdder (n : Nat) : Nat → Nat :=
  let k := dbgTrace s!"prefix {n}" fun _ => n * n
  fun x => x + k

@[noinline] def mkAdder2 (n : Nat) : Nat → Nat :=
  dbgTrace s!"mk2 {n}" fun _ => fun x => x + n * 3

@[noinline] def add3 (a b c : Nat) : Nat := dbgTrace s!"add3 {a} {b} {c}" fun _ => a + b + c

@[noinline] def retFn (a : Nat) (b : Nat) : Nat → Nat → Nat :=
  dbgTrace s!"retFn {a} {b}" fun _ => fun x y => a * 1000 + b * 100 + x * 10 + y

structure Ops where
  f : Nat → Nat
  g : Nat → Nat → Nat
  h : String → Nat → String

@[noinline] def applyN (f : α → α) : Nat → α → α
  | 0, x => x
  | n+1, x => applyN f n (f x)

@[noinline] def compose (fs : List (Nat → Nat)) : Nat → Nat :=
  fs.foldr (· ∘ ·) id

partial def fix (f : (Nat → Nat) → Nat → Nat) : Nat → Nat := f (fix f)

def t1 : IO Unit := do
  let a := mkAdder 3
  IO.println s!"t1 {a 1} {a 2} {mkAdder 3 4}"
  let b := mkAdder2 4
  IO.println s!"t1b {b 1} {b 2}"

def t2 : IO Unit := do
  let p1 := add3 1
  let p2 := p1 2
  IO.println "t2 built"
  IO.println s!"t2 {p2 3} {p2 4} {p1 5 6} {add3 7 8 9}"
  let q := retFn 1
  IO.println "t2 q built"
  let q2 := q 2
  IO.println "t2 q2 built"
  IO.println s!"t2 {q2 3 4} {retFn 5 6 7 8} {q 9 1 2}"
  let r := retFn 1 2 3
  IO.println s!"t2 {r 4} {r 5}"

def t3 : IO Unit := do
  let ops : Ops := { f := (· + 1), g := Nat.add, h := fun s n => s ++ toString n }
  let ops2 : Ops := { ops with f := ops.f ∘ ops.f, g := fun a b => ops.g (ops.f a) b }
  let arr : Array Ops := #[ops, ops2, { ops2 with h := fun s _ => s.push '!' }]
  for o in arr do
    IO.println s!"t3 {o.f 10} {o.g 1 2} {o.h "x" 5}"
  let fs : Array (Nat → Nat) := #[ops.f, ops2.f, ops.g 100, ops2.g 50, add3 1 1, mkAdder 2]
  IO.println s!"t3b {fs.map (· 7)}"

def t4 : IO Unit := do
  let fs := (List.range 2000).map (fun i => fun x => (x + i) % 1000003)
  let c := compose fs
  IO.println s!"t4 {c 1} {applyN (· * 3 % 1000003) 100000 1} {applyN (fun (s : String) => s.push 'a') 5 ""}"
  let fact := fix (fun self n => if n == 0 then 1 else n * self (n - 1))
  IO.println s!"t4b {fact 20}"

def t5 : IO Unit := do
  let xs := #[3, 1, 2]
  IO.println s!"t5 {xs.map Nat.succ} {xs.map (Nat.add 5)} {xs.foldl Nat.max 0} {xs.map toString} {xs.map (Nat.toFloat)}"
  IO.println s!"t5b {xs.toList.map (Prod.mk 1)} {xs.map some} {xs.zipWith (Prod.mk) #["a", "b", "c"]} {xs.qsort (· > ·)}"
  IO.println s!"t5c {xs.any (· > 2)} {xs.all (· > 0)} {(xs.map (fun x => fun y => x + y)).map (· 10)}"
  let strs := #["bb", "a", "ccc"]
  IO.println s!"t5d {strs.map String.length} {strs.qsort (fun a b => a.length < b.length)} {strs.foldl String.append ""}"

def t6 : IO Unit := do
  let r ← IO.mkRef 0
  let acts : Array (IO Unit) := #[r.modify (· + 1), r.modify (· * 10), IO.println "act", r.set 5]
  for a in acts do a
  for a in acts.reverse do a
  IO.println s!"t6 {← r.get}"
  let mkAct (n : Nat) : IO Nat := do r.modify (· + n); return (← r.get)
  let ps := (List.range 5).map mkAct
  let mut out := #[]
  for p in ps do out := out.push (← p)
  IO.println s!"t6b {out}"
  let printers : List (String → IO Unit) := [IO.println, fun s => IO.println (s ++ "!"), IO.print]
  for p in printers do p "pr"
  IO.println ""

def counter : StateT Nat IO Unit := do
  modify (· + 1)
  let s ← get
  if s % 2 == 0 then liftM (m := IO) (IO.println s!"even {s}") else pure ()

def t7 : IO Unit := do
  let steps : List (StateT Nat IO Unit) := [counter, counter, (fun n => pure ((), n * 10)), counter]
  let ((), s) ← (steps.forM id).run 1
  IO.println s!"t7 {s}"
  let rd : ReaderT Nat (ExceptT String IO) Nat := do
    let e ← read
    if e > 5 then throw s!"big {e}" else return e * 2
  let r1 ← (rd.run 3).run
  let r2 ← (rd.run 9).run
  IO.println s!"t7b {repr r1} {repr r2}"

def t8 : IO Unit := do
  -- erased / proof / type params in function values
  let f : (n : Nat) → n > 0 → Nat := fun n _ => n - 1
  let g := f 5
  IO.println s!"t8 {g (by decide)}"
  let ids : List (Nat → Nat) := [@id Nat, fun x => x, Function.const Nat 7]
  IO.println s!"t8b {ids.map (· 3)}"
  let h : {α : Type} → [ToString α] → α → String := fun x => toString x ++ "?"
  IO.println s!"t8c {h 5} {h "s"}"

def t9 : IO Unit := do
  -- closures capturing closures, thunks, tasks
  let base := fun (x : Nat) => x * 2
  let lvl1 := fun (x : Nat) => base (base x)
  let lvl2 := fun (f : Nat → Nat) (x : Nat) => f (lvl1 x)
  let lvl3 := lvl2 lvl1
  let th : Thunk (Nat → Nat) := Thunk.mk fun _ => dbgTrace "thunk" fun _ => lvl3
  IO.println s!"t9 {lvl3 1} {th.get 2} {th.get 3}"
  let tk := Task.spawn fun _ => fun (y : Nat) => lvl3 y + 1
  IO.println s!"t9b {tk.get 1}"

def main : IO Unit := do
  t1; t2; t3; t4; t5; t6; t7; t8; t9
end LwFn1

namespace LwFn2
-- from rv7/lowering/LwFn2.lean
-- Function values through uniform code (existentials, Dynamic, polymorphic recursion)
structure Ex where
  α : Type
  f : α → α
  x : α
  out : α → String

@[noinline] def twice (g : Nat → Nat) (n : Nat) : Nat := dbgTrace s!"twice {n}" fun _ => g (g n)
@[noinline] def add2 (a b : Nat) : Nat := a + b
@[noinline] def mk3 (a : Nat) : Nat → Nat → Nat := dbgTrace s!"mk3 {a}" fun _ => fun b c => a * 100 + b * 10 + c

@[noinline] def runEx (e : Ex) (k : Nat) : String := Id.run do
  let mut v := e.x
  for _ in [0:k] do v := e.f v
  return e.out v

def exs : List Ex := [
  ⟨Nat → Nat, twice, (· + 1), fun g => toString (g 0)⟩,
  ⟨Nat → Nat, fun g => g ∘ g, (· * 2), fun g => toString (g 1)⟩,
  ⟨Nat → Nat → Nat, fun g a b => g b a + 1, add2, fun g => toString (g 3 4)⟩,
  ⟨Nat → Nat → Nat, fun g => g, mk3 7, fun g => toString (g 1 2)⟩,
  ⟨Nat → Nat → Nat, fun _ => mk3 9, mk3 1, fun g => toString (g 5 6 + g 7 8)⟩,
  ⟨String × (Nat → String), fun (s, h) => (s ++ h s.length, fun n => toString (n * 2)), ("a", toString), fun p => p.1 ++ p.2 9⟩,
  ⟨Array (Nat → Nat), fun a => a.push (· + a.size), #[], fun a => toString (a.map (· 100))⟩,
  ⟨Option (Nat → Nat → Nat), fun o => o.map (fun g a => g a), some add2, fun o => toString ((o.getD add2) 10 20)⟩
]

inductive Nest : Type → Type 1 where
  | leaf {α : Type} : α → Nest α
  | node {α : Type} : Nest (α × α) → Nest α

def Nest.depth {α : Type} : Nest α → Nat
  | .leaf _ => 0
  | .node n => n.depth + 1

partial def Nest.apply {α : Type} (k : α → Nat) : Nest α → Nat
  | .leaf a => k a
  | .node n => n.apply (fun (p : α × α) => k p.1 * 31 + k p.2)

def mkNest {α : Type} (a : α) : Nat → Nest α
  | 0 => .leaf a
  | n+1 => .node (mkNest (a, a) n)

def t3 : IO Unit := do
  let n : Nest (Nat → Nat) := mkNest (fun x => x + 1) 3
  IO.println s!"t3 {n.depth} {n.apply (fun f => f 1)}"
  let n2 : Nest (Nat → Nat → Nat) := mkNest add2 2
  IO.println s!"t3b {n2.apply (fun f => f 1 2)} {(mkNest (mk3 2) 2 : Nest (Nat → Nat → Nat)).apply (fun g => g 3 4)}"

structure F1 where f : Nat → Nat
  deriving TypeName
structure F2 where f : Nat → Nat → Nat
  deriving TypeName
structure Str where s : String
  deriving TypeName

def t4 : IO Unit := do
  let ds : List Dynamic := [Dynamic.mk (F1.mk fun (x : Nat) => x + 1), Dynamic.mk (F2.mk add2), Dynamic.mk (F2.mk (mk3 5)), Dynamic.mk (Str.mk "s"), Dynamic.mk (F1.mk (mk3 1 2))]
  for d in ds do
    match d.get? F1 with
    | some f => IO.println s!"t4 f1 {f.f 10}"
    | none =>
      match d.get? F2 with
      | some g => IO.println s!"t4 f2 {g.f 1 2} {(g.f 3) 4}"
      | none => IO.println "t4 other"

-- State transformer tower with function-valued state
abbrev M := StateT (Nat → Nat) (StateT (List (String → String)) IO)

def step (k : Nat) : M Unit := do
  let f ← get
  set (fun x => f x + k)
  modifyThe (List (String → String)) (fun l => (· ++ toString k) :: l)

def t5 : IO Unit := do
  let ((_, f), l) ← (((List.range 5).forM step).run id).run []
  IO.println s!"t5 {f 0} {l.foldl (fun s g => g s) ""}"

def main : IO Unit := do
  for e in exs do IO.println (runEx e 2)
  t3; t4; t5
end LwFn2

def main : IO Unit := do
  IO.println "=== LwFn1"
  LwFn1.main
  IO.println "=== LwFn2"
  LwFn2.main
