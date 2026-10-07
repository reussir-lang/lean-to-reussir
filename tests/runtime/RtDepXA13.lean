/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `A971`: Decision D69: one function value `_f := id` (Lean's CSE shares it)
  that `app` reads at `Nat` and `both`'s rank-2 parameter at `Nat` and
  `String`: the coercion that would wrap it marks its ...
- `A972`: And step 11 (B): a rank-2 variable under a pointer-carrying
  constructor (`applyAll (h : {ι : Type} → List ι → Nat)` applied to a `List
  Nat` and a `List String`): each list is converted to the ...
- `A973`: Decision D69: a rank-2 variable under a by-value constructor
  (`optH (h : {ι : Type} → Option ι → Nat)` at `some n` and `some s`, `pairH
  (h : {ι : Type} → ι × Nat → Nat)`): the variable's key ...
- `A974`: Decision D69: rank-2 parameters whose dictionary over the variable
  is no one-arrow-field structure (`[Shape ι]` with two arrow fields,
  `[Inhabited ι]` whose field is the variable), applied at ...
- `A975`: Decision D69: a rank-2 parameter passed to a first-order higher-
  order function (`(xs.map h).length + h s`): Lean applies its erased type
  argument first (`h ◾`, a call), so the wrapper wraps ...
- `A977`: A function value `g : Unit → IO α` passed straight to `dbgTrace`
  or `dbgSleep` (a parameter, and a structure field) is of a class that T13
  step 6 cuts at the row's `α := IO β`, as at `Thunk.mk`'s (F8): its ...
- `A978`: Decision D69: one reference to a forwarder `twice'` (Lean shares
  it) passed at `useNat`'s rank-2 parameter at `Nat` and at `usePair`'s at
  `Nat × String`: joined by marks, `useNat`'s `h` typed ...
- `A979`: Decision D69: a lambda whose `cases` reads its argument at `Nat`
  and `String` (`x + 1`, `x.length`) passed to `useOp (h : {ι : Type} → Op ι
  → ι → Nat)`, whose calls key `h`'s variable apart: ...
- `A981`: And step 4, decision D69: a forwarder `twice'` passed at two
  rank-2 parameters at two types and a lambda at a two-variable rank-2
  parameter.
- `A982`: A higher-rank function in a one-field structure (`structure HB
  where run : {ι : Type} → ι → ι`, read as `b.run n` and `b.run s`), which
  mono unfolds to the function itself: no rank-2 parameter, so two types at
  its ...
- `A983`: Decision D69: a named generic handler (`handler {ι} (op : Op ι) (x
  : ι)`, whose `cases` reads `x` at `Nat` and `String`) passed to two rank-2
  parameters: its own type parameter is site-keyed ... -/

namespace A971

@[noinline] def app {α : Type} (h : {ι : Type} → ι → ι) (x : α) : α := h x
@[noinline] def both (h : {ι : Type} → ι → ι) (n : Nat) (s : String) : Nat × String := (h n, h s)

def caseMain (args : List String) : IO Unit := do
  IO.println s!"{app id (args.length + 4)} {both id args.length "x"}"
end A971

namespace A972

@[noinline] def applyAll (h : {ι : Type} → List ι → Nat) (n : Nat) (s : String) : Nat := h [n, n + 1] + h [s]
@[noinline] def lenTwice {ι : Type} (xs : List ι) : Nat := xs.length * 2

def caseMain (args : List String) : IO Unit := do
  IO.println s!"{applyAll (fun xs => xs.length + args.length) 3 "a"} {applyAll lenTwice args.length "b"}"
end A972

namespace A973

@[noinline] def optH (h : {ι : Type} → Option ι → Nat) (n : Nat) (s : String) : Nat := h (some n) + h (some s)
@[noinline] def pairH (h : {ι : Type} → ι × Nat → Nat) (n : Nat) (s : String) : Nat := h (n, 1) + h (s, 2)

def caseMain (args : List String) : IO Unit := do
  IO.println s!"{optH (fun o => if o.isSome then 1 else 0) args.length "x"} {pairH (fun p => p.2) 3 "y"}"
end A973

namespace A974

class Shape (α : Type) where
  area : α → Nat
  name : α → String
instance : Shape Nat := ⟨fun n => n * n, fun _ => "nat"⟩
instance : Shape String := ⟨String.length, fun s => s⟩
@[noinline] def useShape (h : {ι : Type} → [Shape ι] → ι → Nat) (n : Nat) (s : String) : Nat := h n + h s
@[noinline] def useInh (h : {ι : Type} → [Inhabited ι] → ι → ι) (n : Nat) (s : String) : Nat × String := (h n, h s)

def caseMain (args : List String) : IO Unit := do
  IO.println s!"{useShape (fun x => Shape.area x + (Shape.name x).length) args.length "ab"} {useInh (fun x => x) 4 "z"}"
end A974

namespace A975

@[noinline] def mp (h : {ι : Type} → ι → Nat) (xs : List Nat) (s : String) : Nat := (xs.map h).length + h s

def caseMain (args : List String) : IO Unit := do
  IO.println s!"{mp (fun _ => 3) [1, 2, args.length] "q"}"
end A975

namespace A977

@[noinline] def actN (n : Nat) (_ : Unit) : IO Nat := do
  IO.println s!"actN {n}"
  pure (n + 1)

@[noinline] def viaTrace (g : Unit → IO Nat) : IO Nat := dbgTrace "via trace" g
@[noinline] def viaSleep (g : Unit → IO Nat) : IO Nat := dbgSleep 1 g

structure Job where
  name : String
  run : Unit → IO Nat

@[noinline] def traceJob (j : Job) : IO Nat := do
  IO.println j.name
  dbgTrace s!"job {j.name}" j.run

def caseMain (args : List String) : IO Unit := do
  let k := args.length
  IO.println s!"{← viaTrace (actN (k + 1))}"
  IO.println s!"{← viaSleep (actN (k + 2))}"
  IO.println s!"{← traceJob { name := s!"j{k}", run := actN (k + 3) }}"
end A977

namespace A978

@[noinline] def useNat (h : {ι : Type} → ι → ι) (n : Nat) : Nat := h n + 1
@[noinline] def usePair (h : {ι : Type} → ι → ι) (n : Nat) (s : String) : String := toString (h (n, s))
@[noinline] def twice {α : Type} (x : α) : α := x
def twice' {α : Type} (x : α) : α := twice x
def caseMain (args : List String) : IO Unit := do
  let n := args.length
  IO.println s!"{useNat twice' (n + 1)}"
  IO.println s!"{usePair twice' n "q"}"
end A978

namespace A979

inductive Op : Type → Type where
  | n : Op Nat
  | s : Op String
@[noinline] def useOp (h : {ι : Type} → Op ι → ι → Nat) : Nat := h .n 5 + h .s "ab"

def caseMain (args : List String) : IO Unit := do
  IO.println s!"{useOp (fun op x => match op, x with | .n, x => x + 1 + args.length | .s, x => x.length)}"
end A979

namespace A981

@[noinline] def useNat (h : {ι : Type} → ι → ι) (n : Nat) : Nat := h n + 1
@[noinline] def usePair (h : {ι : Type} → ι → ι) (n : Nat) (s : String) : String := toString (h (n, s))
@[noinline] def useTwo (h : {α β : Type} → α → β → α) (n : Nat) (s : String) : Nat := h n s
@[noinline] def twice {α : Type} (x : α) : α := x
def twice' {α : Type} (x : α) : α := twice x

def caseMain (args : List String) : IO Unit := do
  let n := args.length
  IO.println s!"{useNat twice' (n + 1)}"
  IO.println s!"{usePair twice' n "q"}"
  IO.println s!"{useTwo (fun a _ => a) (n + 5) "c"}"
end A981

namespace A982

structure HB where
  run : {ι : Type} → ι → ι
@[noinline] def useHB (b : HB) (n : Nat) (s : String) : Nat × String := (b.run n, b.run s)
def caseMain (args : List String) : IO Unit := do
  let n := args.length
  IO.println s!"{useHB ⟨fun x => x⟩ n "s"}"
end A982

namespace A983

inductive Op : Type → Type where
  | n : Op Nat
  | s : Op String
@[noinline] def useOp (h : {ι : Type} → Op ι → ι → Nat) : Nat := h .n 5 + h .s "ab"
@[noinline] def useN (h : {ι : Type} → Op ι → ι → Nat) (k : Nat) : Nat := h .n k
@[noinline] def handler {ι : Type} (op : Op ι) (x : ι) : Nat :=
  match op, x with
  | .n, x => x + 1
  | .s, x => x.length

def caseMain (args : List String) : IO Unit := do
  IO.println s!"{useOp handler + useN handler args.length}"
end A983

def main : IO Unit := do
  IO.println "-- A971"
  A971.caseMain ["a", "b", "c"]
  IO.println "-- A972"
  A972.caseMain ["a", "b", "c"]
  IO.println "-- A973"
  A973.caseMain ["a", "b"]
  IO.println "-- A974"
  A974.caseMain ["a", "b"]
  IO.println "-- A975"
  A975.caseMain ["a", "b"]
  IO.println "-- A977"
  A977.caseMain ["x", "y"]
  IO.println "-- A978"
  A978.caseMain ["a", "b", "c"]
  IO.println "-- A979"
  A979.caseMain ["a", "b", "c"]
  IO.println "-- A981"
  A981.caseMain ["a", "b", "c"]
  IO.println "-- A982"
  A982.caseMain ["a", "b", "c"]
  IO.println "-- A983"
  A983.caseMain ["a", "b", "c"]
