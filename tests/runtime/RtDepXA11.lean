/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `A927`: A debug primitive whose closure returns an `IO` action follows T13
  step 6's cut, as `Thunk.mk`'s does (F8): the row's `α` is an action type,
  so the closure takes `()` and returns the action, a closure in ...
- `A931`: CSLib B2, a false refusal on main 9d342f92 ("constructor field
  FF.mk #1: the field's mono type `lcAny` ...
- `A934`: CSLib's `SingleTapeTM.compComputer` shape: a structure's T7 slot
  parameter (`TM`'s type-carrying field `State`) instantiated in its own
  component at a type containing it (`State := m.State ⊕ m.State`, r-deep
  for an ...
- `A935`: Lean-runtime's case cse/panic_once_across_types (lean2rr XT-6):
  one panicking call `gp xs none` used at `Option String` and `Option (Nat →
  Nat)`, which Lean's CSE merges after erasure, so the panic prints once.
- `A937`: A debug primitive whose closure returns a function value that the
  caller applies at once (a `ReaderT`, `StateT` or `ExceptT` over `ReaderT`
  action, a `String → String` function) carries its result type's witness as
  ...
- `A942`: Polymorphic recursion over `List` with a `ToString` dictionary
  (`occQ n [y]`, called at `String` and at `Nat`) is refused nested-coercion
  at the dictionary argument (tracked
- `A943`: With F2's growing chains: polymorphic recursion whose `ToString`
  dictionary is rebuilt at each level (`occQ n (some y)`), each level
  wrapping the dictionary closure again, ...
- `A947`: Polymorphic recursion whose site union holds a family-keyed
  component (`(x, pick b n)`, `Ty b`) passed down with a lambda `fun (p : α
  × Ty b) => …`: no move relates the lambda's `p.2` to ...
- `A948`: Growing chains, A943's class: mutual polymorphic recursion through
  closures (`mA` passes `mB` a lambda over `α × Option α`, `mB` passes `mA`
  one over `Option β`), whose generic arrow ...
- `A951`: Chapter 06 A4 io fixture A951 (M5, D83
- `A957`: (d)'s wrapper over an IO function value under polymorphic
  recursion (`logD n (fun (p : α × Nat) => do f p.1 -/

namespace A927

def seven : IO Nat := pure 7

@[noinline] def sleepIo (s : String) : IO String := dbgSleep 1 (fun _ => pure s)
@[noinline] def stackIo (s : String) : IO String := dbgStackTrace (fun _ => pure (s ++ "!"))
@[noinline] def traced (n : Nat) : IO Unit := dbgTrace s!"traced {n}" (fun _ => IO.println s!"run {n}")
@[noinline] def mixed (n : Nat) : List (IO Nat) := [seven, dbgTrace "mixed" (fun _ => pure n)]
@[noinline] def built (n : Nat) : List (IO Unit) := [dbgTrace "built" (fun _ => IO.println s!"act {n}")]
@[noinline] def twice (n : Nat) : IO Unit := do
  let a := dbgTrace s!"twice {n}" (fun _ => IO.println s!"once {n}")
  a
  a

def caseMain (args : List String) : IO UInt32 := do
  let n := args.length + 3
  IO.println (← sleepIo s!"s{n}")
  if args.headD "" == "stack" then IO.println (← stackIo s!"k{n}")
  traced n
  traced (n + 1)
  for a in mixed n do IO.println (← a)
  let bs := built n
  for b in bs do b
  for b in bs do b
  twice n
  return 0
end A927

namespace A931

def MS (α : Type) := Quot (@Eq (List α))

def MS.filter {α : Type} (p : α → Bool) (m : MS α) : MS α :=
  Quot.lift (fun l => Quot.mk _ (l.filter p)) (fun _ _ h => h ▸ rfl) m

structure FF (α β : Type) where
  fn : α → β
  items : MS α

def mk {α β : Type} (fn : α → β) (p : α → Bool) (m : MS α) : FF α β := ⟨fn, m.filter p⟩

def caseMain (args : List String) : IO Unit := do
  let f : FF Nat Nat := mk (· + 1) (· % 2 == 0) (Quot.mk _ (List.range (args.length + 3)))
  IO.println s!"{Quot.lift List.length (fun _ _ h => h ▸ rfl) f.items} {f.fn 2}"
end A931

namespace A934

structure TM where
  State : Type
  q0 : State
  step : State → Nat → Option (State × Nat)
def TM.run (m : TM) : Nat → m.State → Nat → Nat
  | 0, _, acc => acc
  | f + 1, q, acc => match m.step q acc with | some (q', a) => m.run f q' a | none => acc
def base : TM := { State := Bool, q0 := false, step := fun q a => if q then none else some (true, a + 1) }
def comp (m : TM) : TM where
  State := m.State ⊕ m.State
  q0 := .inl m.q0
  step := fun q a => match q with
    | .inl s => match m.step s a with | some (s', b) => some (.inl s', b) | none => some (.inr m.q0, a)
    | .inr s => (m.step s a).map fun (s', b) => (.inr s', b)
def compN : Nat → TM | 0 => base | r + 1 => comp (compN r)
def caseMain (args : List String) : IO Unit := do
  let m := compN args.length
  IO.println s!"{m.run 50 m.q0 0}"
end A934

namespace A935

-- One panicking call used at two types. After type erasure the two calls of
-- `gp xs none` are the same, Lean's common-subexpression elimination merges
-- them, and the panic (`xs[5]!` out of bounds: the array's size is the
-- number of arguments, none here) prints once natively. A translation that
-- keeps one instance per type calls `gp` twice and prints it twice
-- "merged call of a declaration that is not pure-total"). Both translators
-- follow native.
@[noinline] def gp {α} (xs : Array Nat) (x : Option α) : Option α :=
  if xs[5]! > 3 then x else none
@[noinline] def useS (o : Option String) : Nat := match o with | some s => s.length | none => 1
@[noinline] def useF (o : Option (Nat → Nat)) : Nat := match o with | some f => f 3 | none => 2

def caseMain (args : List String) : IO Unit := do
  let xs := Array.range args.length
  IO.println (useS (gp xs none) + useF (gp xs none))
end A935

namespace A937

@[noinline] def r (n : Nat) : ReaderT String IO Nat := dbgTrace "rdr" fun _ => do
  let e ← read
  pure (e.length + n)
@[noinline] def st (n : Nat) : StateT String IO Nat := dbgSleep 1 fun _ => do
  let e ← get
  set (e ++ "!")
  pure (e.length + n)
@[noinline] def ex (n : Nat) : ExceptT String (ReaderT String IO) Nat := dbgTrace "ex" fun _ => do
  let e ← read
  if e.length > 100 then throw "long" else pure (e.length * n)
@[noinline] def fn (n : Nat) (s : String) : String := (dbgTrace "fn" fun _ => fun (t : String) => t ++ toString n) s
@[noinline] def sk (n : Nat) : ReaderT String IO Nat := dbgStackTrace fun _ => do
  let e ← read
  pure (e.length - n)

def caseMain (a : List String) : IO Unit := do
  let e := s!"E{a.length}"
  IO.println s!"{← (r 2).run e} {e}"
  let (v, s) ← (st 1).run e
  IO.println s!"{v} {s} {e}"
  match ← (ex 3).run.run e with
  | .ok v => IO.println s!"ok {v}"
  | .error m => IO.println s!"error {m}"
  IO.println (fn 4 e)
  if a.headD "" == "stack" then IO.println s!"{← (sk 1).run e}"
end A937

namespace A942

@[noinline] def occQ {β : Type} [ToString β] : Nat → β → String
  | 0, y => toString y
  | n + 1, y => occQ n [y] ++ "."
def caseMain (args : List String) : IO Unit := IO.println (occQ args.length "q" ++ occQ (args.length + 1) (3 : Nat))
end A942

namespace A943

mutual
@[noinline] def occP {α : Type} [ToString α] : Nat → α → String
  | 0, x => toString x
  | n + 1, x => occP n (x, x) ++ occQ n "q"
@[noinline] def occQ {β : Type} [ToString β] : Nat → β → String
  | 0, y => toString y
  | n + 1, y => occQ n (some y) ++ occP n n
end
def caseMain (args : List String) : IO Unit := IO.println (occP args.length (5 : Nat))
end A943

namespace A947

def Ty : Bool → Type | true => Nat | false => String
def pick : (b : Bool) → Nat → Ty b | true, n => n * 2 | false, n => toString n
@[noinline] def mixed {α : Type} (b : Bool) : Nat → (α → Nat) → α → Nat
  | 0, f, x => f x
  | n+1, f, x => mixed b n (fun (p : α × Ty b) => f p.1 + (match b, p.2 with | true, v => let k : Nat := v; k | false, v => let s : String := v; s.length)) (x, pick b n)
def caseMain (args : List String) : IO Unit := IO.println s!"{mixed true 4 id (6 + args.length)} {mixed false 3 id (7 + args.length)}"
end A947

namespace A948

mutual
@[noinline] def mA {α : Type} : Nat → (α → Nat) → α → Nat
  | 0, f, x => f x
  | n+1, f, x => mB n (fun (p : α × Option α) => f p.1 + (p.2.map f).getD 0) (x, some x)
@[noinline] def mB {β : Type} : Nat → (β → Nat) → β → Nat
  | 0, f, y => f y + 10
  | n+1, f, y => mA n (fun (o : Option β) => match o with | some b => f b | none => 0) (some y)
end
mutual
@[noinline] def occF {α : Type} [ToString α] : Nat → α → String
  | 0, x => toString x
  | n + 1, x => occG n (x, n)
@[noinline] def occG {β : Type} [ToString β] : Nat → β → String
  | 0, y => toString y
  | n + 1, y => occF n (some y)
end
def caseMain (args : List String) : IO Unit := do
  IO.println s!"{mA 4 id (5 + args.length)} {mB 3 String.length "xy"}"
  IO.println (occF (3 + args.length) (7 : Nat))
end A948

namespace A951


def f (k : Nat) (o : Option Nat) : Nat :=
  match o with
  | some v => panic! s!"f ran on {v + k}"
  | none => k

@[noinline] def first : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let t := p.result?.map (·.getD 0)
  IO.println s!"dropped promise: {← IO.wait t}"

@[noinline] def second (k : Nat) : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let t := p.result?.map (f k)
  IO.println s!"state before the resolution: {← IO.getTaskState t}"
  p.resolve (k + 5)
  IO.sleep 100
  IO.println "after the resolution and the sleep"

def caseMain (args : List String) : IO Unit := do
  let k := ((args[0]?).bind String.toNat?).getD 1
  first
  second k
  IO.println "end"
end A951

namespace A957

@[noinline] def logD {α : Type} : Nat → (α → IO Unit) → α → IO Unit
  | 0, f, x => f x
  | n + 1, f, x => logD n (fun (p : α × Nat) => do f p.1; IO.println s!"level {p.2}") (x, n)
def caseMain (args : List String) : IO Unit := do
  let n := ((args[0]?).bind String.toNat?).getD 3
  let h ← IO.getStdout
  logD n (fun x => h.putStrLn s!"base {x}") (args.length + 1)
  IO.println "done"
end A957

def main : IO Unit := do
  IO.println "-- A927"
  let c ← A927.caseMain []
  IO.println s!"exit {c}"
  IO.println "-- A931"
  A931.caseMain ["a", "b", "c", "d", "e"]
  IO.println "-- A934"
  A934.caseMain ["a", "b", "c", "d", "e"]
  IO.println "-- A935"
  A935.caseMain ["a", "b", "c", "d", "e", "f"]
  IO.println "-- A937"
  A937.caseMain []
  IO.println "-- A942"
  A942.caseMain ["a", "b", "c"]
  IO.println "-- A943"
  A943.caseMain ["a", "b", "c"]
  IO.println "-- A947"
  A947.caseMain ["a"]
  IO.println "-- A948"
  A948.caseMain ["a"]
  IO.println "-- A951"
  A951.caseMain ["7"]
  IO.println "-- A957"
  A957.caseMain ["3"]
