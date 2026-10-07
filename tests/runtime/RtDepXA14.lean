/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `A984`: D56 and T15 step 2a: a generic declaration passed point-free at a
  rank-2 parameter (`useBoth twice n s` with `twice {α} (f : α → α) (x : α)`
- `A986`: Decision D69: one `church k` partial application passed to
  `useBoth (c : {α : Type} → (α → α) → α → α)` (at `Nat` and `String`) and
  to `useList` (at `List Nat`): joined at the marked site, but ...
- `A987`: A handler stored in a one-field structure (`H {run : {ι : Type} →
  List ι → List ι}`) read at `List Nat` and `List String` within `useNS`,
  and at one type per use by a generic `useAny`: no ...
- `A988`: A free-monad runner whose own type parameter `σ` meets `PUnit` at
  the slot (`k s` and `k ()`), used by `modifyS` alone, at two state types
  (`Nat` and `String`) and ...
- `A989`: One `FreeM.lift` shared by a marked `FreeM (StateF Nat)` (`walk`)
  and a native `FreeM Tick` (`ticks`): E1 marks `lift`'s class, which every
  caller shares, so `ticks` ...
- `A990`: A marked caller of `withList {F α ι} (op : F ι) (xs : List ι) (k :
  ι → FreeM F α)` (`withList .get [n] …` in a marked `FreeM (StateF Nat)`)
  passes `xs` built at `List Nat` where ...
- `A991`: `withList {F α ι} (op : F ι) (xs : List ι) (k : ι → FreeM F α)`
  used by a native `FreeM Tick` program beside a marked `FreeM (StateF Nat)`
  one: E1 reads the callee's ...
- `A992`: An `Array (FreeM (StateF Nat) Nat)` whose elements come from a
  one-typed producer (`getS`) and a marked one, built by `Array.map`
  (`arrOf`) and by `push` in a loop ...
- `A993`: (reference/support-status.md NS19): `run (getL (σ := Nat)) n`
  beside `run (getL (σ := String)) ab`, whose one closed term `@getL ◾`
  Lean's compiler shares between the two instantiations
- `A994`: An `Array (FreeM (StateF Nat) Nat)` mixing a one-typed producer
  (`getS`) with a marked one (`liftBindAfter (setS i)`), built by
  `Array.map` and by `push` in a loop, read by a ...
- `A995`: Rule E4 and step 11 (A): two mutually recursive free-monad runners
  (`runA`, `runB`) that pass `k s` and `k ()` to each other, at `Nat`,
  `String` and `Bool`: the slot class holds two ... -/

namespace A984

@[noinline] def twice {α : Type} (f : α → α) (x : α) : α := f (f x)
@[noinline] def useBoth (c : {α : Type} → (α → α) → α → α) (n : Nat) (s : String) : Nat × String :=
  (c (· + n) 0, c (· ++ s) "")
inductive Tree where
  | leaf : Nat → Tree
  | node : String → Tree → Tree → Tree
@[noinline] def fold {α : Type} (lf : Nat → α) (nd : String → α → α → α) : Tree → α
  | .leaf n => lf n
  | .node s l r => nd s (fold lf nd l) (fold lf nd r)
@[noinline] def two (v : {α : Type} → (Nat → α) → (String → α → α → α) → Tree → α) (t : Tree) : Nat × String :=
  (v id (fun _ a b => a + b) t, v toString (fun s a b => s!"({s} {a} {b})") t)
def caseMain (args : List String) : IO Unit := do
  IO.println s!"{useBoth twice (args.length + 2) "ab"}"
  IO.println s!"{two fold (.node "r" (.leaf args.length) (.leaf 2))}"
end A984

namespace A986

@[noinline] def church (n : Nat) {α : Type} (f : α → α) (x : α) : α := match n with
  | 0 => x
  | k + 1 => f (church k f x)
@[noinline] def useBoth (c : {α : Type} → (α → α) → α → α) (n : Nat) (s : String) : Nat × String :=
  (c (· + n) 0, c (· ++ s) "")
@[noinline] def useList (c : {α : Type} → (α → α) → α → α) : List Nat := c (fun l => l.length :: l) []
def caseMain (args : List String) : IO Unit := do
  let k := args.length + 2
  IO.println s!"{useBoth (church k) 3 "ab"} {useList (church k)} {useBoth (fun f x => f (f x)) 1 "z"}"
end A986

namespace A987

structure H where
  run : {ι : Type} → List ι → List ι
@[noinline] def useNS (h : H) (n : Nat) (s : String) : Nat × Nat := ((h.run [n, n + 1]).length, (h.run [s]).length)
@[noinline] def useAny {α : Type} (h : H) (xs : List α) : Nat := (h.run xs).length
def caseMain (args : List String) : IO Unit := do
  let k := args.length
  let h : H := ⟨fun xs => xs ++ xs⟩
  let r : H := ⟨List.reverse⟩
  IO.println s!"{useNS h k "s"} {useAny h [k, k]} {useAny h ["a"]} {useNS r k "t"} {useAny r [true]}"
end A987

namespace A988

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit
inductive Tick : Type → Type where
  | tick : Nat → Tick Nat
inductive ReaderF (ρ : Type) : Type → Type where
  | ask : ReaderF ρ ρ
  | tell : String → ReaderF ρ PUnit
@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)
@[noinline] def FreeM.lift {F : Type → Type} {ι : Type} (op : F ι) : FreeM F ι := .liftBind op .pure
@[noinline] def run {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => run (k s) s
    | .set s' => run (k ()) s'
@[noinline] def runR {ρ α : Type} (env : ρ) : FreeM (ReaderF ρ) α → List String → α × List String
  | .pure a, log => (a, log.reverse)
  | .liftBind op k, log => match op with
    | .ask => runR env (k env) log
    | .tell s => runR env (k ()) (s :: log)
@[noinline] def runTick : FreeM Tick Nat → Nat
  | .pure a => a
  | .liftBind (.tick m) k => m + runTick (k m)

/-- E2/E3 shapes: continuations tied to α, nested binds, two instances. -/
@[noinline] def getL {σ : Type} : FreeM (StateF σ) σ := .liftBind .get (fun s => .pure s)
@[noinline] def getK {σ : Type} : FreeM (StateF σ) σ :=
  let k : σ → FreeM (StateF σ) σ := fun s => .pure s
  .liftBind .get k
@[noinline] def getList {σ : Type} : FreeM (StateF σ) (List σ) := .liftBind .get (fun s => .pure [s])
@[noinline] def getPair {σ : Type} : FreeM (StateF σ) (σ × Nat) := .liftBind .get (fun s => .pure (s, 1))
@[noinline] def mapGet {σ β : Type} (f : σ → β) : FreeM (StateF σ) β := .liftBind .get (fun s => .pure (f s))
@[noinline] def modifyS {σ : Type} (f : σ → σ) : FreeM (StateF σ) σ :=
  .liftBind .get fun s => .liftBind (.set (f s)) fun _ => .pure s
@[noinline] def nested (n : Nat) : FreeM (StateF Nat) Nat :=
  getL.bind fun s => (modifyS (· + s + n)).bind fun t => getList.bind fun l => getPair.bind fun p => (mapGet toString).bind fun str => .pure (s + t + l.length + p.2 + str.length)
@[noinline] def nestedS (n : Nat) : FreeM (StateF String) Nat :=
  getL.bind fun s => (modifyS (· ++ s)).bind fun t => (mapGet String.length).bind fun k => .pure (s.length + t.length + k + n)
@[noinline] def runAny {σ α : Type} (p : FreeM (StateF σ) α) (s : σ) : α × σ := run p s
@[noinline] def runAny2 {σ α : Type} (p : FreeM (StateF σ) α) (s : σ) : α × σ := runAny p s
/-- A recursive runner used at `PUnit` alone: stays native under rule E4. -/
@[noinline] def runU {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => runU (k s) s
    | .set s' => runU (k ()) s'
@[noinline] def unitProg : Nat → FreeM (StateF PUnit) Nat
  | 0 => .pure 0
  | n+1 => .liftBind .get fun _ => .liftBind (.set ()) fun _ => unitProg n
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ab := "ab"
  IO.println s!"{run (modifyS (· + 1)) n}"
  IO.println s!"{run (getL (σ := Nat)) n} {run (modifyS (· ++ ab)) ab}"
  IO.println s!"{run (getK (σ := Nat)) n} {run (getList (σ := Nat)) n} {run (modifyS (· * 2)) n}"
  IO.println s!"{runAny (modifyS (· + 5)) n} {runAny2 (modifyS (· ++ "c")) ab}"
  IO.println s!"{(runU (unitProg n) ()).1}"
end A988

namespace A989

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α

inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit

@[noinline] def run {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => run (k s) s
    | .set s' => run (k ()) s'
inductive Tick : Type → Type where
  | tick : Nat → Tick Nat
@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)
@[noinline] def FreeM.lift {F : Type → Type} {ι : Type} (op : F ι) : FreeM F ι := .liftBind op (fun x => .pure x)
@[noinline] def runTick : FreeM Tick Nat → Nat
  | .pure a => a
  | .liftBind (.tick m) k => m + runTick (k m)
def walk : Nat → FreeM (StateF Nat) Nat
  | 0 => FreeM.lift .get
  | k + 1 => (FreeM.lift .get).bind fun s => (FreeM.lift (.set (s + k))).bind fun _ => walk k
def ticks : Nat → FreeM Tick Nat
  | 0 => FreeM.lift (.tick 7)
  | n + 1 => (FreeM.lift (.tick n)).bind fun m => (ticks n).bind fun r => .pure (r + m)
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{run (walk n) 2} {runTick (ticks n)}"
end A989

namespace A990

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α

inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit

@[noinline] def run {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => run (k s) s
    | .set s' => run (k ()) s'
inductive Tick : Type → Type where
  | tick : Nat → Tick Nat
@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)
@[noinline] def withList {F : Type → Type} {α ι : Type} (op : F ι) (xs : List ι) (k : ι → FreeM F α) : FreeM F α :=
  .liftBind op (fun x => k (xs.headD x))
@[noinline] def runTick : FreeM Tick Nat → Nat
  | .pure a => a
  | .liftBind (.tick m) k => m + runTick (k m)
@[noinline] def ticks : Nat → FreeM Tick Nat
  | 0 => .pure 0
  | n + 1 => withList (.tick n) [1, 2] fun m => (ticks n).bind fun r => .pure (r + m)
@[noinline] def prog : Nat → FreeM (StateF Nat) Nat
  | 0 => .liftBind .get .pure
  | n + 1 => withList .get [n] fun s => .liftBind (.set (s + n)) fun _ => prog n
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{runTick (ticks n)} {run (prog n) 5}"
end A990

namespace A991

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α

inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit

@[noinline] def run {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => run (k s) s
    | .set s' => run (k ()) s'
inductive Tick : Type → Type where
  | tick : Nat → Tick Nat
@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)
@[noinline] def withList {F : Type → Type} {α ι : Type} (op : F ι) (xs : List ι) (k : ι → FreeM F α) : FreeM F α :=
  .liftBind op (fun x => k (xs.headD x))
@[noinline] def runTick : FreeM Tick Nat → Nat
  | .pure a => a
  | .liftBind (.tick m) k => m + runTick (k m)
@[noinline] def ticks : Nat → FreeM Tick Nat
  | 0 => .pure 0
  | n + 1 => withList (.tick n) [1, 2] fun m => (ticks n).bind fun r => .pure (r + m)
@[noinline] def prog : Nat → FreeM (StateF Nat) Nat
  | 0 => .liftBind .get .pure
  | n + 1 => .liftBind .get fun s => .liftBind (.set (s + n)) fun _ => prog n
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{runTick (ticks n)} {run (prog n) 5}"
end A991

namespace A992

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α

inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit

/-- One `ι` type only (`σ` at both operations): must stay native. -/
inductive PeekF (σ : Type) : Type → Type where
  | peek : PeekF σ σ
  | poke : σ → PeekF σ σ

@[noinline] def getS {σ : Type} : FreeM (StateF σ) σ := .liftBind .get .pure
@[noinline] def setS {σ : Type} (s : σ) : FreeM (StateF σ) PUnit := .liftBind (.set s) .pure

@[noinline] def run {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => run (k s) s
    | .set s' => run (k ()) s'

@[noinline] def runPeek {σ α : Type} : FreeM (PeekF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .peek => runPeek (k s) s
    | .poke s' => runPeek (k s') s'

@[noinline] def peeks : Nat → FreeM (PeekF Nat) Nat
  | 0 => .liftBind .peek .pure
  | n+1 => .liftBind (.poke n) fun s => .liftBind .peek fun t => match peeks n with
    | .pure r => .pure (r + s + t)
    | o => o

structure Prog where
  name : String
  body : FreeM (StateF Nat) Nat
  alt : Option (FreeM (StateF Nat) Nat)

@[noinline] def mkProg (n : Nat) : Prog :=
  { name := s!"p{n}", body := .liftBind .get fun s => .liftBind (.set (s + n)) fun _ => .pure s,
    alt := if n % 2 == 0 then some getS else none }

@[noinline] def runAll (ps : List Prog) (s : Nat) : List (Nat × Nat) :=
  ps.map fun p => match p.alt with
    | some a => run a s
    | none => run p.body s

@[noinline] def liftBindAfter (p : FreeM (StateF Nat) PUnit) : FreeM (StateF Nat) Nat :=
  .liftBind .get fun s => match p with
    | .pure _ => .pure s
    | .liftBind op k => .liftBind op (fun x => match k x with | _ => .pure (s + 1))
@[noinline] def arrOf (n : Nat) : Array (FreeM (StateF Nat) Nat) :=
  (Array.range n).map fun i => if i % 3 == 0 then getS else liftBindAfter (setS i)

/-- `StateF PUnit`: `ι` is `PUnit` at both operations. -/
@[noinline] def unitProg : Nat → FreeM (StateF PUnit) Nat
  | 0 => .pure 0
  | n+1 => .liftBind .get fun _ => .liftBind (.set ()) fun _ => (unitProg n)

@[noinline] def arrLoop (n : Nat) : Array (FreeM (StateF Nat) Nat) := Id.run do
  let mut a := #[]
  for i in [0:n] do
    a := a.push (if i % 3 == 0 then getS else liftBindAfter (setS i))
  return a
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let a := arrOf (n % 9 + 2)
  IO.println s!"{(a.map fun p => (run p n).2).toList}"
  IO.println s!"{((arrLoop (n % 9 + 2)).map fun p => (run p n).2).toList}"
end A992

namespace A993

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit
inductive Tick : Type → Type where
  | tick : Nat → Tick Nat
inductive ReaderF (ρ : Type) : Type → Type where
  | ask : ReaderF ρ ρ
  | tell : String → ReaderF ρ PUnit
@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)
@[noinline] def FreeM.lift {F : Type → Type} {ι : Type} (op : F ι) : FreeM F ι := .liftBind op .pure
@[noinline] def run {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => run (k s) s
    | .set s' => run (k ()) s'
@[noinline] def runR {ρ α : Type} (env : ρ) : FreeM (ReaderF ρ) α → List String → α × List String
  | .pure a, log => (a, log.reverse)
  | .liftBind op k, log => match op with
    | .ask => runR env (k env) log
    | .tell s => runR env (k ()) (s :: log)
@[noinline] def runTick : FreeM Tick Nat → Nat
  | .pure a => a
  | .liftBind (.tick m) k => m + runTick (k m)

/-- E2/E3 shapes: continuations tied to α, nested binds, two instances. -/
@[noinline] def getL {σ : Type} : FreeM (StateF σ) σ := .liftBind .get (fun s => .pure s)
@[noinline] def getK {σ : Type} : FreeM (StateF σ) σ :=
  let k : σ → FreeM (StateF σ) σ := fun s => .pure s
  .liftBind .get k
@[noinline] def getList {σ : Type} : FreeM (StateF σ) (List σ) := .liftBind .get (fun s => .pure [s])
@[noinline] def getPair {σ : Type} : FreeM (StateF σ) (σ × Nat) := .liftBind .get (fun s => .pure (s, 1))
@[noinline] def mapGet {σ β : Type} (f : σ → β) : FreeM (StateF σ) β := .liftBind .get (fun s => .pure (f s))
@[noinline] def modifyS {σ : Type} (f : σ → σ) : FreeM (StateF σ) σ :=
  .liftBind .get fun s => .liftBind (.set (f s)) fun _ => .pure s
@[noinline] def nested (n : Nat) : FreeM (StateF Nat) Nat :=
  getL.bind fun s => (modifyS (· + s + n)).bind fun t => getList.bind fun l => getPair.bind fun p => (mapGet toString).bind fun str => .pure (s + t + l.length + p.2 + str.length)
@[noinline] def nestedS (n : Nat) : FreeM (StateF String) Nat :=
  getL.bind fun s => (modifyS (· ++ s)).bind fun t => (mapGet String.length).bind fun k => .pure (s.length + t.length + k + n)
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ab := "ab"
  IO.println s!"{run (getL (σ := Nat)) n} {run (getK (σ := Nat)) n} {run (getList (σ := Nat)) n} {run (modifyS (· + 1)) n}"
  IO.println s!"{run (getL (σ := String)) ab} {run (modifyS (· ++ ab)) ab}"
end A993

namespace A994

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α

inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit

/-- One `ι` type only (`σ` at both operations): must stay native. -/
inductive PeekF (σ : Type) : Type → Type where
  | peek : PeekF σ σ
  | poke : σ → PeekF σ σ

@[noinline] def getS {σ : Type} : FreeM (StateF σ) σ := .liftBind .get .pure
@[noinline] def setS {σ : Type} (s : σ) : FreeM (StateF σ) PUnit := .liftBind (.set s) .pure

@[noinline] def run : FreeM (StateF Nat) Nat → Nat → Nat × Nat
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => run (k s) s
    | .set s' => run (k ()) s'

@[noinline] def runPeek {σ α : Type} : FreeM (PeekF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .peek => runPeek (k s) s
    | .poke s' => runPeek (k s') s'

@[noinline] def peeks : Nat → FreeM (PeekF Nat) Nat
  | 0 => .liftBind .peek .pure
  | n+1 => .liftBind (.poke n) fun s => .liftBind .peek fun t => match peeks n with
    | .pure r => .pure (r + s + t)
    | o => o

structure Prog where
  name : String
  body : FreeM (StateF Nat) Nat
  alt : Option (FreeM (StateF Nat) Nat)

@[noinline] def mkProg (n : Nat) : Prog :=
  { name := s!"p{n}", body := .liftBind .get fun s => .liftBind (.set (s + n)) fun _ => .pure s,
    alt := if n % 2 == 0 then some getS else none }

@[noinline] def runAll (ps : List Prog) (s : Nat) : List (Nat × Nat) :=
  ps.map fun p => match p.alt with
    | some a => run a s
    | none => run p.body s

@[noinline] def liftBindAfter (p : FreeM (StateF Nat) PUnit) : FreeM (StateF Nat) Nat :=
  .liftBind .get fun s => match p with
    | .pure _ => .pure s
    | .liftBind op k => .liftBind op (fun x => match k x with | _ => .pure (s + 1))
@[noinline] def arrOf (n : Nat) : Array (FreeM (StateF Nat) Nat) :=
  (Array.range n).map fun i => if i % 3 == 0 then getS else liftBindAfter (setS i)

/-- `StateF PUnit`: `ι` is `PUnit` at both operations. -/
@[noinline] def unitProg : Nat → FreeM (StateF PUnit) Nat
  | 0 => .pure 0
  | n+1 => .liftBind .get fun _ => .liftBind (.set ()) fun _ => (unitProg n)

@[noinline] def arrLoop (n : Nat) : Array (FreeM (StateF Nat) Nat) := Id.run do
  let mut a := #[]
  for i in [0:n] do
    a := a.push (if i % 3 == 0 then getS else liftBindAfter (setS i))
  return a
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let a := arrOf (n % 9 + 2)
  IO.println s!"{(a.map fun p => (run p n).2).toList}"
  IO.println s!"{((arrLoop (n % 9 + 2)).map fun p => (run p n).2).toList}"
end A994

namespace A995

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit
@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)
@[noinline] def run {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => run (k s) s
    | .set s' => run (k ()) s'
/-- Programs built inline, so no closed term is shared between instantiations. -/
@[noinline] def progN : Nat → FreeM (StateF Nat) Nat
  | 0 => .liftBind .get fun s => .pure (s + 1)
  | n+1 => .liftBind .get fun s => .liftBind (.set (s + n)) fun _ => progN n
@[noinline] def progS : Nat → FreeM (StateF String) Nat
  | 0 => .liftBind .get fun s => .pure s.length
  | n+1 => .liftBind .get fun s => .liftBind (.set (s ++ toString n)) fun _ => progS n
@[noinline] def progB : Nat → FreeM (StateF Bool) Nat
  | 0 => .liftBind .get fun b => .pure (if b then 1 else 0)
  | n+1 => .liftBind .get fun b => .liftBind (.set (!b)) fun _ => progB n
@[noinline] def progU : Nat → FreeM (StateF PUnit) Nat
  | 0 => .liftBind .get fun _ => .pure 7
  | n+1 => .liftBind .get fun _ => .liftBind (.set ()) fun _ => progU n

mutual
@[noinline] def runA {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => runB (k s) s
    | .set s' => runB (k ()) s'
@[noinline] def runB {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => runA (k s) s
    | .set s' => runA (k ()) s'
end
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{runA (progN n) 5} {runB (progS (n % 30)) "ab"} {runA (progB n) false}"
end A995

def main : IO Unit := do
  IO.println "-- A984"
  A984.caseMain ["a", "b", "c"]
  IO.println "-- A986"
  A986.caseMain ["a", "b", "c"]
  IO.println "-- A987"
  A987.caseMain ["a", "b", "c"]
  IO.println "-- A988"
  A988.caseMain ["4"]
  IO.println "-- A989"
  A989.caseMain ["4"]
  IO.println "-- A990"
  A990.caseMain ["4"]
  IO.println "-- A991"
  A991.caseMain ["4"]
  IO.println "-- A992"
  A992.caseMain ["4"]
  IO.println "-- A993"
  A993.caseMain ["4"]
  IO.println "-- A994"
  A994.caseMain ["4"]
  IO.println "-- A995"
  A995.caseMain ["a", "b", "c"]
