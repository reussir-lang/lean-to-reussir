/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `A958`: Existentials of a recursive inductive: a free monad over `StateF`,
  whose `liftBind`'s `ι` is `Nat` at `get` and `PUnit` at `set` along one
  value, is `FreeM<StateF<Nat>, Nat, ...
- `A959`: A continuation passed into a marked field and also stored in a
  list (`stored`): Rule 17.17's dyn-key check fails on `stored`, so
  dependent mode fails closed into T13's refusal ...
- `A960`: A free monad's continuation whose `α` is a type parameter of the
  declaration that passes it into a marked field (`getL {σ} := .liftBind
  .get (fun s => .pure s)`, ...
- `A961`: A refusal at a partial application inside a continuation (`mk n :=
  .liftBind .get fun s => .liftBind (.set (s + n)) fun _ => getS`, and a
  left-nested bind) is a trigger too: its ...
- `A962`: A generic helper (`FreeM.mapF`) shared by a marked instantiation
  (`FreeM (StateF Nat)`) and a native one (`FreeM Tick Nat`) stays generic
  in the slot, so the native program ...
- `A963`: A free monad over a custom command type with a partial IO
  interpreter
- `A964`: One `ι` type per value (`PeekF σ`, `σ` at both operations
- `A965`: A generic continuation-passing smart constructor (`withCont`)
  shared by a marked instantiation (`prog2`'s `FreeM (StateF Nat)`) and a
  native one (`ticks2`'s `FreeM Tick`): ...
- `A968`: Rank-2 parameters: `foldFreeM`'s handler `h : {ι : Type} → F ι →
  (ι → β) → β`, passed a lambda whose `cases` on `op` calls `k` at `Nat` and
  at `PUnit`, over a `FreeM (StateF ...
- `A969`: Rank-2 parameters: `both (h : {ι : Type} → ι → ι)` applied at
  `Nat` and `String`: one group for `h`'s domain and codomain, site-keyed as
  the union of `Nat` and `String` with ...
- `A970`: Rank-2 parameters: a group one type reaches keeps run 1's typing
  (`app (h : {ι : Type} → ι → ι) (x : α) := h x` generic, `useNat` at
  `Nat`). -/

namespace A958

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α

inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit

@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)

@[noinline] def getS {σ : Type} : FreeM (StateF σ) σ := .liftBind .get .pure
@[noinline] def setS {σ : Type} (s : σ) : FreeM (StateF σ) PUnit := .liftBind (.set s) .pure

@[noinline] def run {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => run (k s) s
    | .set s' => run (k ()) s'

@[noinline] def prog : Nat → FreeM (StateF Nat) Nat
  | 0 => getS
  | n+1 => getS.bind fun s => (setS (s + n)).bind fun _ => prog n

inductive Tick : Type → Type where
  | tick : Nat → Tick Nat

/-- An unrelated instantiation, `ι = Nat` at every node: it stays native (`FreeM<Tick, Nat, Nat>`). -/
@[noinline] def ticks : Nat → FreeM Tick Nat
  | 0 => .pure 0
  | n + 1 => .liftBind (.tick n) fun m => match ticks n with
    | .pure r => .pure (r + m)
    | other => other

@[noinline] def runTick : FreeM Tick Nat → Nat
  | .pure a => a
  | .liftBind (.tick m) k => m + runTick (k m)

/-- The continuation read out of a `liftBind .get` node, stored at `σ → FreeM`: step 3 (d) wraps it. -/
@[noinline] def peel (p : FreeM (StateF Nat) Nat) : Option (Nat → FreeM (StateF Nat) Nat) :=
  match p with
  | .liftBind .get k => some k
  | _ => none

def caseMain (args : List String) : IO Unit := do
  let r := run (prog (3 + args.length)) 5
  IO.println s!"{r.1} {r.2}"
  match peel (prog (2 + args.length)) with
  | some k => let r2 := run (k (7 + args.length)) 1; IO.println s!"{r2.1} {r2.2}"
  | none => IO.println "none"
  IO.println (runTick (ticks (4 + args.length)))
end A958

namespace A959

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α

inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit

inductive Tick : Type → Type where
  | tick : Nat → Tick Nat

@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)

/-- A generic helper shared by the marked StateF program and the native Tick program. -/
@[noinline] def FreeM.mapF {F : Type → Type} {α β : Type} (f : α → β) : FreeM F α → FreeM F β
  | .pure a => .pure (f a)
  | .liftBind op k => .liftBind op (fun x => (k x).mapF f)

@[noinline] def getS {σ : Type} : FreeM (StateF σ) σ := .liftBind .get .pure
@[noinline] def setS {σ : Type} (s : σ) : FreeM (StateF σ) PUnit := .liftBind (.set s) .pure
/-- getS-like: the result shares the instance's type twice over. -/
@[noinline] def getS2 {σ : Type} : FreeM (StateF σ) (σ × σ) := .liftBind .get (fun s => .pure (s, s))

@[noinline] def run {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => run (k s) s
    | .set s' => run (k ()) s'

@[noinline] def prog : Nat → FreeM (StateF Nat) Nat
  | 0 => getS
  | n+1 => getS.bind fun s => (setS (s + n)).bind fun _ => prog n

@[noinline] def progS : Nat → FreeM (StateF String) Nat
  | 0 => getS2.mapF fun (a, b) => a.length + b.length
  | n+1 => getS.bind fun s => (setS (s ++ "x")).bind fun _ => progS n

@[noinline] def ticks : Nat → FreeM Tick Nat
  | 0 => .pure 0
  | n + 1 => (FreeM.liftBind (.tick n) .pure).bind fun m => (ticks n).mapF (· + m)

@[noinline] def runTick : FreeM Tick Nat → Nat
  | .pure a => a
  | .liftBind (.tick m) k => m + runTick (k m)

/-- A continuation passed into a marked field and also stored in a list and applied directly. -/
@[noinline] def stored (n : Nat) : Nat × Nat × Nat :=
  let k : Nat → FreeM (StateF Nat) Nat := fun x => .pure (x + 1)
  let p : FreeM (StateF Nat) Nat := .liftBind .get k
  let ks := [k, k]
  let r := run p n
  let r2 := run ((ks.headD k) (n + 10)) 0
  let r3 := run (.liftBind (.set (n + 20)) (fun _ => (ks.getLastD k) 5)) 0
  (r.1, r2.1, r3.2)

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let r := run (prog n) 5
  IO.println s!"{r.1} {r.2}"
  let rs := run (progS (n % 50)) "ab"
  IO.println s!"{rs.1} {rs.2.length}"
  IO.println s!"{runTick (ticks (n % 1000))}"
  IO.println s!"{stored n}"
  let m := run ((getS2 (σ := Nat)).mapF fun (a, b) => a + b + 1) n
  IO.println s!"{m.1} {m.2}"
end A959

namespace A960

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

/-- V1: `getS` with a lambda in place of `.pure`. -/
@[noinline] def getL {σ : Type} : FreeM (StateF σ) σ := .liftBind .get (fun s => .pure s)
/-- V2: the lambda let-bound first. -/
@[noinline] def getK {σ : Type} : FreeM (StateF σ) σ :=
  let k : σ → FreeM (StateF σ) σ := fun s => .pure s
  .liftBind .get k
/-- V3: the parameter captured and returned in `α` after a `set`. -/
@[noinline] def modifyS {σ : Type} (f : σ → σ) : FreeM (StateF σ) σ :=
  .liftBind .get fun s => .liftBind (.set (f s)) fun _ => .pure s
/-- V4: the parameter used only at a flat position. -/
@[noinline] def modifyF {σ : Type} (f : σ → σ) : FreeM (StateF σ) σ :=
  .liftBind .get fun s => .liftBind (.set (f s)) fun _ => .pure (f s)
/-- V5: the parameter under a `List` in `α`. -/
@[noinline] def getList {σ : Type} : FreeM (StateF σ) (List σ) := .liftBind .get (fun s => .pure [s])
/-- V6: the parameter returned through a `set`'s unit continuation at `Nat`, not `σ`. -/
@[noinline] def tick (n : Nat) : FreeM (StateF Nat) Nat :=
  .liftBind .get fun s => .liftBind (.set (s + n)) fun _ => .pure s

@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)
def FreeM.lift {F : Type → Type} {ι : Type} (op : F ι) : FreeM F ι := .liftBind op .pure
def natsL : Nat → FreeM (StateF Nat) Nat
  | 0 => FreeM.lift .get
  | n + 1 => (FreeM.lift .get).bind fun s => (FreeM.lift (.set (s + n))).bind fun _ => natsL n
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{run (getL (σ := Nat)) n} {run (getK (σ := Nat)) n} {run (modifyS (· + 1)) n} {run (modifyF (· * 2)) n}"
  IO.println s!"{run (getList (σ := Nat)) n} {run (tick 5) n}"
  IO.println s!"{run (natsL (n % 6)) 2}"
end A960

namespace A961

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit
@[noinline] def getS {σ : Type} : FreeM (StateF σ) σ := .liftBind .get .pure
@[noinline] def run {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => run (k s) s
    | .set s' => run (k ()) s'
@[noinline] def mk (n : Nat) : FreeM (StateF Nat) Nat :=
  .liftBind .get fun s => .liftBind (.set (s + n)) fun _ => getS
@[noinline] def listOf (n : Nat) : List (FreeM (StateF Nat) Nat) := (List.range n).map mk
@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)
@[noinline] def setS {σ : Type} (s : σ) : FreeM (StateF σ) PUnit := .liftBind (.set s) .pure
/-- A left-nested bind (the tester's V4): refused at a partial application before the trigger read it. -/
def nats : Nat → FreeM (StateF Nat) Nat
  | 0 => getS
  | n + 1 => (getS.bind fun s => setS (s + n)).bind fun _ => nats n
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{(listOf (n % 5 + 1)).map fun p => (run p 1).2}"
  IO.println s!"{run (nats (n % 7)) 2}"
end A961

namespace A962

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α

inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit

inductive Tick : Type → Type where
  | tick : Nat → Tick Nat

@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)

/-- A generic helper shared by the marked StateF program and the native Tick program. -/
@[noinline] def FreeM.mapF {F : Type → Type} {α β : Type} (f : α → β) : FreeM F α → FreeM F β
  | .pure a => .pure (f a)
  | .liftBind op k => .liftBind op (fun x => (k x).mapF f)

@[noinline] def getS {σ : Type} : FreeM (StateF σ) σ := .liftBind .get .pure
@[noinline] def setS {σ : Type} (s : σ) : FreeM (StateF σ) PUnit := .liftBind (.set s) .pure
/-- getS-like: the result shares the instance's type twice over. -/
@[noinline] def getS2 {σ : Type} : FreeM (StateF σ) (σ × σ) := .liftBind .get (fun s => .pure (s, s))

@[noinline] def run {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => run (k s) s
    | .set s' => run (k ()) s'

@[noinline] def prog : Nat → FreeM (StateF Nat) Nat
  | 0 => getS
  | n+1 => getS.bind fun s => (setS (s + n)).bind fun _ => prog n

@[noinline] def ticks : Nat → FreeM Tick Nat
  | 0 => .pure 0
  | n + 1 => (FreeM.liftBind (.tick n) .pure).bind fun m => (ticks n).mapF (· + m)

@[noinline] def runTick : FreeM Tick Nat → Nat
  | .pure a => a
  | .liftBind (.tick m) k => m + runTick (k m)

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let r := run (prog n) 5
  IO.println s!"{r.1} {r.2}"
  IO.println s!"{runTick (ticks (n % 1000))}"
end A962

namespace A963

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)
inductive Cmd : Type → Type where
  | readLine : Cmd String
  | print : String → Cmd PUnit
  | rand : Nat → Cmd Nat
@[noinline] def readLine : FreeM Cmd String := .liftBind .readLine .pure
@[noinline] def print (s : String) : FreeM Cmd PUnit := .liftBind (.print s) .pure
@[noinline] def rand (k : Nat) : FreeM Cmd Nat := .liftBind (.rand k) .pure
partial def interp (seed : Nat) (lines : List String) : FreeM Cmd Nat → IO Unit
  | .pure a => IO.println s!"result {a}"
  | .liftBind op k => match op with
    | .readLine => match lines with
      | l :: ls => interp seed ls (k l)
      | [] => interp seed [] (k "")
    | .print s => do IO.println s; interp seed lines (k ())
    | .rand m => interp (seed * 1103515245 + 12345) lines (k (seed % (m + 1)))
def loop : Nat → FreeM Cmd Nat
  | 0 => .pure 0
  | n + 1 => readLine.bind fun l => (print s!"got [{l}]").bind fun _ => (rand 9).bind fun r => (loop n).bind fun t => .pure (t + r + l.length)
def caseMain (args : List String) : IO Unit := do
  interp 7 args (loop (args.length + 2))
end A963

namespace A964

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α

inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit

/-- One `ι` type only (`σ` at both operations): stays native. -/
inductive PeekF (σ : Type) : Type → Type where
  | peek : PeekF σ σ
  | poke : σ → PeekF σ σ

@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)

@[noinline] def getS {σ : Type} : FreeM (StateF σ) σ := .liftBind .get .pure
@[noinline] def setS {σ : Type} (s : σ) : FreeM (StateF σ) PUnit := .liftBind (.set s) .pure

@[noinline] def run {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => run (k s) s
    | .set s' => run (k ()) s'

@[noinline] def prog : Nat → FreeM (StateF Nat) Nat
  | 0 => getS
  | n+1 => getS.bind fun s => (setS (s + n)).bind fun _ => prog n

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

/-- `StateF PUnit` with a runner of its own: `ι` is `PUnit` at both operations. -/
@[noinline] def runUnit {α : Type} : FreeM (StateF PUnit) α → Nat → α × Nat
  | .pure a, c => (a, c)
  | .liftBind op k, c => match op with
    | .get => runUnit (k ()) (c + 1)
    | .set _ => runUnit (k ()) (c + 2)

@[noinline] def unitProg : Nat → FreeM (StateF PUnit) Nat
  | 0 => .pure 0
  | n+1 => .liftBind .get fun _ => .liftBind (.set ()) fun _ => (unitProg n)

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let r := run (prog n) 5
  IO.println s!"{r.1} {r.2}"
  let p := runPeek (peeks (n % 7)) 1
  IO.println s!"{p.1} {p.2}"
  let u := runUnit (unitProg (n % 9)) 0
  IO.println s!"{u.1} {u.2}"
end A964

namespace A965

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit
inductive Tick : Type → Type where
  | tick : Nat → Tick Nat
@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)
@[noinline] def FreeM.mapF {F : Type → Type} {α β : Type} (f : α → β) : FreeM F α → FreeM F β
  | .pure a => .pure (f a)
  | .liftBind op k => .liftBind op (fun x => (k x).mapF f)
@[noinline] def getS {σ : Type} : FreeM (StateF σ) σ := .liftBind .get .pure
@[noinline] def setS {σ : Type} (s : σ) : FreeM (StateF σ) PUnit := .liftBind (.set s) .pure
@[noinline] def run {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind op k, s => match op with
    | .get => run (k s) s
    | .set s' => run (k ()) s'
@[noinline] def runTick : FreeM Tick Nat → Nat
  | .pure a => a
  | .liftBind (.tick m) k => m + runTick (k m)
@[noinline] def prog : Nat → FreeM (StateF Nat) Nat
  | 0 => getS
  | n+1 => getS.bind fun s => (setS (s + n)).bind fun _ => prog n

/-- A continuation passed through a generic parameter before it enters the marked field. -/
@[noinline] def withCont {F : Type → Type} {α ι : Type} (op : F ι) (k : ι → FreeM F α) : FreeM F α := .liftBind op k
@[noinline] def prog2 : Nat → FreeM (StateF Nat) Nat
  | 0 => withCont .get (fun s => .pure (s + 1))
  | n+1 => withCont .get fun s => withCont (.set (s + n)) fun _ => prog2 n
@[noinline] def ticks2 : Nat → FreeM Tick Nat
  | 0 => withCont (.tick 7) .pure
  | n+1 => withCont (.tick n) fun m => (ticks2 n).mapF (· + m)
/-- `ι` also types a phantom argument, whose element no term binds (the breaker's `withContP`). -/
@[noinline] def withContP {F : Type → Type} {α ι : Type} (op : F ι) (k : ι → FreeM F α) (tag : Option ι) : FreeM F α :=
  match tag with
  | some _ => .liftBind op k
  | none => .liftBind op k
@[noinline] def prog4 : Nat → FreeM (StateF Nat) Nat
  | 0 => withContP .get (fun s => .pure (s + 2)) none
  | n+1 => withContP .get (fun s => withContP (.set (s * 2 + n)) (fun _ => prog4 n) none) (some 0)
@[noinline] def ticks4 : Nat → FreeM Tick Nat
  | 0 => withContP (.tick 7) .pure (some 1)
  | n+1 => withContP (.tick n) (fun m => (ticks4 n).mapF (· + m)) none
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let r := run (prog2 n) 5
  IO.println s!"{r.1} {r.2} {(run (prog n) 1).2}"
  IO.println s!"{runTick (ticks2 (n % 500))}"
  let r4 := run (prog4 n) 3
  IO.println s!"{r4.1} {r4.2} {runTick (ticks4 (n % 500))}"
end A965

namespace A968

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α

inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit

@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)

@[noinline] def getS {σ : Type} : FreeM (StateF σ) σ := .liftBind .get .pure
@[noinline] def setS {σ : Type} (s : σ) : FreeM (StateF σ) PUnit := .liftBind (.set s) .pure

@[noinline] def foldFreeM {F : Type → Type} {α β : Type} (pureCase : α → β)
    (h : {ι : Type} → F ι → (ι → β) → β) : FreeM F α → β
  | .pure a => pureCase a
  | .liftBind op k => h op (fun x => foldFreeM pureCase h (k x))

@[noinline] def countOps (p : FreeM (StateF Nat) Nat) : Nat :=
  foldFreeM (fun _ => 0) (fun op k => match op with | .get => k 0 + 1 | .set _ => k () + 1) p

@[noinline] def prog : Nat → FreeM (StateF Nat) Nat
  | 0 => getS
  | n+1 => getS.bind fun s => (setS (s + n)).bind fun _ => prog n

inductive Tick : Type → Type where
  | tick : Nat → Tick Nat
@[noinline] def ticks : Nat → FreeM Tick Nat
  | 0 => .pure 0
  | n + 1 => .liftBind (.tick n) fun m => (ticks n).bind fun r => .pure (r + m)
@[noinline] def sumTicks (p : FreeM Tick Nat) : Nat :=
  foldFreeM (fun a => a) (fun op k => match op with | .tick m => k m + m) p

@[noinline] def pa (h : {ι : Type} → ι → ι → Nat) (s : String) : Nat :=
  let h1 := h 1
  h1 2 + h s s

def caseMain (args : List String) : IO Unit := do
  IO.println s!"{countOps (prog (3 + args.length))} {sumTicks (ticks (4 + args.length))}"
  IO.println s!"{pa (fun _ _ => 7) (toString args.length)}"
end A968

namespace A969

@[noinline] def both (h : {ι : Type} → ι → ι) (n : Nat) (s : String) : Nat × String := (h n, h s)
@[noinline] def twice {α : Type} (x : α) : α := x

def caseMain (args : List String) : IO Unit := do
  IO.println s!"{both id args.length "x"} {both (fun x => x) (args.length + 1) "y"}"
end A969

namespace A970

@[noinline] def app {α : Type} (h : {ι : Type} → ι → ι) (x : α) : α := h x
@[noinline] def useNat (h : {ι : Type} → ι → ι) (n : Nat) : Nat := h n + 1

def caseMain (args : List String) : IO Unit := do
  IO.println s!"{app id (args.length + 4)} {app (fun x => x) "s"} {useNat id 3}"
end A970

def main : IO Unit := do
  IO.println "-- A958"
  A958.caseMain ["a"]
  IO.println "-- A959"
  A959.caseMain ["5"]
  IO.println "-- A960"
  A960.caseMain ["4"]
  IO.println "-- A961"
  A961.caseMain ["4"]
  IO.println "-- A962"
  A962.caseMain ["4"]
  IO.println "-- A963"
  A963.caseMain ["hello", "world"]
  IO.println "-- A964"
  A964.caseMain ["5"]
  IO.println "-- A965"
  A965.caseMain ["4"]
  IO.println "-- A968"
  A968.caseMain ["a", "b"]
  IO.println "-- A969"
  A969.caseMain ["a", "b"]
  IO.println "-- A970"
  A970.caseMain ["a", "b"]
