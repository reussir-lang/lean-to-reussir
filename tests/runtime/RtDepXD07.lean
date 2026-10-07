/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `D71BreakerP22`: Refs crossing representations: IO.Ref String / Array
  natively and in family positions.
- `D71BreakerP24A`: Effect handlers: a free monad over a sum of functors,
  handled in stages at several state types.
- `D71BreakerP24C`: Effect handlers: a free monad over a sum of functors,
  handled in stages at several state types.
- `D71BreakerP24D`: Shared closed getL under a two-stage handler without a
  sum functor
- `D71BreakerP24E`: Effect handlers: a free monad over a sum of functors,
  handled in stages at several state types.
- `D71BreakerP24F`: Effect handlers: a free monad over a sum of functors,
  handled in stages at several state types.
- `D71BreakerP25`: Mutual recursion and nested dependent records (a Pkg
  inside a Pkg's family position).
- `D71BreakerP27`: Option / Except / Sum at family positions with shared
  closed none/[]
- `D71BreakerP28`: One-field structures, Fin, Subtype and scalars at family
  positions (mono-equal and mono-different types).
- `D71BreakerP29`: Function values of several arities and kinds at one
  family position, applied both ways
- `D71BreakerP30`: Closed shared terms holding functions whose results or
  arguments are the reader's type -/

namespace D71BreakerP22
/- P22: refs crossing representations: IO.Ref String / Array natively and in family positions. -/
structure RS where
  b : Bool
  r : IO.Ref (if b then String else Nat)
structure RA where
  b : Bool
  r : IO.Ref (Array (if b then Nat else String))

@[noinline] def wrapS (r : IO.Ref String) : RS := RS.mk true r
@[noinline] def wrapA (r : IO.Ref (Array Nat)) : RA := RA.mk true r
@[noinline] def bumpS : RS → IO Unit
  | ⟨true, r⟩ => r.modify (fun (s : String) => s ++ "!")
  | ⟨false, r⟩ => r.modify (fun (n : Nat) => n + 1)
@[noinline] def showS : RS → IO String
  | ⟨true, r⟩ => do let s : String := ← r.get; return s
  | ⟨false, r⟩ => do let n : Nat := ← r.get; return toString n
@[noinline] def bumpA : RA → IO Unit
  | ⟨true, r⟩ => r.modify (fun (a : Array Nat) => a.push a.size)
  | ⟨false, r⟩ => r.modify (fun (a : Array String) => a.push "x")
@[noinline] def showA : RA → IO String
  | ⟨true, r⟩ => do let a : Array Nat := ← r.get; return toString a
  | ⟨false, r⟩ => do let a : Array String := ← r.get; return toString a

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let rs ← IO.mkRef (toString n)
  let rn ← IO.mkRef n
  let items : List RS := [wrapS rs, RS.mk false rn]
  for it in items do bumpS it
  rs.modify (· ++ "?"); rn.modify (· * 2)
  for it in items do IO.println (← showS it)
  IO.println s!"{← rs.get} {← rn.get}"
  let ra ← IO.mkRef (Array.range n)
  let rb ← IO.mkRef #["a"]
  let arrs : List RA := [wrapA ra, RA.mk false rb]
  for it in arrs do bumpA it
  ra.modify (·.push 100)
  for it in arrs do IO.println (← showA it)
  IO.println s!"{← ra.get} {← rb.get}"
end D71BreakerP22

namespace D71BreakerP24A
/- P24: effect handlers: a free monad over a sum of functors, handled in stages at several state types. -/
inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | put : σ → StateF σ PUnit
inductive LogF : Type → Type where
  | log : String → LogF PUnit
inductive SumF (F G : Type → Type) : Type → Type where
  | inl : F ι → SumF F G ι
  | inr : G ι → SumF F G ι

@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)
instance {F : Type → Type} : Monad (FreeM F) where
  pure := .pure
  bind := FreeM.bind

def getS {σ : Type} : FreeM (SumF (StateF σ) LogF) σ := .liftBind (.inl .get) .pure
def putS {σ : Type} (s : σ) : FreeM (SumF (StateF σ) LogF) PUnit := .liftBind (.inl (.put s)) .pure
def logS {σ : Type} (m : String) : FreeM (SumF (StateF σ) LogF) PUnit := .liftBind (.inr (.log m)) .pure

/- handle the state layer, leaving the log layer -/
@[noinline] def runState {σ α : Type} : FreeM (SumF (StateF σ) LogF) α → σ → FreeM LogF (α × σ)
  | .pure a, s => .pure (a, s)
  | .liftBind (.inl .get) k, s => runState (k s) s
  | .liftBind (.inl (.put s')) k, _ => runState (k ()) s'
  | .liftBind (.inr op) k, s => .liftBind op (fun i => runState (k i) s)

@[noinline] def runLog {α : Type} : FreeM LogF α → List String → α × List String
  | .pure a, l => (a, l.reverse)
  | .liftBind (.log m) k, l => runLog (k ()) (m :: l)

@[noinline] def prog {σ : Type} (f : σ → σ) (sh : σ → String) : Nat → FreeM (SumF (StateF σ) LogF) Nat
  | 0 => do let s ← getS; logS (sh s); pure 0
  | n + 1 => do let s ← getS; putS (f s); logS s!"step {n}: {sh s}"; let r ← prog f sh n; pure (r + 1)

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 2
  IO.println (runLog (runState (prog (· + 3) toString n) n) [])
  IO.println (runLog (runState (prog (· ++ "x") id n) (toString n)) ["init"])
end D71BreakerP24A

namespace D71BreakerP24C
/- P24: effect handlers: a free monad over a sum of functors, handled in stages at several state types. -/
inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | put : σ → StateF σ PUnit
inductive LogF : Type → Type where
  | log : String → LogF PUnit
inductive SumF (F G : Type → Type) : Type → Type where
  | inl : F ι → SumF F G ι
  | inr : G ι → SumF F G ι

@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)
instance {F : Type → Type} : Monad (FreeM F) where
  pure := .pure
  bind := FreeM.bind

def getS {σ : Type} : FreeM (SumF (StateF σ) LogF) σ := .liftBind (.inl .get) .pure
def putS {σ : Type} (s : σ) : FreeM (SumF (StateF σ) LogF) PUnit := .liftBind (.inl (.put s)) .pure
def logS {σ : Type} (m : String) : FreeM (SumF (StateF σ) LogF) PUnit := .liftBind (.inr (.log m)) .pure

@[noinline] def runAll {σ α : Type} : FreeM (SumF (StateF σ) LogF) α → σ → List String → α × σ × List String
  | .pure a, s, l => (a, s, l.reverse)
  | .liftBind (.inl .get) k, s, l => runAll (k s) s l
  | .liftBind (.inl (.put s')) k, _, l => runAll (k ()) s' l
  | .liftBind (.inr (.log m)) k, s, l => runAll (k ()) s (m :: l)
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 2
  IO.println (runAll (getS (σ := Nat)) n [])
  IO.println (runAll (getS (σ := String)) "q" [])
end D71BreakerP24C

namespace D71BreakerP24D
/- P24D: shared closed getL under a two-stage handler without a sum functor -/
inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | put : σ → StateF σ PUnit
inductive LogF : Type → Type where
  | log : String → LogF PUnit
def getL {σ : Type} : FreeM (StateF σ) σ := .liftBind .get .pure
@[noinline] def runState {σ α : Type} : FreeM (StateF σ) α → σ → FreeM LogF (α × σ)
  | .pure a, s => .liftBind (.log "done") (fun _ => .pure (a, s))
  | .liftBind .get k, s => runState (k s) s
  | .liftBind (.put s') k, _ => runState (k ()) s'
@[noinline] def runLog {α : Type} : FreeM LogF α → List String → α × List String
  | .pure a, l => (a, l.reverse)
  | .liftBind (.log m) k, l => runLog (k ()) (m :: l)
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 2
  IO.println (runLog (runState (getL (σ := Nat)) n) [])
  IO.println (runLog (runState (getL (σ := String)) "q") [])
end D71BreakerP24D

namespace D71BreakerP24E
/- P24: effect handlers: a free monad over a sum of functors, handled in stages at several state types. -/
inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | put : σ → StateF σ PUnit
inductive ReaderF (ρ : Type) : Type → Type where
  | ask : ReaderF ρ ρ
inductive LogF : Type → Type where
  | log : String → LogF PUnit
inductive SumF (F G : Type → Type) : Type → Type where
  | inl : F ι → SumF F G ι
  | inr : G ι → SumF F G ι

@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)
instance {F : Type → Type} : Monad (FreeM F) where
  pure := .pure
  bind := FreeM.bind

def getS {σ : Type} : FreeM (SumF (StateF σ) LogF) σ := .liftBind (.inl .get) .pure
def putS {σ : Type} (s : σ) : FreeM (SumF (StateF σ) LogF) PUnit := .liftBind (.inl (.put s)) .pure
def logS {σ : Type} (m : String) : FreeM (SumF (StateF σ) LogF) PUnit := .liftBind (.inr (.log m)) .pure

/- handle the state layer, leaving the log layer -/
@[noinline] def runState {σ α : Type} : FreeM (SumF (StateF σ) LogF) α → σ → FreeM LogF (α × σ)
  | .pure a, s => .pure (a, s)
  | .liftBind (.inl .get) k, s => runState (k s) s
  | .liftBind (.inl (.put s')) k, _ => runState (k ()) s'
  | .liftBind (.inr op) k, s => .liftBind op (fun i => runState (k i) s)

@[noinline] def runLog {α : Type} : FreeM LogF α → List String → α × List String
  | .pure a, l => (a, l.reverse)
  | .liftBind (.log m) k, l => runLog (k ()) (m :: l)

@[noinline] def prog {σ : Type} (f : σ → σ) (sh : σ → String) : Nat → FreeM (SumF (StateF σ) LogF) Nat
  | 0 => do let s ← getS; logS (sh s); pure 0
  | n + 1 => do let s ← getS; putS (f s); logS s!"step {n}: {sh s}"; let r ← prog f sh n; pure (r + 1)

def askR {ρ σ : Type} : FreeM (SumF LogF (ReaderF ρ)) ρ := .liftBind (.inr .ask) .pure
@[noinline] def runR {ρ α : Type} (env : ρ) : FreeM (SumF LogF (ReaderF ρ)) α → List String → α × List String
  | .pure a, l => (a, l.reverse)
  | .liftBind (.inl (.log m)) k, l => runR env (k ()) (m :: l)
  | .liftBind (.inr .ask) k, l => runR env (k env) l
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 2
  IO.println (runR n (askR (ρ := Nat) (σ := Nat)) [])
  IO.println (runR "e" (askR (ρ := String) (σ := Nat)) ["i"])
end D71BreakerP24E

namespace D71BreakerP24F
/- P24: effect handlers: a free monad over a sum of functors, handled in stages at several state types. -/
inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | put : σ → StateF σ PUnit
inductive LogF : Type → Type where
  | log : String → LogF PUnit
inductive SumF (F G : Type → Type) : Type → Type where
  | inl : F ι → SumF F G ι
  | inr : G ι → SumF F G ι

@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op (fun x => (k x).bind f)
instance {F : Type → Type} : Monad (FreeM F) where
  pure := .pure
  bind := FreeM.bind

def getS {σ : Type} : FreeM (SumF (StateF σ) LogF) σ := .liftBind (.inl .get) .pure
def putS {σ : Type} (s : σ) : FreeM (SumF (StateF σ) LogF) PUnit := .liftBind (.inl (.put s)) .pure
def logS {σ : Type} (m : String) : FreeM (SumF (StateF σ) LogF) PUnit := .liftBind (.inr (.log m)) .pure

/- handle the state layer, leaving the log layer -/
@[noinline] def runState {σ α : Type} : FreeM (SumF (StateF σ) LogF) α → σ → FreeM LogF (α × σ)
  | .pure a, s => .pure (a, s)
  | .liftBind (.inl .get) k, s => runState (k s) s
  | .liftBind (.inl (.put s')) k, _ => runState (k ()) s'
  | .liftBind (.inr op) k, s => .liftBind op (fun i => runState (k i) s)

@[noinline] def runLog {α : Type} : FreeM LogF α → List String → α × List String
  | .pure a, l => (a, l.reverse)
  | .liftBind (.log m) k, l => runLog (k ()) (m :: l)

@[noinline] def prog {σ : Type} (f : σ → σ) (sh : σ → String) : Nat → FreeM (SumF (StateF σ) LogF) Nat
  | 0 => do let s ← getS; logS (sh s); pure 0
  | n + 1 => do let s ← getS; putS (f s); logS s!"step {n}: {sh s}"; let r ← prog f sh n; pure (r + 1)

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 2
  IO.println (runLog (runState (logS (σ := Nat) "hi") n) [])
  IO.println (runLog (runState (logS (σ := String) "hi") (toString n)) [])
  IO.println (runLog (runState (do logS (σ := Nat) "a"; logS "b"; pure 1) n) [])
end D71BreakerP24F

namespace D71BreakerP25
/- P25: mutual recursion and nested dependent records (a Pkg inside a Pkg's family position). -/
structure Pkg where
  b : Bool
  v : if b then Nat else String

structure Outer where
  c : Bool
  w : if c then Pkg else List Pkg

@[noinline] def mkP (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
@[noinline] def mkO (n : Nat) : Outer := if n % 3 = 0 then ⟨true, mkP n⟩ else ⟨false, (List.range (n % 4)).map mkP⟩

mutual
@[noinline] partial def showP : Pkg → String
  | ⟨true, v⟩ => let w : Nat := v; if w > 0 then s!"N{w}<" ++ showO (mkO (w - 1)) ++ ">" else "N0"
  | ⟨false, v⟩ => let s : String := v; s!"S{s}"
@[noinline] partial def showO : Outer → String
  | ⟨true, w⟩ => let p : Pkg := w; "O(" ++ showP p ++ ")"
  | ⟨false, w⟩ => let ps : List Pkg := w; "L" ++ toString (ps.map showP)
end

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  for i in List.range (n + 2) do IO.println (showO (mkO i))
end D71BreakerP25

namespace D71BreakerP27
/- P27: Option / Except / Sum at family positions with shared closed none/[]; nested Option. -/
structure OP where
  b : Bool
  v : Option (if b then Nat else String)
structure EP where
  b : Bool
  e : Except String (List (if b then Nat else String))

@[noinline] def mkOP (n : Nat) : OP :=
  if n % 2 = 0 then ⟨true, if n % 4 = 0 then none else some n⟩ else ⟨false, if n % 3 = 0 then none else some (toString n)⟩
@[noinline] def showOP : OP → String
  | ⟨true, v⟩ => let o : Option Nat := v; toString o
  | ⟨false, v⟩ => let o : Option String := v; toString o
@[noinline] def mkEP (n : Nat) : EP :=
  if n % 2 = 0 then ⟨true, if n % 4 = 0 then .error "even-fail" else .ok (List.range n)⟩
  else ⟨false, if n % 3 = 0 then .error "odd-fail" else .ok []⟩
@[noinline] def showEP : EP → String
  | ⟨true, e⟩ => let x : Except String (List Nat) := e; match x with | .ok l => toString l | .error m => m
  | ⟨false, e⟩ => let x : Except String (List String) := e; match x with | .ok l => toString l | .error m => m

@[noinline] def flipOP : OP → OP
  | ⟨true, v⟩ => let o : Option Nat := v; ⟨false, o.map toString⟩
  | ⟨false, v⟩ => let o : Option String := v; ⟨true, o.map String.length⟩

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ops := (List.range (n + 4)).map mkOP
  IO.println (ops.map showOP)
  IO.println ((ops.map flipOP).map showOP)
  IO.println (((List.range (n + 4)).map mkEP).map showEP)
end D71BreakerP27

namespace D71BreakerP28
/- P28: one-field structures, Fin, Subtype and scalars at family positions (mono-equal and mono-different types). -/
structure W where
  n : Nat
structure Pkg where
  b : Bool
  v : if b then W else Nat
structure Pkg2 where
  b : Bool
  v : if b then Fin 10 else UInt8
structure Pkg3 where
  b : Bool
  v : if b then { n : Nat // n > 0 } else String

@[noinline] def mk1 (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, ⟨n⟩⟩ else ⟨false, n + 100⟩
@[noinline] def rd1 : Pkg → Nat
  | ⟨true, v⟩ => let w : W := v; w.n * 2
  | ⟨false, v⟩ => let k : Nat := v; k
@[noinline] def mk2 (n : Nat) : Pkg2 := if n % 2 = 0 then ⟨true, ⟨n % 10, Nat.mod_lt _ (by decide)⟩⟩ else ⟨false, (n * 7).toUInt8⟩
@[noinline] def rd2 : Pkg2 → Nat
  | ⟨true, v⟩ => let f : Fin 10 := v; f.val + 1000
  | ⟨false, v⟩ => let u : UInt8 := v; u.toNat
@[noinline] def mk3 (n : Nat) : Pkg3 := if n % 2 = 0 then ⟨true, ⟨n + 1, Nat.succ_pos n⟩⟩ else ⟨false, toString n⟩
@[noinline] def rd3 : Pkg3 → String
  | ⟨true, v⟩ => let s : { n : Nat // n > 0 } := v; toString s.val
  | ⟨false, v⟩ => let s : String := v; s ++ "."

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let xs := List.range (n + 2)
  IO.println (xs.map (fun i => rd1 (mk1 i)))
  IO.println (xs.map (fun i => rd2 (mk2 i)))
  IO.println (xs.map (fun i => rd3 (mk3 i)))
end D71BreakerP28

namespace D71BreakerP29
/- P29: function values of several arities and kinds at one family position, applied both ways -/
structure Op where
  b : Bool
  f : if b then (Nat → Nat → Nat) else String
@[noinline] def add3 (a b c : Nat) : Nat := a + b * c
@[noinline] def mkOp (n : Nat) : Op :=
  match n % 5 with
  | 0 => ⟨true, Nat.add⟩
  | 1 => ⟨true, fun a b => a * b + n⟩
  | 2 => ⟨true, add3 n⟩
  | 3 => ⟨true, (Nat.sub · ·)⟩
  | _ => ⟨false, s!"s{n}"⟩
@[noinline] def apBoth (o : Op) (x y : Nat) : String := match o with
  | ⟨true, f⟩ => let g : Nat → Nat → Nat := f; let h := g x; s!"{g x y}/{h y}/{(h (y + 1))}"
  | ⟨false, f⟩ => let s : String := f; s
@[noinline] def compose (o p : Op) : Op := match o, p with
  | ⟨true, f⟩, ⟨true, g⟩ => let f : Nat → Nat → Nat := f; let g : Nat → Nat → Nat := g; ⟨true, fun a b => f (g a b) b⟩
  | ⟨false, s⟩, _ => let s : String := s; ⟨false, s ++ "."⟩
  | _, ⟨false, s⟩ => let s : String := s; ⟨false, "." ++ s⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ops := (List.range (n + 5)).map mkOp
  IO.println (ops.map (apBoth · n 2))
  IO.println ((ops.zip ops.reverse).map (fun (a, b) => apBoth (compose a b) n 3))
end D71BreakerP29

namespace D71BreakerP30
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
  IO.println s!"{useAccumum idAccumum n n} {useAccumum idAccumum (toString n) n} {useAccumum idAccumum [n] n}"
  IO.println s!"{usePair pairFn n} {usePair pairFn (toString n)}"
  let g : Gen (List Nat) := emptyGen
  let h : Gen (List String) := emptyGen
  IO.println s!"{g.tag + h.tag} {(g.next n).length + (h.next n).length}"
end D71BreakerP30

def main : IO Unit := do
  IO.println "-- D71BreakerP22"
  D71BreakerP22.caseMain ["3"]
  IO.println "-- D71BreakerP24A"
  D71BreakerP24A.caseMain ["3"]
  IO.println "-- D71BreakerP24C"
  D71BreakerP24C.caseMain ["3"]
  IO.println "-- D71BreakerP24D"
  D71BreakerP24D.caseMain ["3"]
  IO.println "-- D71BreakerP24E"
  D71BreakerP24E.caseMain ["3"]
  IO.println "-- D71BreakerP24F"
  D71BreakerP24F.caseMain ["3"]
  IO.println "-- D71BreakerP25"
  D71BreakerP25.caseMain ["6"]
  IO.println "-- D71BreakerP27"
  D71BreakerP27.caseMain ["5"]
  IO.println "-- D71BreakerP28"
  D71BreakerP28.caseMain ["4"]
  IO.println "-- D71BreakerP29"
  D71BreakerP29.caseMain ["3"]
  IO.println "-- D71BreakerP30"
  D71BreakerP30.caseMain ["3"]
