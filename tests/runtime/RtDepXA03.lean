/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `A1046`: T15 step B7's reference dispatch: an `IO.Ref (List Nat)` made and
  used natively, passed by `wrapR` (whose parameter's mono type fixes `List
  Nat`) into `RP`, whose family position other values make ...
- `A1048`: `get2 p := get p ++ "!"` passes its parameter on to `get`, whose
  family slot two refinements make `Box`
- `A1049`: Steps B2 (ii) and B5: docs reviewer 1's counterexample to the
  narrowed B2 (ii), A1042's shape with a list in Pkg's slot.
- `A1066`: (iii): a shared closed term `@swapK ◾ : FreeM (StateF lcAny)
  lcAny`, read at σ := Nat and σ := String, whose program stores the state
  it got back into a `set` operation (the ...
- `A1067`: A rigid Array Nat stored where Array Box is typed and read back:
  the Box table's unbox arm converts the Array by B7's index loop, whose
  primitive Array.getInternal the table's ...
- `A1068`: ByteArray and Array UInt8 (both Vec<u8>) boxed at one existential
  position: the variants are deduplicated by Lean type, not by Rust type,
  and Lower's boxedImpls stops with an internal ...
- `A1069`: A family position at an uninhabited type (Empty): unbox_Empty's
  Unit arm binds `let p: Empty = placeholder()
- `A1070`: A value of List^12 Nat boxed at an existential beside a Nat: Box
  mode's translation time grows exponentially in the nesting depth (depth 5:
  1 s, depth 9: 7 s, depth 13: over 300 s)
- `A1071`: Free state and reader monads in one program (CSLib E01's shape):
  Box mode makes a variant Key(UBox) (a box of a UBox value), so UBox
  becomes recursive behind a Link and loses Clone, and ...
- `A1072`: The D71 breaker's probe P24B (068c02704).
- `A1073`: The D71 breaker's probe P08A (068c02704). -/

namespace A1046

structure RP where
  b : Bool
  r : IO.Ref (List (if b then Nat else String))
@[noinline] def wrapR (r : IO.Ref (List Nat)) : RP := ⟨true, r⟩
@[noinline] def bump (p : RP) : IO Unit := match p with
  | ⟨true, r⟩ => r.modify (fun (xs : List Nat) => xs.map (· + 1))
  | ⟨false, r⟩ => r.modify (fun (xs : List String) => xs.map (· ++ "!"))
@[noinline] def showRP (p : RP) : IO String := match p with
  | ⟨true, r⟩ => do let xs : List Nat := (← r.get); return toString xs
  | ⟨false, r⟩ => do let xs : List String := (← r.get); return toString xs
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let rn ← IO.mkRef (List.range n)
  let rs ← IO.mkRef ["a", toString n]
  let ps : List RP := [wrapR rn, ⟨false, rs⟩]
  for p in ps do bump p
  rn.modify (· ++ [100])
  for p in ps do IO.println (← showRP p)
  IO.println s!"{← rn.get} {← rs.get}"
end A1046

namespace A1048

def T : Bool → Type
  | true => Nat
  | false => String
structure Pkg where
  b : Bool
  v : T b
@[noinline] def get : Pkg → String
  | ⟨true, v⟩ => toString ((show Nat from v) + 1)
  | ⟨false, v⟩ => (show String from v)
@[noinline] def get2 (p : Pkg) : String := get p ++ "!"
@[noinline] def mkN (n : Nat) : Pkg := ⟨true, (n : Nat)⟩
@[noinline] def mkS (s : String) : Pkg := ⟨false, (s : String)⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{get (mkN n)} {get (mkS "s")} {get2 (mkN (n + 1))}"
end A1048

namespace A1049

@[noinline] def rdL (d : Bool) (xs : List (if d then Nat else String)) : Nat :=
  match d, xs with | true, ys => (let zs : List Nat := ys; zs.foldl (· + ·) 0) | false, _ => 0
@[noinline] def mkQ : (c d : Bool) → if c then List (if d then Nat else String) else Nat
  | true, true => ([1, 2] : List Nat) | true, false => (["a"] : List String) | false, _ => (5 : Nat)
@[noinline] def getQ : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, d, xs => rdL d xs | false, _, n => n
def caseMain (a : List String) : IO Unit := IO.println (getQ (a.length < 100) a.isEmpty (mkQ (a.length < 100) a.isEmpty))
end A1049

namespace A1066

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
@[noinline] def swapK {σ : Type} : FreeM (StateF σ) σ :=
  .liftBind .get fun a => .liftBind (.set a) fun _ => .liftBind .get fun b => .pure b
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{run (swapK (σ := Nat)) n} {run (swapK (σ := String)) "ab"}"
end A1066

namespace A1067

structure Pkg where
  b : Bool
  v : if b then Array Nat else Array String
@[noinline] def mkA (n : Nat) : Array Nat := (List.range n).toArray
@[noinline] def mkSA (n : Nat) : Array String := (List.range n).toArray.map (s!"s{·}")
@[noinline] def mkN (n : Nat) : Pkg := ⟨true, mkA n⟩
@[noinline] def mkS (n : Nat) : Pkg := ⟨false, mkSA n⟩
@[noinline] def sumA (xs : Array Nat) : Nat := xs.foldl (· + ·) 0
@[noinline] def rd : Pkg → String
  | ⟨true, v⟩ => toString (sumA v)
  | ⟨false, v⟩ => let w : Array String := v; s!"{w.size}:{w.toList}"
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let ps := #[mkN n, mkS n, mkN 0, mkS 0, mkN 1]
  IO.println s!"{ps.map rd}"
  IO.println s!"{rd (mkN (n * 50000))}"
end A1067

namespace A1068

structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
instance : ToString ByteArray := ⟨fun b => s!"BA{b.toList}"⟩
def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ba := (List.range n).foldl (fun b i => b.push i.toUInt8) ByteArray.empty
  let au : Array UInt8 := (List.range (n+1)).toArray.map (·.toUInt8)
  let xs : List AnyS := [⟨ba⟩, ⟨au⟩]
  IO.println (xs.map (·.show))
end A1068

namespace A1069

def F : Bool → Type
  | true => Nat
  | false => Empty
@[noinline] def get : (b : Bool) → Nat → Option (F b)
  | true, n => some (n + 1 : Nat)
  | false, _ => none
@[noinline] def useE (o : Option Empty) : String := match o with | some e => nomatch e | none => "none"
@[noinline] def useN (o : Option Nat) : Nat := o.getD 0
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 7
  IO.println s!"{useN (get true n)} {useE (get false n)}"
end A1069

namespace A1070

structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
abbrev Deep := List (List (List (List (List (List (List (List (List (List (List (List (Nat))))))))))))
instance : ToString Deep := ⟨fun x => s!"deep{x.length}"⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let d : Deep := [[[[[[[[[[[[n]]]]]]]]]]]]
  let xs : List AnyS := [⟨d⟩, ⟨n⟩]
  IO.println (xs.map (·.show))
end A1070

namespace A1071

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op fun z => FreeM.bind (k z) f
instance {F : Type → Type} : Monad (FreeM F) where
  pure := .pure
  bind := FreeM.bind
def FreeM.lift {F : Type → Type} {ι : Type} (op : F ι) : FreeM F ι := .liftBind op .pure
inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit
inductive ReaderF (σ : Type) : Type → Type where
  | read : ReaderF σ σ
def runS {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind .get k, s => runS (k s) s
  | .liftBind (.set s') k, _ => runS (k PUnit.unit) s'
def runR {σ α : Type} : FreeM (ReaderF σ) α → σ → α
  | .pure a, _ => a
  | .liftBind .read k, s => runR (k s) s
def counter : Nat → FreeM (StateF Nat) Nat
  | 0 => .lift .get
  | k + 1 => do
    let s ← .lift .get
    let _ ← FreeM.lift (StateF.set (s + k))
    counter k
def readProg (n : Nat) : FreeM (ReaderF Nat) String := do
  let x ← .lift .read
  let y ← .lift .read
  pure s!"{x * n + y}"
def caseMain (args : List String) : IO Unit := do
  for n in args.filterMap String.toNat? do
    let (a, s) := runS (counter n) 5
    IO.println s!"n={n}: state {a} {s} {(runS (counter n) 0).1} reader {runR (readProg n) 7}"
end A1071

namespace A1072

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
  IO.println (runLog (runState (getS (σ := Nat)) n) [])
  IO.println (runLog (runState (getS (σ := String)) "q") [])
end A1072

namespace A1073

/- P08: type-class dictionaries carrying dependent data: Type members, packed instances, Σ lists. -/
class Container (c : Type) where
  Elem : Type
  toList : c → List Elem
  showE : Elem → String
  combine : Elem → Elem → Elem

instance : Container (List Nat) where
  Elem := Nat
  toList := id
  showE := toString
  combine := (· + ·)

instance : Container String where
  Elem := Char
  toList s := s.toList
  showE c := c.toString
  combine a b := if a < b then b else a

instance : Container (Array (String × Nat)) where
  Elem := String × Nat
  toList a := a.toList
  showE p := s!"{p.1}={p.2}"
  combine a b := (a.1 ++ b.1, a.2 + b.2)

@[noinline] def summary [inst : Container c] (x : c) : String :=
  let es := Container.toList x
  match es with
  | [] => "empty"
  | e :: r => Container.showE (r.foldl (Container.combine (c := c)) e) ++ s!" of {es.length}"

structure AnyC where
  {c : Type}
  [inst : Container c]
  val : c

@[noinline] def AnyC.summary : AnyC → String
  | @AnyC.mk _ _ v => A1073.summary v
@[noinline] def AnyC.first? : AnyC → Option String
  | @AnyC.mk c _ v => match (Container.toList v : List (Container.Elem c)) with
    | [] => none
    | e :: _ => some (Container.showE (c := c) e)

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let cs : List AnyC := [⟨List.range n⟩, ⟨s!"hello{n}"⟩, ⟨#[("a", n), ("b", 1)]⟩, ⟨("" : String)⟩]
  for c in cs do IO.println s!"{c.summary} {c.first?}"
end A1073

def main : IO Unit := do
  IO.println "-- A1046"
  A1046.caseMain ["x", "y"]
  IO.println "-- A1048"
  A1048.caseMain ["7"]
  IO.println "-- A1049"
  A1049.caseMain ["x"]
  IO.println "-- A1066"
  A1066.caseMain ["2"]
  IO.println "-- A1067"
  A1067.caseMain ["2"]
  IO.println "-- A1068"
  A1068.caseMain ["0"]
  IO.println "-- A1069"
  A1069.caseMain ["0"]
  IO.println "-- A1070"
  A1070.caseMain ["3"]
  IO.println "-- A1071"
  A1071.caseMain ["10"]
  IO.println "-- A1072"
  A1072.caseMain ["3"]
  IO.println "-- A1073"
  A1073.caseMain ["3"]
