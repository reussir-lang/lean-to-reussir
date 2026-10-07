/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `A1085`: Section 3.8's `manual_map` and `needless_match` rows at an
  identity rebuild of an `Option` whose `none` is a default arm: `getG7`'s
  `match d, xs.head? with | true, some a => some a | _, _ => none` keeps,
  ...
- `A1086`: A universe whose denotation holds an arrow, with Σ values holding
  functions: two same-head arms' wrappers capture each other's `Deep`
  variants, so a `Deep` variant's `Boxed<UBox>` impl is written at its inner
  type ...
- `A1087`: A structure whose field is `Nat → Nat` or `String → String →
  String` by a Bool: the Box table's same-head arm between two arrows of
  different arities is a parametric wrapper taking the shorter one's
  arguments, and an ...
- `A1088`: Effect handlers over a free monad of a sum of functors, handled
  in stages at several state types: a relaxed annotation of a reference to a
  generic declaration is retyped with its class's type, so a rebuild at the
  ...
- `A1089`: A foldr whose closed `([], [])` accumulator is read in a generic
  split over dependent records: a static's result is retyped at the
  occurrence that holds the Box slot argument, so its read is no D65
  refusal.
- `A1090`: A cell holding `List (if d then Nat else String)` read under
  refinements whose tail binder nothing reads: no coercion at an unread
  binder, and a conversion no body calls is not admitted (exit 4 before: an
  admitted ...
- `A1091`: R8's cell read through a second refinement: no coercion at an
  unread binder, and a conversion no body calls is not admitted.
- `A1092`: Step B7's lazy Thunk conversion, forced only where Lean forces it
  (dbgTrace order on stderr): a `Deep` variant's `Boxed<UBox>` impl at its
  inner type too.
- `A1093`: Free state and reader monads in one program (CSLib E01's shape):
  `UBox` reaches `FreeM`'s type only through an arrow's domain, so a read of
  the print-rebuildable static `counter._closed_0` rebuilds rather than
  clones ...
- `A1095`: Site rule (f): join point variants where both arms pass the list
  unchanged, one passes `[]`, the parameter refined by a later match: no
  coercion at an unread binder. -/

namespace A1085

@[noinline] def mkQ : (c d : Bool) → if c then List (if d then Nat else String) else Nat
  | true, true => ([1, 2] : List Nat) | true, false => (["a"] : List String) | false, _ => (5 : Nat)
@[noinline] def getG7 {A : Type} (c d : Bool) (x : if c then List (if d then A else String) else Nat) : Option A :=
  match c, x with
  | true, xs => (match d, xs.head? with | true, some a => some a | _, _ => none)
  | false, _ => none
def caseMain (a : List String) : IO Unit := do
  let c := a.length < 100
  for d in [a.isEmpty, !a.isEmpty] do
    let r := match d, getG7 (A := Nat) c d (mkQ c d) with
      | true, some n => toString (n + 2)
      | _, _ => "none"
    IO.println r
end A1085

namespace A1086

inductive Ty where
  | nat | str
  | arrow : Ty → Ty → Ty
@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat | .str => String
  | .arrow a b => a.denote → b.denote
def Any := (t : Ty) × t.denote
@[noinline] def mkAny (n : Nat) : Any :=
  match n % 3 with
  | 0 => ⟨.nat, n⟩
  | 1 => ⟨.arrow .nat .str, fun x => String.join (List.replicate x (toString n))⟩
  | _ => ⟨.arrow .str .nat, fun s => s.length + n⟩
@[noinline] def useAny (a : Any) : String :=
  match a with
  | ⟨.arrow .nat .str, f⟩ => (f : Nat → String) 3
  | ⟨.arrow .str .nat, f⟩ => toString ((f : String → Nat) "hello")
  | ⟨.nat, v⟩ => toString (v : Nat)
  | ⟨.str, v⟩ => (v : String)
  | ⟨.arrow _ _, _⟩ => "<fn>"
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  for i in List.range (n + 3) do IO.println (useAny (mkAny i))
end A1086

namespace A1087

structure Op where
  b : Bool
  f : if b then (Nat → Nat) else (String → String → String)

@[noinline] def mkOp (n : Nat) : Op := if n % 2 = 0 then ⟨true, (· + n)⟩ else ⟨false, fun a b => a ++ toString n ++ b⟩
@[noinline] def apOp (o : Op) (n : Nat) : String := match o with
  | ⟨true, f⟩ => let g : Nat → Nat := f; toString (g n)
  | ⟨false, f⟩ => let g : String → String → String := f; g "<" (toString n)

@[noinline] def mapOp (o : Op) : Op := match o with
  | ⟨true, f⟩ => let g : Nat → Nat := f; ⟨true, fun x => g (g x)⟩
  | ⟨false, f⟩ => let g : String → String → String := f; ⟨false, fun a b => g b a⟩

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ops := (List.range (n + 2)).map mkOp
  IO.println (ops.map (apOp · n))
  IO.println ((ops.map mapOp).map (apOp · n))
  IO.println (((ops.map mapOp).map mapOp).map (apOp · 1))
end A1087

namespace A1088

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
  IO.println (runLog (runState (prog (fun (p : Nat × List Nat) => (p.1 + 1, p.1 :: p.2)) (fun p => toString p.2) n) (n, [])) [])
  IO.println (runLog (runState (getS (σ := Nat)) n) [])
  IO.println (runLog (runState (getS (σ := String)) "q") [])
end A1088

namespace A1089

structure Pkg where
  b : Bool
  v : if b then Nat else String
@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
@[noinline] def rd : Pkg → Nat
  | ⟨true, v⟩ => let w : Nat := v; w + 1
  | ⟨false, v⟩ => let s : String := v; s.length
@[noinline] def split2 (ps : List Pkg) : List Pkg × List Pkg :=
  ps.foldr (fun p (ns, ss) => if p.b then (p :: ns, ss) else (ns, p :: ss)) ([], [])
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let (ns, ss) := split2 ((List.range (n + 3)).map mk)
  IO.println s!"{ns.map rd} {ss.map rd}"
end A1089

namespace A1090

inductive Cell where
  | mk (d : Bool) (v : List (if d then Nat else String))
@[noinline] def mkN (n : Nat) : Cell := ⟨true, [n, n + 1]⟩
@[noinline] def mkS (s : String) : Cell := ⟨false, [s, s ++ s]⟩
def rd : Cell → Nat
  | ⟨true, x :: _⟩ => show Nat from x
  | _ => 0
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  IO.println s!"{rd (mkN n)} {rd (mkS (toString n))}"
end A1090

namespace A1091

inductive Cell where
  | mk (d : Bool) (v : List (if d then Nat else String))
@[noinline] def mkN (n : Nat) : Cell := ⟨true, [n, n + 1]⟩
@[noinline] def mkS (s : String) : Cell := ⟨false, [s, s ++ s]⟩
def rd : Cell → Nat
  | ⟨true, x :: _⟩ => show Nat from x
  | ⟨false, s :: _⟩ => (show String from s).length
  | _ => 0
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  IO.println s!"{rd (mkN n)} {rd (mkS (toString n))}"
end A1091

namespace A1092

structure Pkg where
  b : Bool
  v : if b then Thunk (List Nat) else Thunk (List String)
@[noinline] def mkT (n : Nat) : Thunk (List Nat) := Thunk.mk fun _ => dbgTrace s!"force N {n}" fun _ => List.range n
@[noinline] def mkTS (n : Nat) : Thunk (List String) := Thunk.mk fun _ => dbgTrace s!"force S {n}" fun _ => (List.range n).map toString
@[noinline] def mkN (n : Nat) : Pkg := ⟨true, mkT n⟩
@[noinline] def mkS (n : Nat) : Pkg := ⟨false, mkTS n⟩
@[noinline] def rd (force : Bool) : Pkg → String
  | ⟨true, v⟩ => let w : Thunk (List Nat) := v; if force then toString (w.get.foldl (· + ·) 0) else "lazyN"
  | ⟨false, v⟩ => let w : Thunk (List String) := v; if force then String.intercalate "," w.get else "lazyS"
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let ps := [mkN n, mkS n]
  IO.println s!"{ps.map (rd false)}"
  IO.println s!"{ps.map (rd true)}"
  IO.println s!"{ps.map (rd true)}"
end A1092

namespace A1093

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
    IO.println s!"n={n}: state {a} {s} reader {runR (readProg n) 7}"
end A1093


namespace A1095

@[noinline] def mkQ : (c d : Bool) → if c then List (if d then Nat else String) else Nat
  | true, true => ([4, 5] : List Nat) | true, false => (["xy"] : List String) | false, _ => (5 : Nat)
@[noinline] def getJ2 : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, d, xs =>
    let xs0 : List (if d then Nat else String) := xs
    let ys : List (if d then Nat else String) := if xs0.length > 1 then xs0 else []
    match d, ys with
    | true, (h :: _) => ys.length + (show Nat from h)
    | _, _ => ys.length * 100
  | false, _, n => n
def caseMain (a : List String) : IO Unit := do
  let c := a.length < 100
  for d in [a.isEmpty, !a.isEmpty] do
    IO.println s!"{getJ2 c d (mkQ c d)}"
end A1095

def main : IO Unit := do
  IO.println "-- A1085"
  A1085.caseMain ["x"]
  IO.println "-- A1086"
  A1086.caseMain ["3"]
  IO.println "-- A1087"
  A1087.caseMain ["3"]
  IO.println "-- A1088"
  A1088.caseMain ["3"]
  IO.println "-- A1089"
  A1089.caseMain ["4"]
  IO.println "-- A1090"
  A1090.caseMain ["9"]
  IO.println "-- A1091"
  A1091.caseMain ["9"]
  IO.println "-- A1092"
  A1092.caseMain ["3"]
  IO.println "-- A1093"
  A1093.caseMain ["10"]
  IO.println "-- A1095"
  A1095.caseMain ["x"]
