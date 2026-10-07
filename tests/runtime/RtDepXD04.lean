/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `D71Breaker3R13`: Statics holding closures, nested statics, and statics
  consumed owned twice and in place, in a Box-mode program.
- `D71BreakerP01`: Dependent record nested in containers, one reader
  matching both arms, built in loops.
- `D71BreakerP02`: Value-indexed vectors (GADT-style) at two element types,
  with existential Σ n, Vec.
- `D71BreakerP03`: A type universe with denote, Σ-typed values, pairs
  (nested dependent payloads), eval and show.
- `D71BreakerP04`: A typed expression GADT with eval : Expr t → t.denote,
  if/pairs/fst/snd/let via closures.
- `D71BreakerP05`: Free monad with a state functor at several state types,
  shared closed programs, combinators.
- `D71BreakerP06`: Closed terms shared between instantiations: [], none,
  some [], #[], ([], []), id, const thunks.
- `D71BreakerP07`: Polymorphic recursion at the function level: growing
  pairs, lists of pairs, with functions, strings, options.
- `D71BreakerP08`: Type-class dictionaries carrying dependent data: Type
  members, packed instances, Σ lists.
- `D71BreakerP08B`: Lean values of a D71 role repro
- `D71BreakerP08C`: Type-class dictionaries carrying dependent data: Type
  members, packed instances, Σ lists. -/

namespace D71Breaker3R13
/- R13: statics holding closures, nested statics, and statics consumed owned twice and in place, in a Box-mode program. -/
structure Pkg where
  b : Bool
  v : if b then Nat else String
@[noinline] def rd : Pkg → Nat
  | ⟨true, v⟩ => let w : Nat := v; w + 1
  | ⟨false, v⟩ => let s : String := v; s.length
@[noinline] def swap : Pkg → Pkg
  | ⟨true, v⟩ => let w : Nat := v; ⟨false, toString w⟩
  | ⟨false, v⟩ => let s : String := v; ⟨true, s.length⟩
def kList : List Pkg := [⟨true, (5 : Nat)⟩, ⟨false, "xyz"⟩, ⟨true, (7 : Nat)⟩]
def kFns : List (Pkg → Nat) := [rd, rd ∘ swap, fun p => rd (swap (swap p)) * 2]
def kPair : List Pkg × List (Pkg → Nat) := (kList, kFns)
def kNest : List (List Pkg × Nat) := [(kList, 1), ([], 2), (kList.map swap, 3)]
@[noinline] def consume (xs : List Pkg) : List Pkg := xs.reverse.map swap        -- takes ownership, rebuilds
@[noinline] def inPlace (xs : List Pkg) (n : Nat) : List Pkg := match n with
  | 0 => xs
  | k + 1 => inPlace (xs.map swap) k
@[noinline] def applyAll (fs : List (Pkg → Nat)) (ps : List Pkg) : List Nat := fs.foldl (fun acc f => acc ++ ps.map f) []
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{(consume kList).map rd} {(consume kList).map rd} {(inPlace kList n).map rd} {kList.map rd}"
  IO.println s!"{applyAll kFns kList} {applyAll kPair.2 kPair.1} {applyAll kFns (inPlace kPair.1 (n + 1))}"
  IO.println s!"{kNest.map (fun (ps, k) => (ps.map rd, k))} {(kNest.map (fun (ps, k) => (inPlace ps k).map rd))} {kNest.length}"
  let mut acc := kList
  for _ in List.range n do acc := consume acc ++ kList
  IO.println s!"{acc.length} {acc.map rd |>.foldl (· + ·) 0} {kList.map rd}"
end D71Breaker3R13

namespace D71BreakerP01
/- P01: dependent record nested in containers, one reader matching both arms, built in loops. -/
structure Pkg where
  b : Bool
  v : if b then Nat else String

@[noinline] def mk (n : Nat) : Pkg := if n % 3 = 0 then ⟨true, n * 2⟩ else ⟨false, s!"s{n}"⟩

@[noinline] def showP : Pkg → String
  | ⟨true, v⟩ => let w : Nat := v; s!"N{w}"
  | ⟨false, v⟩ => let s : String := v; s!"S{s}"

@[noinline] def total : List Pkg → Nat
  | [] => 0
  | ⟨true, v⟩ :: r => let w : Nat := v; w + total r
  | ⟨false, v⟩ :: r => let s : String := v; s.length + total r

@[noinline] def firstStr : Array Pkg → Option String
  | a => a.foldl (fun acc p => match acc, p with
      | some s, _ => some s
      | none, ⟨false, v⟩ => let s : String := v; some s
      | none, ⟨true, _⟩ => none) none

@[noinline] def swap (p : Pkg) : Pkg := match p with
  | ⟨true, v⟩ => let w : Nat := v; ⟨false, toString w⟩
  | ⟨false, v⟩ => let s : String := v; ⟨true, s.length⟩

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 5
  let ps := (List.range n).map mk
  let arr := ps.toArray
  IO.println (ps.map showP)
  IO.println (total ps)
  IO.println (firstStr arr)
  IO.println (firstStr (arr.map swap))
  IO.println ((ps.map swap).map showP)
  let o : Option Pkg := ps.head?
  match o with
  | some p => IO.println (showP (swap (swap p)))
  | none => IO.println "none"
  let pairs : List (Pkg × Pkg) := ps.zip (ps.map swap)
  IO.println (pairs.map (fun (a, b) => showP a ++ "/" ++ showP b))
end D71BreakerP01

namespace D71BreakerP02
/- P02: value-indexed vectors (GADT-style) at two element types, with existential Σ n, Vec. -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

@[noinline] def Vec.toList : Vec α n → List α
  | .nil => []
  | .cons a v => a :: v.toList

@[noinline] def Vec.head : Vec α (n + 1) → α
  | .cons a _ => a

@[noinline] def Vec.zipWith (f : α → β → γ) : Vec α n → Vec β n → Vec γ n
  | .nil, .nil => .nil
  | .cons a v, .cons b w => .cons (f a b) (v.zipWith f w)

@[noinline] def Vec.map (f : α → β) : Vec α n → Vec β n
  | .nil => .nil
  | .cons a v => .cons (f a) (v.map f)

def SomeVec (α : Type) := (n : Nat) × Vec α n

@[noinline] def fromList : List α → SomeVec α
  | [] => ⟨0, .nil⟩
  | a :: r => let ⟨n, v⟩ := fromList r; ⟨n + 1, .cons a v⟩

@[noinline] def descr : SomeVec Nat → String
  | ⟨0, _⟩ => "empty"
  | ⟨n + 1, v⟩ => s!"len {n+1} head {v.head}"

@[noinline] def descrS : SomeVec String → String
  | ⟨0, _⟩ => "empty"
  | ⟨n + 1, v⟩ => s!"len {n+1} head {v.head}"

structure Mixed where
  b : Bool
  sv : SomeVec (if b then Nat else String)

@[noinline] def mkMixed (n : Nat) : Mixed :=
  if n % 2 = 0 then ⟨true, fromList (List.range n)⟩ else ⟨false, fromList ((List.range n).map toString)⟩

@[noinline] def descrM : Mixed → String
  | ⟨true, sv⟩ => let s : SomeVec Nat := sv; descr s
  | ⟨false, sv⟩ => let s : SomeVec String := sv; descrS s

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let ⟨k, v⟩ := fromList (List.range n)
  let ⟨_, w⟩ := fromList ((List.range n).map (fun i => s!"<{i}>"))
  IO.println s!"{k} {v.toList} {w.toList}"
  match k, v with
  | 0, _ => IO.println "zero"
  | _ + 1, v => IO.println s!"{v.head} {(v.map (· * 10)).toList}"
  -- zipWith across types requires equal n; both built from range n so same n via cast of the index
  let z := (fromList (List.range n)).2.toList.zip ((fromList ((List.range n).map toString)).2.toList)
  IO.println z
  IO.println (descrM (mkMixed n))
  IO.println (descrM (mkMixed (n + 1)))
  IO.println ((List.range (n+2)).map (fun i => descrM (mkMixed i)))
end D71BreakerP02

namespace D71BreakerP03
/- P03: a type universe with denote, Σ-typed values, pairs (nested dependent payloads), eval and show. -/
inductive Ty where
  | nat | str | bool
  | pair : Ty → Ty → Ty
  | list : Ty → Ty
  deriving Repr

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String
  | .bool => Bool
  | .pair a b => a.denote × b.denote
  | .list a => List a.denote

def Val := (t : Ty) × t.denote

@[noinline] def Ty.show : (t : Ty) → t.denote → String
  | .nat, n => toString n
  | .str, s => s!"\"{s}\""
  | .bool, b => toString b
  | .pair a b, (x, y) => s!"({a.show x}, {b.show y})"
  | .list a, xs => "[" ++ ", ".intercalate (xs.map a.show) ++ "]"

@[noinline] def Ty.default : (t : Ty) → t.denote
  | .nat => 0
  | .str => ""
  | .bool => false
  | .pair a b => (a.default, b.default)
  | .list _ => []

@[noinline] def Ty.gen : (t : Ty) → Nat → t.denote
  | .nat, n => n * 3
  | .str, n => s!"g{n}"
  | .bool, n => n % 2 = 0
  | .pair a b, n => (a.gen n, b.gen (n + 1))
  | .list a, n => (List.range (n % 4)).map a.gen

@[noinline] def Ty.size : (t : Ty) → t.denote → Nat
  | .nat, n => n
  | .str, s => s.length
  | .bool, b => if b then 1 else 0
  | .pair a b, (x, y) => a.size x + b.size y
  | .list a, xs => xs.foldl (fun acc x => acc + a.size x) 0

@[noinline] def mkVal (n : Nat) : Val :=
  let t : Ty := match n % 5 with
    | 0 => .nat | 1 => .str | 2 => .pair .nat .str | 3 => .list (.pair .bool .nat) | _ => .list (.list .str)
  ⟨t, t.gen n⟩

@[noinline] def showVal (v : Val) : String := v.1.show v.2
@[noinline] def sizeVal (v : Val) : Nat := v.1.size v.2

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 6
  let vs := (List.range n).map mkVal
  for v in vs do IO.println s!"{repr v.1} = {showVal v} size {sizeVal v}"
  IO.println (vs.foldl (fun a v => a + sizeVal v) 0)
  let d : Val := ⟨.pair (.list .nat) .str, Ty.default _⟩
  IO.println (showVal d)
  let p : Val := ⟨.pair .nat .str, (n, toString n)⟩
  IO.println (showVal p)
  match p with
  | ⟨.pair .nat .str, (a, b)⟩ => IO.println s!"{a + 1} {b ++ "!"}"
  | _ => IO.println "other"
end D71BreakerP03

namespace D71BreakerP04
/- P04: a typed expression GADT with eval : Expr t → t.denote, if/pairs/fst/snd/let via closures. -/
inductive Ty where | nat | bool | str | pair : Ty → Ty → Ty

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat | .bool => Bool | .str => String | .pair a b => a.denote × b.denote

inductive Expr : Ty → Type where
  | lit : Nat → Expr .nat
  | slit : String → Expr .str
  | add : Expr .nat → Expr .nat → Expr .nat
  | eq : Expr .nat → Expr .nat → Expr .bool
  | ite : Expr .bool → Expr t → Expr t → Expr t
  | mk : Expr a → Expr b → Expr (.pair a b)
  | fst : Expr (.pair a b) → Expr a
  | snd : Expr (.pair a b) → Expr b
  | len : Expr .str → Expr .nat
  | app : Expr .str → Expr .str → Expr .str
  | showN : Expr .nat → Expr .str

@[noinline] def Expr.eval : Expr t → t.denote
  | .lit n => n
  | .slit s => s
  | .add a b => a.eval + b.eval
  | .eq a b => a.eval == b.eval
  | .ite c a b => if c.eval then a.eval else b.eval
  | .mk a b => (a.eval, b.eval)
  | .fst p => p.eval.1
  | .snd p => p.eval.2
  | .len s => s.eval.length
  | .app a b => a.eval ++ b.eval
  | .showN n => toString n.eval

@[noinline] def Expr.size : Expr t → Nat
  | .lit _ | .slit _ => 1
  | .add a b | .eq a b | .app a b => 1 + a.size + b.size
  | .ite c a b => 1 + c.size + a.size + b.size
  | .mk a b => 1 + a.size + b.size
  | .fst p | .snd p => 1 + p.size
  | .len s | .showN s => 1 + s.size

@[noinline] def build (n : Nat) : Expr (.pair .nat .str) :=
  match n with
  | 0 => .mk (.lit 1) (.slit "a")
  | k + 1 =>
    let e := build k
    .mk (.ite (.eq (.fst e) (.lit (k + 1))) (.lit 0) (.add (.fst e) (.lit k)))
        (.app (.snd e) (.showN (.len (.snd e))))

@[noinline] def Ty.show : (t : Ty) → t.denote → String
  | .nat, n => toString n | .bool, b => toString b | .str, s => s
  | .pair a b, (x, y) => s!"<{a.show x}|{b.show y}>"

def AnyExpr := (t : Ty) × Expr t

@[noinline] def anyOf (n : Nat) : AnyExpr :=
  match n % 4 with
  | 0 => ⟨.nat, .add (.lit n) (.lit 1)⟩
  | 1 => ⟨.bool, .eq (.lit n) (.lit 5)⟩
  | 2 => ⟨.str, .showN (.lit n)⟩
  | _ => ⟨.pair .nat .str, build (n % 3)⟩

@[noinline] def runAny (e : AnyExpr) : String := e.1.show e.2.eval ++ s!" #{e.2.size}"

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let e := build n
  IO.println s!"{e.eval.1} {e.eval.2} {e.size}"
  IO.println (Ty.show _ e.eval)
  for i in List.range (n + 4) do IO.println (runAny (anyOf i))
end D71BreakerP04

namespace D71BreakerP05
/- P05: free monad with a state functor at several state types, shared closed programs, combinators. -/
inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | put : σ → StateF σ Unit

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α

@[noinline] def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, k => k a
  | .liftBind op c, k => .liftBind op (fun i => (c i).bind k)

instance : Monad (FreeM F) where
  pure := .pure
  bind := FreeM.bind

def getL {σ : Type} : FreeM (StateF σ) σ := .liftBind .get .pure
def putL {σ : Type} (s : σ) : FreeM (StateF σ) Unit := .liftBind (.put s) .pure
def modifyL {σ : Type} (f : σ → σ) : FreeM (StateF σ) Unit := do let s ← getL; putL (f s)

@[noinline] def run {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind .get k, s => run (k s) s
  | .liftBind (.put s') k, _ => run (k ()) s'

@[noinline] def steps {σ : Type} : Nat → FreeM (StateF σ) (List σ)
  | 0 => pure []
  | n + 1 => do let s ← getL; let r ← steps n; pure (s :: r)

def progN (n : Nat) : FreeM (StateF Nat) Nat := do
  for _ in List.range n do modifyL (· + 2)
  let s ← getL
  putL (s * 10)
  getL

def progS (n : Nat) : FreeM (StateF String) Nat := do
  for i in List.range n do modifyL (· ++ toString i)
  let s ← getL
  putL (s ++ "!")
  pure s.length

def progP (n : Nat) : FreeM (StateF (Nat × String)) String := do
  for i in List.range n do modifyL (fun (a, b) => (a + i, b ++ "x"))
  let (a, b) ← getL
  putL (a * 2, b)
  pure s!"{a}{b}"

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println (run (progN n) n)
  IO.println (run (progS n) "s")
  IO.println (run (progP n) (n, "p"))
  IO.println (run (steps (σ := Nat) n) n)
  IO.println (run (steps (σ := String) n) "q")
  IO.println (run (getL (σ := Nat)) n)
  IO.println (run (getL (σ := String)) (toString n))
  IO.println (run (modifyL (σ := Nat) (· + 1)) n)
  IO.println (run (modifyL (σ := String) (· ++ "z")) (toString n))
end D71BreakerP05

namespace D71BreakerP06
/- P06: closed terms shared between instantiations: [], none, some [], #[], ([], []), id, const thunks. -/
@[noinline] def lenO : Option (List α) → Nat
  | none => 0
  | some xs => xs.length

@[noinline] def ap (f : α → β) (x : α) : β := f x
@[noinline] def twice (f : α → α) (x : α) : α := f (f x)

@[noinline] def pushAll (a : Array α) (xs : List α) : Array α := xs.foldl (·.push ·) a

@[noinline] def both (p : List α × List β) (x : α) (y : β) : List α × List β := (x :: p.1, y :: p.2)

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let s := toString n
  -- none / some [] shared
  IO.println s!"{lenO (none : Option (List Nat))} {lenO (none : Option (List String))}"
  IO.println s!"{lenO (some ([] : List Nat))} {lenO (some ([] : List String))}"
  let on : Option (List Nat) := if n > 100 then some [n] else some []
  let os : Option (List String) := if n > 100 then some [s] else some []
  IO.println s!"{lenO on} {lenO os}"
  -- id / twice shared function values
  IO.println s!"{ap id n} {ap id s} {twice id n} {twice id s}"
  IO.println s!"{ap (fun x => x) n} {ap (fun x => x) s}"
  -- empty arrays
  IO.println s!"{pushAll #[] (List.range n)} {pushAll #[] ((List.range n).map toString)}"
  -- empty pair
  IO.println s!"{both ([], []) n s} {both ([], []) s n}"
  -- a closed cons shared via a generic wrapper
  let l1 : List (List Nat) := [[]]
  let l2 : List (List String) := [[]]
  IO.println s!"{(l1.map (· ++ [n]))} {(l2.map (· ++ [s]))}"
  -- List.length / head? shared as references
  IO.println s!"{ap List.length (List.range n)} {ap List.length [s, s]} {ap List.head? (List.range n)} {ap List.head? [s]}"
  IO.println s!"{ap List.reverse (List.range n)} {ap List.reverse [s, "b"]}"
end D71BreakerP06

namespace D71BreakerP07
/- P07: polymorphic recursion at the function level: growing pairs, lists of pairs, with functions, strings, options. -/
@[noinline] def grow (n : Nat) (x : α) (sh : α → String) : String :=
  match n with
  | 0 => sh x
  | n + 1 => grow n (x, x) (fun (a, b) => "[" ++ sh a ++ " " ++ sh b ++ "]")

@[noinline] def depth (n : Nat) (xs : List α) (sz : α → Nat) : Nat :=
  match n with
  | 0 => xs.foldl (fun a x => a + sz x) 0
  | n + 1 => depth n (xs.zip xs.reverse) (fun (a, b) => sz a + sz b)

@[noinline] def wrapOpt (n : Nat) (x : α) (sh : α → String) : String :=
  match n with
  | 0 => sh x
  | n + 1 => wrapOpt n (some x) (fun o => match o with | some v => "S" ++ sh v | none => "N")

@[noinline] def growList (n : Nat) (x : α) (count : α → Nat) : Nat :=
  match n with
  | 0 => count x
  | n + 1 => growList n [x, x] (fun l => l.foldl (fun a y => a + count y) 0)

@[noinline] def growIO (n : Nat) (x : α) (sh : α → String) : IO Unit :=
  match n with
  | 0 => IO.println (sh x)
  | n + 1 => do IO.println s!"level {n}"; growIO n (x, n) (fun (a, k) => sh a ++ s!"@{k}")

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println (grow n n toString)
  IO.println (grow (n % 2) "s" id)
  IO.println (depth n (List.range n) id)
  IO.println (depth (n % 3) ["ab", toString n] String.length)
  IO.println (wrapOpt n n toString)
  IO.println (wrapOpt (n + 1) (toString n) id)
  IO.println s!"{growList n n id} {growList (n % 4) "abc" String.length}"
  growIO (n % 3) n toString
  growIO (n % 2) "s" id
end D71BreakerP07

namespace D71BreakerP08
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
  | @AnyC.mk _ _ v => D71BreakerP08.summary v
@[noinline] def AnyC.first? : AnyC → Option String
  | @AnyC.mk c _ v => match (Container.toList v : List (Container.Elem c)) with
    | [] => none
    | e :: _ => some (Container.showE (c := c) e)

class Shape (α : Type) where
  name : α → String
  area : α → Nat
  scale : Nat → α → α

structure Circle where r : Nat
structure Rect where
  w : Nat
  h : Nat
instance : Shape Circle := ⟨fun _ => "circle", fun c => 3 * c.r * c.r, fun k c => ⟨c.r * k⟩⟩
instance : Shape Rect := ⟨fun _ => "rect", fun r => r.w * r.h, fun k r => ⟨r.w * k, r.h⟩⟩
instance [inst : Shape α] : Shape (List α) := ⟨fun xs => s!"list of {xs.length}", fun xs => xs.foldl (fun a x => a + inst.area x) 0, fun k xs => xs.map (inst.scale k)⟩

structure AnyShape where
  {α : Type}
  [inst : Shape α]
  val : α

@[noinline] def AnyShape.descr : AnyShape → String
  | @AnyShape.mk _ _ v => s!"{Shape.name v}:{Shape.area v}"
@[noinline] def AnyShape.scale (k : Nat) : AnyShape → AnyShape
  | @AnyShape.mk _ _ v => ⟨Shape.scale k v⟩

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let cs : List AnyC := [⟨List.range n⟩, ⟨s!"hello{n}"⟩, ⟨#[("a", n), ("b", 1)]⟩, ⟨("" : String)⟩]
  for c in cs do IO.println s!"{c.summary} {c.first?}"
  let shapes : List AnyShape := [⟨Circle.mk n⟩, ⟨Rect.mk n 2⟩, ⟨[Circle.mk 1, Circle.mk n]⟩, ⟨[[Rect.mk 1 1], [Rect.mk n n]]⟩]
  for s in shapes do IO.println (s.descr ++ " -> " ++ (s.scale 2).descr)
  IO.println ((shapes.map (AnyShape.scale n)).map AnyShape.descr)
end D71BreakerP08

namespace D71BreakerP08B
class Shape (α : Type) where
  name : α → String
  area : α → Nat
  scale : Nat → α → α

structure Circle where r : Nat
structure Rect where
  w : Nat
  h : Nat
instance : Shape Circle := ⟨fun _ => "circle", fun c => 3 * c.r * c.r, fun k c => ⟨c.r * k⟩⟩
instance : Shape Rect := ⟨fun _ => "rect", fun r => r.w * r.h, fun k r => ⟨r.w * k, r.h⟩⟩
instance [inst : Shape α] : Shape (List α) := ⟨fun xs => s!"list of {xs.length}", fun xs => xs.foldl (fun a x => a + inst.area x) 0, fun k xs => xs.map (inst.scale k)⟩

structure AnyShape where
  {α : Type}
  [inst : Shape α]
  val : α

@[noinline] def AnyShape.descr : AnyShape → String
  | @AnyShape.mk _ _ v => s!"{Shape.name v}:{Shape.area v}"
@[noinline] def AnyShape.scale (k : Nat) : AnyShape → AnyShape
  | @AnyShape.mk _ _ v => ⟨Shape.scale k v⟩

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let shapes : List AnyShape := [⟨Circle.mk n⟩, ⟨Rect.mk n 2⟩, ⟨[Circle.mk 1, Circle.mk n]⟩, ⟨[[Rect.mk 1 1], [Rect.mk n n]]⟩]
  for s in shapes do IO.println (s.descr ++ " -> " ++ (s.scale 2).descr)
  IO.println ((shapes.map (AnyShape.scale n)).map AnyShape.descr)
end D71BreakerP08B

namespace D71BreakerP08C
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

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println (summary (List.range n))
  IO.println (summary s!"hello{n}")
  IO.println (summary #[("a", n), ("b", 1)])
end D71BreakerP08C

def main : IO Unit := do
  IO.println "-- D71Breaker3R13"
  D71Breaker3R13.caseMain ["4"]
  IO.println "-- D71BreakerP01"
  D71BreakerP01.caseMain ["7"]
  IO.println "-- D71BreakerP02"
  D71BreakerP02.caseMain ["5"]
  IO.println "-- D71BreakerP03"
  D71BreakerP03.caseMain ["11"]
  IO.println "-- D71BreakerP04"
  D71BreakerP04.caseMain ["6"]
  IO.println "-- D71BreakerP05"
  D71BreakerP05.caseMain ["4"]
  IO.println "-- D71BreakerP06"
  D71BreakerP06.caseMain ["3"]
  IO.println "-- D71BreakerP07"
  D71BreakerP07.caseMain ["4"]
  IO.println "-- D71BreakerP08"
  D71BreakerP08.caseMain ["5"]
  IO.println "-- D71BreakerP08B"
  D71BreakerP08B.caseMain ["3"]
  IO.println "-- D71BreakerP08C"
  D71BreakerP08C.caseMain ["3"]
