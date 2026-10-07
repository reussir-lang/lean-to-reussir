/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `A896`: A structure field `shw : Option (α → String)` that is `none` at
  one construction is bound at its type in the rebuild and rebuilt with its
  own wrappers.
- `A897`: A map into `List (Ty b)`, pure and through `mapM` in `IO`, refused
  as `nested-coercion` (tracked).
- `A910`: Lean's compiler shares the closed term `List.length` between `List
  String` and `List Nat` (an erased type argument), which no dependent
  position types
- `A911`: Steps 1 and 10, support-status NS19: a closed term `List.length`
  shared between `List String → Nat` and `List Nat → Nat` beside a dynamic
  key, seen only in the rewritten program's T13 run, refused ...
- `A912`: Dependent function values in a `List`, an `Array`, an `Option` and
  a pair: an `lcAny` slot whose class holds `Dyn` below its top is keyed at
  the ...
- `A913`: A structure's slot parameter held by a field under a container of
  arrows (`fs : List (α → String)`) at Nat and String in one array: refused
  as nested-coercion naming the field (tracked).
- `A914`: Steps 3 and 4: a key collapsed to one variant keeping a head over
  unions (`Ty b × Ty b`, `Option (Option (Ty b))`, `Option (Ty b × Ty b)`,
  `Option (Ty b) × Except String (Option (Ty b))`, three-deep ...
- `A917`: (iv), support-status NS20: a witness-less `none` beside a keyed
  pair under a by-value constructor, read at `(Nat × Nat) × Option Nat`,
  refused as witness-less-nested (tracked).
- `A918`: (iv), support-status NS20: `some (.ok (.inr n))` at `Option
  (Except String (Sum (Ty b) Nat))` holds nothing on the Sum's left, a
  witness-less path below several by-value constructors: refused as ...
- `A919`: Support-status NS21: a structure keyed over its own type parameter
  whose arrow field and value field share one slot (`Box α b`, `f : T2 α b →
  Nat`, `v : T2 α b`) fails T13 on the rewritten program
- `A924`: Libm rows whose result IEEE 754 does not fix exactly are computed
  at run time. -/

namespace A896

structure Pkg where
  α : Type
  val : α
  shw : Option (α → String)
@[noinline] def pkgN (n : Nat) : Pkg := Pkg.mk Nat n (some (fun (k : Nat) => toString k))
@[noinline] def pkgS (s : String) : Pkg := Pkg.mk String s none
@[noinline] def useP (p : Pkg) : Nat := ((p.shw.map (· p.val)).getD "-").length
@[noinline] def mkShow (p : Pkg) : Unit → String := fun _ => (p.shw.map (· p.val)).getD "?"
@[noinline] def applyShw (p : Pkg) : Option (Unit → String) := p.shw.map fun f _ => f p.val
def caseMain (args : List String) : IO Unit := do
  let n := args.length
  let ps : Array Pkg := #[pkgN (5 + n), pkgS "hi", pkgN 123]
  IO.println s!"{ps.foldl (fun a p => a + useP p) 0} {(ps.map fun p => (mkShow p ()).length).foldl (· + ·) 0} {(ps.map fun p => ((applyShw p).map (· ())).getD "none" |>.length).foldl (· + ·) 0}"
end A896

namespace A897

def Ty : Bool → Type | true => Nat | false => String
def pick : (b : Bool) → Nat → Ty b | true, n => n * 2 | false, n => toString n
@[noinline] def sumDep (b : Bool) (xs : List (Ty b)) : Nat := match b with | true => (xs : List Nat).foldl (· + ·) 0 | false => (xs : List String).foldl (fun a s => a + s.length) 0
-- a map into List (Ty b), pure and in IO
@[noinline] def mapPure (b : Bool) (n : Nat) : List (Ty b) := (List.range n).map fun i => pick b i
@[noinline] def mapDep (b : Bool) (n : Nat) : IO (List (Ty b)) := (List.range n).mapM fun i => (pure (pick b i) : IO (Ty b))
def caseMain (args : List String) : IO Unit := do
  let c ← mapDep true (4 + args.length)
  let d ← mapDep false 12
  IO.println s!"{sumDep true (mapPure true (3 + args.length))} {sumDep false (mapPure false 11)} {sumDep true c} {sumDep false d}"
end A897

namespace A910

@[noinline] def ap {β : Type} (g : β → Nat) (x : β) : Nat := g x
def caseMain (args : List String) : IO Unit := do
  let k := args.length
  IO.println s!"{ap List.length ["a", "b"] + ap List.length [k]}"
end A910

namespace A911

def K (α β : Type) : Bool → Type
  | true => α
  | false => β
def KS (γ : Type) (b : Bool) : Type := K γ γ b
def KL (γ : Type) (b : Bool) : Type := K γ (List γ) b
def mkS {γ : Type} (b : Bool) (x : γ) : KS γ b := match b with
  | true => x
  | false => x
def mkL {γ : Type} (b : Bool) (x : γ) : KL γ b := match b with
  | true => x
  | false => [x, x, x]
def readK {α β : Type} (b : Bool) (v : K α β b) (f : α → Nat) (g : β → Nat) : Nat := match b, v with
  | true, a => f (show α from a)
  | false, c => g (show β from c)
def caseMain (args : List String) : IO UInt32 := do
  let k := args.length
  let b := k % 2 == 0
  IO.println s!"{readK (α := Nat) (β := Nat) b (mkS b k) id (· + 100)} {readK (α := String) (β := List String) b (mkL b "x") String.length List.length}"
  IO.println s!"{readK (α := Nat) (β := List Nat) (!b) (mkL (!b) k) id List.length}"
  return 0
end A911

namespace A912

@[noinline] def pickL {α : Type} (b : Bool) (x : α) : if b then List α else List (List α) :=
  match b with | true => [x, x, x] | false => [[x], [x]]
@[noinline] def lenP {α : Type} (b : Bool) (v : if b then List α else List (List α)) : Nat :=
  match b, v with
  | true, xs => xs.length
  | false, xss => xss.length + 10
@[noinline] def mkF (k : Nat) : (b : Bool) → (if b then List Nat else List (List Nat)) → Nat :=
  fun c v => lenP c v + k
@[noinline] def run (fs : List ((b : Bool) → (if b then List Nat else List (List Nat)) → Nat)) (b : Bool) (n : Nat) : List Nat :=
  fs.map fun f => f b (pickL b n)
@[noinline] def runA (fs : Array ((b : Bool) → (if b then List Nat else List (List Nat)) → Nat)) (b : Bool) (n : Nat) : List Nat :=
  fs.toList.map fun f => f b (pickL b n)
@[noinline] def runO (f? : Option ((b : Bool) → (if b then List Nat else List (List Nat)) → Nat)) (b : Bool) (n : Nat) : Nat :=
  match f? with | some f => f b (pickL b n) | none => 0
@[noinline] def runP (fp : ((b : Bool) → (if b then List Nat else List (List Nat)) → Nat) × Nat) (b : Bool) (n : Nat) : Nat :=
  fp.1 b (pickL b n) + fp.2
def caseMain (args : List String) : IO Unit := do
  let n := args.length
  IO.println s!"{run [mkF 1, mkF 2, lenP] true n} {run [mkF 3] false n}"
  IO.println s!"{runA #[mkF 1, lenP, mkF n] true n} {runA #[mkF 3] false n} {runO (some (mkF 2)) false n} {runO none true n} {runP (mkF 5, 100) true n}"
end A912

namespace A913

structure Pkg where
  α : Type
  val : α
  fs : List (α → String)
@[noinline] def pkgN (n : Nat) : Pkg := Pkg.mk Nat n [fun (k : Nat) => toString k]
@[noinline] def pkgS (s : String) : Pkg := Pkg.mk String s [fun (t : String) => t]
@[noinline] def useP (p : Pkg) : Nat := (p.fs.map (· p.val)).foldl (fun a s => a + s.length) 0
def caseMain (args : List String) : IO Unit := IO.println s!"{#[pkgN (5 + args.length), pkgS "hello"].foldl (fun a p => a + useP p) 0}"
end A913

namespace A914

def Ty : Bool → Type | true => Nat | false => String
def pick : (b : Bool) → Nat → Ty b | true, n => n * 2 | false, n => toString n
@[noinline] def mkP (b : Bool) (n : Nat) : (b : Bool) × (Ty b × Ty b) := ⟨b, (pick b n, pick b (n + 3))⟩
@[noinline] def rdP (p : (b : Bool) × (Ty b × Ty b)) : Nat := match p with
  | ⟨true, q⟩ => let r : Nat × Nat := q; r.1 + r.2
  | ⟨false, q⟩ => let r : String × String := q; r.1.length + r.2.length
@[noinline] def mkOO (b : Bool) (n : Nat) : (b : Bool) × Option (Option (Ty b)) := ⟨b, some (some (pick b n))⟩
@[noinline] def rdOO (p : (b : Bool) × Option (Option (Ty b))) : Nat := match p with
  | ⟨true, o⟩ => let q : Option (Option Nat) := o; match q with | some (some k) => k | _ => 0
  | ⟨false, o⟩ => let q : Option (Option String) := o; match q with | some (some s) => s.length | _ => 0
@[noinline] def mkA (b : Bool) (n : Nat) : (b : Bool) × Option (Ty b × Ty b) := ⟨b, some (pick b n, pick b (n + 1))⟩
@[noinline] def rdA (p : (b : Bool) × Option (Ty b × Ty b)) : Nat := match p with
  | ⟨true, o⟩ => let q : Option (Nat × Nat) := o; match q with | some (x, y) => x + y | none => 0
  | ⟨false, o⟩ => let q : Option (String × String) := o; match q with | some (x, y) => x.length + y.length | none => 0
@[noinline] def mkB (b : Bool) (n : Nat) : (b : Bool) × (Option (Ty b) × Except String (Option (Ty b))) := ⟨b, (some (pick b n), .ok (some (pick b (n + 2))))⟩
@[noinline] def rdB (p : (b : Bool) × (Option (Ty b) × Except String (Option (Ty b)))) : Nat := match p with
  | ⟨true, q⟩ => let r : Option Nat × Except String (Option Nat) := q
    (r.1.getD 0) + (match r.2 with | .ok (some k) => k | _ => 0)
  | ⟨false, q⟩ => let r : Option String × Except String (Option String) := q
    (r.1.getD "").length + (match r.2 with | .ok (some s) => s.length | _ => 0)
@[noinline] def mkC (b : Bool) (n : Nat) : (b : Bool) × Option (Option (Option (Ty b))) := ⟨b, some (some (some (pick b n)))⟩
@[noinline] def rdC (p : (b : Bool) × Option (Option (Option (Ty b)))) : Nat := match p with
  | ⟨true, o⟩ => let q : Option (Option (Option Nat)) := o; match q with | some (some (some k)) => k | _ => 0
  | ⟨false, o⟩ => let q : Option (Option (Option String)) := o; match q with | some (some (some s)) => s.length | _ => 0
def caseMain (args : List String) : IO Unit := do
  let n := args.length
  IO.println s!"{rdP (mkP true (4 + n))} {rdP (mkP false 1234)} {rdOO (mkOO true (5 + n))} {rdOO (mkOO false 99)}"
  IO.println s!"{rdA (mkA true (3 + n))} {rdA (mkA false 456)} {rdB (mkB true (1 + n))} {rdB (mkB false 77)} {rdC (mkC true (2 + n))} {rdC (mkC false 12345)}"
end A914

namespace A917

def Ty : Bool → Type | true => Nat | false => String
def pick : (b : Bool) → Nat → Ty b | true, n => n * 2 | false, n => toString n
@[noinline] def mkD (b : Bool) (n : Nat) : (b : Bool) × ((Ty b × Nat) × Option (Ty b)) := ⟨b, ((pick b n, 7), none)⟩
@[noinline] def rdD (p : (b : Bool) × ((Ty b × Nat) × Option (Ty b))) : Nat := match p with
  | ⟨true, q⟩ => let r : (Nat × Nat) × Option Nat := q; r.1.1 + r.1.2 + r.2.getD 1
  | ⟨false, q⟩ => let r : (String × Nat) × Option String := q; r.1.1.length + r.1.2 + (r.2.getD "zz").length
def caseMain (args : List String) : IO Unit := do
  let n := args.length
  IO.println s!"{rdD (mkD true n)} {rdD (mkD false 9)}"
end A917

namespace A918

def Ty : Bool → Type | true => Nat | false => String
def pick : (b : Bool) → Nat → Ty b | true, n => n * 2 | false, n => toString n
@[noinline] def mkM (b : Bool) (n : Nat) (c : Bool) : (b : Bool) × Option (Except String (Sum (Ty b) Nat)) := ⟨b, if c then some (.ok (.inl (pick b n))) else some (.ok (.inr n))⟩
@[noinline] def rdM (p : (b : Bool) × Option (Except String (Sum (Ty b) Nat))) : Nat := match p with
  | ⟨true, o⟩ => let q : Option (Except String (Sum Nat Nat)) := o; match q with | some (.ok (.inl k)) => k | some (.ok (.inr k)) => k + 100 | _ => 0
  | ⟨false, o⟩ => let q : Option (Except String (Sum String Nat)) := o; match q with | some (.ok (.inl s)) => s.length | some (.ok (.inr k)) => k + 200 | _ => 0
def caseMain (args : List String) : IO Unit := IO.println s!"{rdM (mkM true (6 + args.length) true)} {rdM (mkM true 6 false)} {rdM (mkM false 12 true)} {rdM (mkM false 12 false)}"
end A918

namespace A919

def T2 (α : Type) : Bool → Type | true => List α | false => Option α
@[noinline] def lenT {α : Type} (b : Bool) (v : T2 α b) : Nat := match b with
  | true => let l : List α := v; l.length
  | false => let o : Option α := v; if o.isSome then 1 else 0
@[noinline] def mkT {α : Type} (b : Bool) (x : α) : T2 α b := match b with | true => [x, x] | false => some x
structure Box (α : Type) (b : Bool) where
  f : T2 α b → Nat
  v : T2 α b
@[noinline] def mkBox {α : Type} (b : Bool) (x : α) : Box α b := ⟨lenT b, mkT b x⟩
@[noinline] def runBox {α : Type} (bx : Box α b) : Nat := bx.f bx.v + bx.f bx.v
def caseMain (args : List String) : IO Unit := IO.println s!"{runBox (mkBox true (1 + args.length))} {runBox (mkBox false "s")}"
end A919

namespace A924

def e : Float := Float.exp 1.0
def c : Float := Float.cbrt 27.0
def k : Float := (1.5 : Float) * 2.0

def caseMain : IO Unit := do
  IO.println s!"e {e.toBits}"
  IO.println s!"c {c.toBits}"
  IO.println s!"k {k.toBits}"
  IO.println s!"exp {(Float.exp 1.0).toBits}"
  IO.println s!"cbrt {(Float.cbrt 27.0).toBits}"
end A924

def main : IO Unit := do
  IO.println "-- A896"
  A896.caseMain ["a"]
  IO.println "-- A897"
  A897.caseMain ["a"]
  IO.println "-- A910"
  A910.caseMain ["a"]
  IO.println "-- A911"
  let c ← A911.caseMain ["a"]
  IO.println s!"exit {c}"
  IO.println "-- A912"
  A912.caseMain ["a"]
  IO.println "-- A913"
  A913.caseMain ["a"]
  IO.println "-- A914"
  A914.caseMain ["a"]
  IO.println "-- A917"
  A917.caseMain ["a"]
  IO.println "-- A918"
  A918.caseMain ["a"]
  IO.println "-- A919"
  A919.caseMain ["a"]
  IO.println "-- A924"
  A924.caseMain
