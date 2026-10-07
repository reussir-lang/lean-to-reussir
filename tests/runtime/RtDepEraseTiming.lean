/-! Runtime test: where a function's body runs when some of its parameters
are types (or proofs), which carry no data. Native Lean runs a body when
its last parameter is applied, types included: a partial application that
leaves a type open does not run it, and each later application to that
type runs it again. Each body prints a trace (stderr), so the traces and
their counts show where bodies run; the results go to stdout. Cases:
- a function whose parameters are all types, used as a value and applied
  twice, in one function (Lean merges the two equal applications) and in
  two functions;
- `fx (x : Nat) (α : Type)`: `fx 3` bound as a partial application and
  applied later in two places, and `fx 4` never applied;
- types in the middle (`mid x α y f`) and at the end (`endT x α β`) of a
  parameter list: partial applications that stop before, between and
  after the type parameters, applied later, and never;
- a structure field `run : {α : Type} → List α → Nat` filled with a lambda
  that computes before its list parameter (Lean gives the lambda both
  parameters: the work runs at each application to a list) and with a
  partial application of a function whose last parameter is the list;
- a value of type `(α β : Type) → Nat` that completes after its first
  type (`mkW true`: its type `(α : Type) → T3 true` unfolds to the
  function type at the use site), applied to a second type in two places;
- a function value stored where its type is not known (an existential's
  field), applied there to a mix of types and values;
- local functions with a type parameter, called at two types in tail
  position (Lean makes them join points);
- functions whose only parameter is a type, with closed-term extraction
  off and with `@[never_extract]`, used twice. -/

-- all parameters are types
@[noinline] def allTy (_α _β : Type) : Nat := dbgTrace "allTy body" fun _ => 41

@[noinline] def useTwiceSame (f : (α β : Type) → Nat) : Nat := f Nat String + f Bool Nat
@[noinline] def useA (f : (α β : Type) → Nat) : Nat := f Nat String
@[noinline] def useB (f : (α β : Type) → Nat) : Nat := f Bool Nat + 1

-- a trailing type parameter
@[noinline] def fx (x : Nat) (_α : Type) : Nat := dbgTrace s!"fx {x}" fun _ => x + 1

@[noinline] def apA (g : (α : Type) → Nat) : Nat := g Nat
@[noinline] def apB (g : (α : Type) → Nat) : Nat := g String * 10
@[noinline] def ignore (_ : (α : Type) → Nat) : Nat := 0

-- types in the middle and at the end
@[noinline] def mid (x : Nat) (α : Type) (y : α) (f : α → Nat) : Nat :=
  dbgTrace s!"mid {x}" fun _ => x + f y

@[noinline] def endT (x : Nat) (_α : Type) (_β : Type) : Nat := dbgTrace s!"endT {x}" fun _ => x * 3

@[noinline] def apMid (m : (α : Type) → α → (α → Nat) → Nat) : Nat := m Nat 1 id + m String "ab" String.length
@[noinline] def apMid2 (m : Nat → (Nat → Nat) → Nat) : Nat := m 3 id
@[noinline] def apEnd (e : (α β : Type) → Nat) : Nat := e Nat Nat
@[noinline] def apEnd1 (e : (β : Type) → Nat) : Nat := e String
@[noinline] def ignoreEnd (_ : (β : Type) → Nat) : Nat := 0

-- a field over any element type
structure Op where
  run : {α : Type} → List α → Nat

@[noinline] def work (k : Nat) : Nat := dbgTrace s!"work {k}" fun _ => k * 2

@[noinline] def mkOp (k : Nat) : Op := ⟨fun {α} => let c := work k; fun (xs : List α) => xs.length + c⟩

@[noinline] def stage (k : Nat) (α : Type) (xs : List α) : Nat := dbgTrace s!"stage {k}" fun _ => xs.length + k

@[noinline] def mkOp2 (k : Nat) : Op := ⟨@stage k⟩

@[noinline] def twice (g : List Nat → Nat) : Nat := g [1, 2] + g [3]

-- a value that completes after its first type
def T3 : Bool → Type 1
  | true => (β : Type) → Nat
  | false => ULift.{1} Nat

@[noinline] def h3 (b : Bool) (_α : Type) : T3 b :=
  dbgTrace s!"outer {b}" fun _ => match b with
    | true => (fun β => dbgTrace "inner" fun _ => 5 : (β : Type) → Nat)
    | false => (⟨7⟩ : ULift.{1} Nat)

@[noinline] def mkW (b : Bool) : (α : Type) → T3 b := h3 b
@[noinline] def useG1 (g : (β : Type) → Nat) : Nat := g Nat
@[noinline] def useG2 (g : (β : Type) → Nat) : Nat := g Bool + 100
@[noinline] def chain (f : (α β : Type) → Nat) : Nat := let g := f Nat; useG1 g + useG2 g

-- a function value applied where its type is not known
@[noinline] def mixApp (b : Bool) (n : Nat) : Nat :=
  let p : (α : Type) × α × ((β : Type) → α → List β → Nat) :=
    if b then ⟨Nat, n, fun _ x l => dbgTrace "mix nat" fun _ => x + l.length⟩
    else ⟨String, toString n, fun _ s l => dbgTrace "mix str" fun _ => s.length + l.length⟩
  p.2.2 String p.2.1 ["a", "b"] + p.2.2 Nat p.2.1 [1]

-- local functions with a type parameter, in tail position
@[noinline] def jpL (b : Bool) (n : Nat) : String :=
  let k {α : Type} [ToString α] (x : α) : String := dbgTrace "k" fun _ => s!"<{x}>"
  if b then k n else k "s"

@[noinline] def jpL2 (b : Bool) (n : Nat) (xs : List Nat) : Nat :=
  let k {α : Type} (ys : List α) (m : Nat) : Nat := dbgTrace "k2" fun _ => ys.length + m
  match b with
  | true => k xs n
  | false => k [toString n] (n + 1)

-- only a type parameter, not extracted as a closed term
set_option compiler.extract_closed false in
@[noinline] def elT (α : Type) : List α := dbgTrace "elT" fun _ => []

@[never_extract, noinline] def elN (α : Type) : List α := dbgTrace "elN" fun _ => []

@[noinline] def lenT (n : Nat) : Nat := (elT Nat).length + (elT String).length + n
@[noinline] def lenN (n : Nat) : Nat := (elN Nat).length + (elN String).length + n

def main (args : List String) : IO Unit := do
  let b := args.length == 0
  let n := args.length + 3
  IO.println s!"allTy {useTwiceSame allTy} {useA allTy + useB allTy}"
  let p := fx 3
  let q := fx 4
  IO.println s!"fx {apA p + apB p} {ignore q}"
  let m := mid 5
  let m2 := mid 6 Nat
  IO.println s!"mid {apMid m} {apMid2 m2} {apMid2 (mid 7 Nat)}"
  let e1 := endT 1
  let e2 := endT 2 Nat
  let e3 := endT 3 Nat
  IO.println s!"endT {apEnd e1 + apEnd e1} {apEnd1 e2 + apEnd1 e2} {ignoreEnd e3} {endT 4 Nat Nat}"
  let o := mkOp 1
  let g := @o.run Nat
  IO.println s!"op {twice g} {o.run [1] + o.run ["a", "b"]}"
  let o2 := mkOp2 2
  IO.println s!"op2 {twice (@o2.run Nat)} {o2.run [true]}"
  let w : (α β : Type) → Nat := mkW true
  IO.println s!"chain {chain w} {chain (mkW true)}"
  IO.println s!"mix {mixApp b n} {mixApp (!b) n}"
  IO.println s!"jp {jpL b n} {jpL (!b) n} {jpL2 b n [1, 2]} {jpL2 (!b) n []}"
  IO.println s!"closed {lenT n} {lenT (n + 1)} {lenN n} {lenN (n + 1)}"
