/-! Runtime test: the probes of a second review of lean2rr's handling of
unknown types (review of the dependent-type design, probes c123, c4 and
c4b; one namespace each, run in that order):
- c123: a polymorphic `pick`; a structure with a proof field; a generic
  structure read at `Nat` and `String`; a dependent pair whose second
  component's type is computed from its first (`Σ b, T b`);
- c4: polymorphic recursion at a growing type (`List α`, from a run-time
  count); a field whose type is a type-former parameter applied to `Nat`
  (`f Nat`); scalar lambdas through `List.map`; `Float` and a `UInt64`
  above 2^63 in a generic structure;
- c4b: a higher-order generic function applied to closures over `UInt64`,
  `Float` and `String`. -/

namespace c123
-- C1 / C2 / C3 probe
structure Pos where
  n : Nat
  h : n > 0

def pick (α : Type) (b : Bool) (x y : α) : α := if b then x else y

def withProof (p : Pos) : Nat := p.n - 1

structure Box (α : Type) where
  val : α

def getVal (α : Type) (b : Box α) : α := b.val

-- a field whose type is computed from a value (not a type parameter)
def T : Bool → Type
  | true => Nat
  | false => String

def ex (b : Bool) : Σ b' : Bool, T b' :=
  if b then ⟨true, ((41 : Nat) + 1 : T true)⟩ else ⟨false, ("hello" : T false)⟩

def showT : (b : Bool) → T b → String
  | true, n => Nat.repr n
  | false, s => s

def showEx (b : Bool) : String :=
  let ⟨b', v⟩ := ex b
  showT b' v

def run : IO Unit := do
  IO.println (pick Nat true 1 2)
  IO.println (pick Nat false 1 2)
  IO.println (pick String false "a" "b")
  IO.println (withProof ⟨5, by decide⟩)
  IO.println (getVal Nat ⟨7⟩)
  IO.println (getVal String ⟨"seven"⟩)
  IO.println (showEx true)
  IO.println (showEx false)
end c123

namespace c4
-- C4 probe: polymorphic recursion, scalar lambdas through List.map, Float in polymorphic fields
structure Box (α : Type) where
  val : α

-- polymorphic recursion: the element type changes with the run-time n
def nest : (n : Nat) → {α : Type} → [ToString α] → α → String
  | 0, _, _, x => toString x
  | n+1, _, _, x => nest n [x, x]

-- a function whose type parameter is applied: field type `f Nat` is not a type parameter itself
structure App (f : Type → Type) where
  payload : f Nat

def getApp (f : Type → Type) (a : App f) : f Nat := a.payload

@[noinline] def mapU64 (xs : List UInt64) : List UInt64 := xs.map (fun x => x + 1)
@[noinline] def mapF (xs : List Float) : List Float := xs.map (fun x => x * 2.0)

def run : IO Unit := do
  IO.println (nest 2 (7 : Nat))
  IO.println (nest 1 (1.5 : Float))
  IO.println (getApp List ⟨[1,2,3]⟩)
  IO.println (getApp Option ⟨some 4⟩)
  IO.println (mapU64 [1, 2, 3])
  IO.println (mapF [1.0, 2.5])
  let b : Box Float := ⟨3.25⟩
  let b2 : Box UInt64 := ⟨0xFFFFFFFFFFFFFFFF⟩
  IO.println (b.val + 1.0)
  IO.println (b2.val)
end c4

namespace c4b
-- non-specialized higher-order call: closure over scalar type crosses a lcAny boundary
@[noinline] def applyTwice {α : Type} (f : α → α) (x : α) : α := f (f x)
@[noinline] def inc64 (x : UInt64) : UInt64 := x + 1
@[noinline] def dbl (x : Float) : Float := x * 2.0
def run : IO Unit := do
  IO.println (applyTwice inc64 5)
  IO.println (applyTwice dbl 1.25)
  IO.println (applyTwice (fun (s : String) => s ++ "!") "hi")
end c4b

def main : IO Unit := do
  IO.println "-- c123"; c123.run
  IO.println "-- c4"; c4.run
  IO.println "-- c4b"; c4b.run
