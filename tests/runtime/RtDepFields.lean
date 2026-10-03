/-! Runtime test: projections out of values whose type depends on a value
or is an existential payload (round 7 RV7F-01). Mono types such a value
`lcAny` (`s.Data`, `V b`, `cast p.isPair p.val`), and `structProjCases`
types the projected field from the generic constructor, `lcAny` too. Stage 3
must leave those fields `lcAny`: the constructor's field types are known
only when the value's type is the constructor's inductive applied to its
parameters. Taking the parameters' types for the fields (`◾` for `Prod`'s
type parameters, `Nat` for `Tagged`'s value parameter `n`) gave the
functions below the result type `◾` or `Nat`, and the callers unboxed a
`Float`, a pair, a `String` or a `List` as unit or `Nat`: "INTERNAL PANIC:
unreachable code has been reached". -/

-- A family of record types indexed by a tag; every branch of the getter
-- returns the first component (Lean merges them into one projection).
inductive Shape where
  | circle | rect

def Shape.Dim : Shape → Type
  | .circle => Float
  | .rect => Float × Float

def Shape.Data : Shape → Type
  | .circle => Float × String
  | .rect => (Float × Float) × String

@[noinline] def Shape.mk : (s : Shape) → s.Data
  | .circle => (1.5, "c")
  | .rect => ((2.0, 3.0), "r")

@[noinline] def Shape.dim : (s : Shape) → s.Data → s.Dim
  | .circle, d => d.1
  | .rect, d => d.1

@[noinline] def Shape.label : (s : Shape) → s.Data → String
  | .circle, d => d.2
  | .rect, d => d.2

-- A structure with a value parameter before its type parameter, reached
-- through a type that depends on a value.
structure Tagged (n : Nat) (α : Type) where
  val : α
  tag : Nat

def V : Bool → Type
  | true => Tagged 3 String
  | false => Tagged 4 (List Nat)

def R : Bool → Type
  | true => String
  | false => List Nat

@[noinline] def mkV : (b : Bool) → V b
  | true => ⟨"tagged", 30⟩
  | false => ⟨[1, 2, 3], 40⟩

@[noinline] def val : (b : Bool) → V b → R b
  | true, x => (x : Tagged 3 String).val
  | false, x => (x : Tagged 4 (List Nat)).val

@[noinline] def tag : (b : Bool) → V b → Nat
  | true, x => (x : Tagged 3 String).tag
  | false, x => (x : Tagged 4 (List Nat)).tag

-- An existential package whose payload is a pair, pinned by an equation.
structure Pkg where
  A : Type
  B : Type
  val : A
  isPair : A = (B × String)

def mkPkg (n : Nat) : Pkg := ⟨Nat × String, Nat, (n, "s"), rfl⟩

def mkPkgStr (s : String) : Pkg := ⟨String × String, String, (s, "t"), rfl⟩

@[noinline] def leftOf (p : Pkg) : p.B := (cast p.isPair p.val).1

@[noinline] def rightOf (p : Pkg) : String := (cast p.isPair p.val).2

def main : IO Unit := do
  let r : Float := Shape.dim .circle (Shape.mk .circle)
  let wh : Float × Float := Shape.dim .rect (Shape.mk .rect)
  IO.println s!"circle radius: {r}"
  IO.println s!"rect: {wh.1} x {wh.2}"
  IO.println s!"labels: {Shape.label .circle (Shape.mk .circle)} {Shape.label .rect (Shape.mk .rect)}"
  let c : String := val true (mkV true)
  IO.println s!"val true: [{c}] tag {tag true (mkV true)}"
  let d : List Nat := val false (mkV false)
  IO.println s!"val false: {d} tag {tag false (mkV false)}"
  let p := mkPkg 41
  let h : p.B = Nat := rfl
  IO.println s!"left: {cast h (leftOf p) + 1} right: {rightOf p}"
  let q := mkPkgStr "str"
  let h' : q.B = String := rfl
  IO.println s!"left: {cast h' (leftOf q) ++ "!"} right: {rightOf q}"
