import Lean
import LeanToReussir.MonoTypesKeep
import LeanToReussir.LowerBase

/-!
# Stage 4: the context of code lowering

How jumps to join points are lowered (J1–J4, translation plan §5.6), the
state machine of a declaration lowered as one function (J4), matched
values whose fields are bound where they are used, and the context
`lowerCode` threads through a declaration's code.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- How a jump to a join point is lowered. -/
inductive JumpAction where
  /-- J1: the join point has a single jump; its body is inlined there. -/
  | inline (params : Array (Param .pure)) (body : Code .pure)
  /-- J2: jumps produce the join point's arguments as the value of the
  enclosing structured `let`. -/
  | yield (tys : Array RR.Ty)
  /-- J3: jumps call the outlined function with the captured variables
  followed by the arguments. -/
  | call (fn : String) (captured : Array String)
  /-- J4: jumps re-enter the declaration's state machine at the join point's
  variant (see `StateMachine`). -/
  | enter (variant : String) (captured : Array String)

/-- A self-recursive declaration with outlined join points is lowered as one
function over a `[value]` enum of entry points (J4, translation plan §5.6):
the declaration's own entry and one variant per outlined join point. Jumps to
those join points and self tail calls become self tail calls of that
function, which LLVM turns into a loop; separate functions would make the
loop mutually recursive. -/
structure StateMachine where
  /-- The dispatching function: the declaration's parameters, then the
  entry point. -/
  fn : String
  /-- The entry-point enum: nullary `e` for the declaration itself (no
  allocation), one variant per outlined join point. -/
  mode : String
  /-- The declaration, whose tail calls re-enter at `entry`. -/
  self : Name
  arity : Nat
  /-- Names of the declaration's parameters, passed through unchanged when
  entering a join point. -/
  params : Array String
  entry : String := "e"

/-- A matched value that stays live in its arm, whose fields are bound where
they are used (see `lowerCases`). `fields` are the arm's field parameters
that the arm uses, with their binder index and type; `pending` those not
bound yet. -/
structure LazyMatch where
  discr : FVarId
  scrut : String
  ty : String
  variant : String
  nbinders : Nat
  fields : Array (FVarId × Nat × RR.Ty)
  pending : Array (FVarId × Nat × RR.Ty)
  /-- A structure: its pending fields are projected where they are used
  (Reussir has no structure patterns). -/
  struct : Bool := false

structure CodeCtx where
  vars : Std.HashMap FVarId (String × RR.Ty) := {}
  jumps : Std.HashMap FVarId JumpAction := {}
  /-- Types of join-point parameters, for lowering jump arguments. -/
  jpParams : Std.HashMap FVarId (Array RR.Ty) := {}
  sm : Option StateMachine := none
  /-- Matched values whose fields are bound lazily (outermost first). -/
  lazy : Array LazyMatch := #[]
  /-- Bodies of the join points in scope. -/
  jpBodies : Std.HashMap FVarId (Code .pure) := {}

end LeanToReussir
