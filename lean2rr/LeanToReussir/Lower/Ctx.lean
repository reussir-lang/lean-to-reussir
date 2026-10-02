import Lean
import LeanToReussir.MonoTypesKeep
import LeanToReussir.LowerBase

/-!
# Stage 4: the context of code lowering

How jumps to join points are lowered (J1–J4, translation plan §5.6), the
state machine of a declaration lowered as one function (J4), and the
context `lowerCode` threads through a declaration's code, with a slot for
the state of optional passes.
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

/-- A self-recursive declaration whose outlined join points call it back in
tail position is lowered as one function over an enum of entry points (J4,
translation plan §5.6): the declaration's own entry and one variant per
outlined join point. Jumps to those join points and self tail calls become
self tail calls of that function, which LLVM turns into a loop; separate
functions would make the loop mutually recursive, using stack per
iteration. Planned and emitted by the lowering hook
`LowerHooks.stateMachine`; `lowerCode` re-enters it when the context has
one. -/
structure StateMachine where
  /-- The dispatching function. -/
  fn : String
  /-- The entry-point enum: `e` for the declaration itself, one variant per
  outlined join point. -/
  mode : String
  /-- The declaration, whose tail calls re-enter at `entry`. -/
  self : Name
  arity : Nat
  /-- Names of the declaration's parameters. -/
  params : Array String
  entry : String := "e"
  /-- Which form of state machine this is: `.anonymous` for the core's
  (`Lower/StateMachine`); an optional pass that plans another form tags it
  with its name, and its hooks handle that form only. -/
  form : Name := .anonymous

structure CodeCtx where
  vars : Std.HashMap FVarId (String × RR.Ty) := {}
  jumps : Std.HashMap FVarId JumpAction := {}
  /-- Types of join-point parameters, for lowering jump arguments. -/
  jpParams : Std.HashMap FVarId (Array RR.Ty) := {}
  sm : Option StateMachine := none
  /-- Bodies of the join points in scope. -/
  jpBodies : Std.HashMap FVarId (Code .pure) := {}
  /-- Variables that a hook bound again, in the current alternative, to a
  value of its own equal to theirs (Opt/NullaryScrutinee): other hooks must
  not bind them again there. -/
  pinned : FVarIdSet := {}
  /-- Variables bound in the function being lowered to an application of a
  constant (a declaration or a constructor) to at least one argument: the
  constant and the number of arguments. -/
  letCalls : Std.HashMap FVarId (Name × Nat) := {}
  /-- Matched values that the current alternative returns as an expression
  of their type instead of themselves (Opt/FreshRebuild: the constructor
  rebuilt from the alternative's fields). Plain: none. -/
  rebuild : Std.HashMap FVarId (RR.Expr × RR.Ty) := {}
  /-- The state optional passes keep in the context, by the pass's name
  (`CodeCtx.getExt?`, `CodeCtx.setExt`). -/
  ext : NameMap Dynamic := {}

/-- The state optional pass `key` keeps in the context, if any. -/
def CodeCtx.getExt? (ctx : CodeCtx) (α : Type) [TypeName α] (key : Name) : Option α :=
  (ctx.ext.find? key).bind (·.get? α)

/-- The context with optional pass `key`'s state set to `v`. -/
def CodeCtx.setExt {α : Type} [TypeName α] (ctx : CodeCtx) (key : Name) (v : α) : CodeCtx :=
  { ctx with ext := ctx.ext.insert key (.mk v) }

end LeanToReussir
