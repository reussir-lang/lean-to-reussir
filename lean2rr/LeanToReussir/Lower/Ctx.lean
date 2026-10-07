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
  /-- Types of join-point parameters, for lowering jump arguments (of the
parameters the join point takes: rule 4 removes the erased ones). -/
  jpParams : Std.HashMap FVarId (Array RR.Ty) := {}
  /-- Which parameters of each join point it takes (not the erased ones,
  rule 4); a jump passes the arguments of these. -/
  jpKeep : Std.HashMap FVarId (Array Bool) := {}
  sm : Option StateMachine := none
  /-- Bodies of the join points in scope. -/
  jpBodies : Std.HashMap FVarId (Code .pure) := {}
  /-- The join points in scope jumped to once (J1, inlined at their jump). -/
  jpSingle : FVarIdSet := {}
  /-- The declarations of the call cycle of the declaration being lowered
  (`JpScope.loop`). -/
  loop : NameSet := {}
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
  /-- The variables that the outlined join points in scope (J3, J4) capture,
  with their types. A jump to one passes them by these names, also where
  `vars` names the same LCNF variable differently (a hook or a `cases` bound
  it again in an alternative: Opt/NullaryScrutinee, a converted scrutinee,
  Opt/LazyFields); the names stay in scope, so a join point outlined there
  that jumps to one captures them too. Also the binders that a rebuilt
  matched value reads (`rebuild`, Opt/FreshRebuild), which `vars` no longer
  names when a field is converted: a join point outlined there that
  returns the value captures them. -/
  captured : Std.HashMap String RR.Ty := {}
  /-- The variables the declaration being lowered uses (`codeUses` of its
  body): a field parameter that is not used is not converted to its own
  type (`bindField`). -/
  used : Std.HashSet FVarId := {}
  /-- The variables of the declaration being lowered whose every use puts
  the value into a box (`boxedOnlyVars`): a field parameter among them
  keeps the field's `Box` (`bindField`), and a `let` among them is bound as
  a `Box` (`lowerCode`). -/
  boxedOnly : Std.HashSet FVarId := {}
  /-- The field parameters that `bindField` converted to their own types,
  with the name of the conversion's `let`: a binding drops such a `let`
  when its code does not use it (`dropUnusedConvs`), and `lazy-fields`'
  consuming re-match keeps it instead of converting the field again. -/
  fieldConv : Std.HashMap FVarId String := {}
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
