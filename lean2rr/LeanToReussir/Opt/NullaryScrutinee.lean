import Lean
import LeanToReussir.PassConfig

/-!
# Matched constructors without fields rebuilt (optimization `nullary-scrutinee`)

In the alternative of a constructor without fields, the matched value is
that constructor, which costs nothing to build in Reussir (a nullary
variant of a shared enum allocates nothing): a use of the matched value
there (`leaf` used as the children of a new node) uses a new nullary value
instead, so the matched value is not kept alive by the use. Without this
pass the matched value itself is used.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- The `let` binding the matched variable again, to its constructor, in an
alternative of a constructor without fields that uses it. -/
def nullaryPrelude (ctx : CodeCtx) (arm : CasesArm) (binders : Array (Option String)) :
    LowerM (ArmLets × CodeCtx) := do
  unless binders.isEmpty && hasFVar arm.discr arm.code do return (#[], ctx)
  let sty := RR.Ty.named arm.ty
  let x ← fresh "nc"
  -- The variable is pinned to this binding: no other hook binds it again
  -- in this alternative (e.g. as a field of an enclosing value).
  return (#[(x, some sty, RR.Expr.ctor arm.ty (some arm.layout.variant) #[])],
    { ctx with vars := ctx.vars.insert arm.discr (x, sty), pinned := ctx.pinned.insert arm.discr })

/-- Registry entry point: after the bindings of the hooks installed before. -/
def Opt.NullaryScrutinee.install (c : PassConfig) : PassConfig :=
  let prev := c.lower.armPrelude
  { c with lower := { c.lower with armPrelude := fun ctx arm binders => do
      let (lets, ctx) ← prev ctx arm binders
      let (more, ctx) ← nullaryPrelude ctx arm binders
      return (lets ++ more, ctx) } }

end LeanToReussir
