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
  -- Fields of enclosing lazily matched values (Opt/LazyFields) that are
  -- this variable need no binding here any more.
  return (#[(x, some sty, RR.Expr.ctor arm.ty (some arm.layout.variant) #[])],
    { ctx with vars := ctx.vars.insert arm.discr (x, sty),
               lazy := ctx.lazy.map fun l =>
                 { l with fields := l.fields.filter (·.1 != arm.discr),
                          pending := l.pending.filter (·.1 != arm.discr) } })

/-- Registry entry point. -/
def Opt.NullaryScrutinee.install (c : PassConfig) : PassConfig :=
  { c with lower := { c.lower with armPrelude := nullaryPrelude } }

end LeanToReussir
