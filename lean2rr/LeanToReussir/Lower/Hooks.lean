import LeanToReussir.Lower.JoinPoints

/-!
# Stage 4: the hooks of code lowering

The points where optional passes change how declarations and their code are
lowered. Each default is the plain translation; an optimization module
(`Opt/*.lean`) supplies another function in its `install`, and
Opt/Registry.lean installs the enabled ones. `lowerDecl` and the code
lowering (`Lower/Code`) take the hooks as their first argument.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- An alternative of a `cases` whose fields are being bound. -/
structure CasesArm where
  /-- The matched variable, its Reussir name and its generated type. -/
  discr : FVarId
  scrut : String
  ty : String
  /-- The constructor's layout over the matched value's record. -/
  layout : CtorLayout
  /-- The alternative's field parameters and code. -/
  params : Array (Param .pure)
  code : Code .pure
  /-- A shared (heap) value matched at its own type, whose fields could be
  bound later than at the match. -/
  shared : Bool

/-- `let`s placed before an alternative's code. -/
abbrev ArmLets := Array (String × Option RR.Ty × RR.Expr)

/-- The plain binding of a structure alternative's fields: every relevant
field projected from the matched value, the others bound to the unit. -/
def bindStructFields (ctx : CodeCtx) (arm : CasesArm) : LowerM (ArmLets × CodeCtx) := do
  let mut ctx' := ctx
  let mut lets := #[]
  for h : i in [:arm.params.size] do
    let p := arm.params[i]
    match arm.layout.fields[i]? with
    | some (some (j, ft)) =>
      let x ← fresh "f"
      lets := lets.push (x, some ft, RR.Expr.field (.var arm.scrut) j)
      ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, ft) }
    | _ => ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId ("L2RUnit::u{}", .unit) }
  return (lets, ctx')

structure LowerHooks where
  /-- A rewrite of a declaration's body before it is lowered (LCNF to LCNF,
  the same behaviour). Plain: none (Opt/JpSink). -/
  prepareBody : Code .pure → Code .pure := id
  /-- Whether a join point that is neither J1 nor J2 is duplicated at its
  jumps (J1′) instead of outlined (J3). Plain: outlined (Opt/JpSmall). -/
  duplicateJp : FunDecl .pure → Bool := fun _ => false
  /-- Whether a constant (a declaration without parameters) with body
  `body` is recomputed at every use instead of computed once and kept in a
  once-cell (`cafAccessor`). Plain: kept (Opt/CheapConsts). -/
  recomputeConst : Code .pure → LowerM Bool := fun _ => pure false
  /-- The fields of a structure alternative, bound before its code: the
  `let`s and the context for the code. Plain: every field projected at the
  match (`bindStructFields`; Opt/LazyFields binds some later). -/
  structFields : CodeCtx → CasesArm → LowerM (ArmLets × CodeCtx) := bindStructFields
  /-- The fields of an enum alternative, bound by the match's `binders` (at
  record positions) and in the context: the binders and the context for the
  code. Plain: unchanged (Opt/LazyFields unbinds some, bound later). -/
  enumFields : CodeCtx → CasesArm → Array (Option String) → LowerM (Array (Option String) × CodeCtx) :=
    fun ctx _ binders => pure (binders, ctx)
  /-- `let`s before an enum alternative's code, given its binders. Plain:
  none (Opt/NullaryScrutinee). -/
  armPrelude : CodeCtx → CasesArm → Array (Option String) → LowerM (ArmLets × CodeCtx) :=
    fun ctx _ _ => pure (#[], ctx)
  /-- Lowering an alternative's code (fields bound): `self` lowers an
  alternative, `code` any code, `retTy` is the result type. Plain: `code`
  (Opt/LazyFields matches values again to bind fields bound later). -/
  lowerAlt : (self code : CodeCtx → Code .pure → LowerM RR.Block) → CodeCtx → RR.Ty → Code .pure →
      LowerM RR.Block := fun _ code ctx _ k => code ctx k

end LeanToReussir
