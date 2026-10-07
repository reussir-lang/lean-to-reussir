import LeanToReussir.Lower.BoxedUses

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
  /-- Matched through the constructors of another type (a cast value,
  `castCases`): the layout is that type's. -/
  view : Bool := false

/-- `let`s placed before an alternative's code. -/
abbrev ArmLets := Array (String × Option RR.Ty × RR.Expr)

/-- Field parameter `p` of an alternative (its Reussir type `pt`, from its
mono type), whose value is `x : ft` (the field's type in the record),
bound in the context at its own type: a field of a parameter's type is a
`Box` in the record (one type per inductive, `nominalType`), and is unboxed
here, once, not at each use of the parameter. The `let` that converts it
(none when the types agree, at a unit type, which carries nothing, when
the declaration never uses the parameter, `CodeCtx.used`, or when every use
puts the value back into a box, `CodeCtx.boxedOnly`: the field's box is
then passed on), recorded in `CodeCtx.fieldConv`. -/
def bindField (ctx : CodeCtx) (p : FVarId) (pt : RR.Ty) (x : String) (ft : RR.Ty) :
    LowerM (ArmLets × CodeCtx) := do
  if pt == ft || !ctx.used.contains p then
    return (#[], { ctx with vars := ctx.vars.insert p (x, ft) })
  if pt == .unit then
    return (#[], { ctx with vars := ctx.vars.insert p ("L2RUnit::u{}", .unit) })
  -- Every use puts the value back into a box: the field's box is passed
  -- on, never unboxed (`boxedOnlyVars`).
  if ft == RR.Ty.box && ctx.boxedOnly.contains p then
    return (#[], { ctx with vars := ctx.vars.insert p (x, ft) })
  let y ← fresh "fv"
  return (#[(y, some pt, ← coerce (.var x) ft pt)],
    { ctx with vars := ctx.vars.insert p (y, pt), fieldConv := ctx.fieldConv.insert p y })

/-- The plain binding of a structure alternative's fields: every relevant
field projected from the matched value (and converted to the parameter's
own type, `bindField`), the others bound to the unit. -/
def bindStructFields (ctx : CodeCtx) (arm : CasesArm) : LowerM (ArmLets × CodeCtx) := do
  let mut ctx' := ctx
  let mut lets := #[]
  for h : i in [:arm.params.size] do
    let p := arm.params[i]
    match arm.layout.fields[i]? with
    | some (some (j, ft)) =>
      let x ← fresh "f"
      lets := lets.push (x, some ft, RR.Expr.field (.var arm.scrut) j)
      let (conv, c) ← bindField ctx' p.fvarId (← lowerType p.type) x ft
      lets := lets ++ conv
      ctx' := c
    | _ => ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId ("L2RUnit::u{}", .unit) }
  return (lets, ctx')

/-- J4 (translation plan §5.6): a declaration lowered as one state machine. -/
structure StateMachineHook where
  /-- The state machine to lower declaration `d` as (its body, outlined join
  points and parameter names given), if any. -/
  plan : (d : Decl .pure) → Code .pure → FVarIdSet → Array String → Option StateMachine
  /-- Emit the functions of declaration `d` lowered as a state machine, given
  its parameters, result type and lowered entry code (the outlined join
  points' variants are in `LowerState.smArms`). -/
  emit : (d : Decl .pure) → StateMachine → Array (String × RR.Ty) → RR.Ty → RR.Block → LowerM Unit
  /-- A self tail call of the declaration, with the new arguments. -/
  selfCall : StateMachine → Array RR.Expr → LowerM RR.Expr
  /-- A jump to an outlined join point: its variant and the variant's
  fields (captured variables, then the jump's arguments). -/
  jumpCall : StateMachine → String → Array RR.Expr → LowerM RR.Expr

structure LowerHooks where
  /-- A rewrite of a declaration's body before it is lowered (LCNF to LCNF,
  the same behaviour). Plain: none (Opt/JpSink). -/
  prepareBody : Code .pure → Code .pure := id
  /-- Whether a join point that is neither J1 nor J2 is duplicated at its
  jumps (J1′) instead of outlined (J3), given the join points in scope and
  its number of jumps. Plain: outlined (Opt/JpSmall). -/
  duplicateJp : JpScope → FunDecl .pure → Nat → Bool := fun _ _ _ => false
  /-- Declarations lowered as state machines (J4): when an outlined join
  point calls the declaration back in tail position. Plain: the entry
  variant carries the parameters (`Lower/StateMachine`; Opt/StateMachines
  passes them alongside). -/
  stateMachine : StateMachineHook :=
    { plan := stateMachinePlan, emit := emitStateMachine,
      selfCall := stateMachineSelfCall, jumpCall := stateMachineJumpCall }
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
