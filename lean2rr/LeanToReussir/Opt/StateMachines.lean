import Lean
import LeanToReussir.PassConfig

/-!
# State machines entered without allocation (optimization `state-machines`)

The core lowers a loop through outlined join points as a state machine
whose entry variant `e` carries the declaration's parameters (J4,
`Lower/StateMachine`). This pass passes the parameters beside the entry
point instead, so that `e` is nullary: calling the declaration (through its
wrapper) and its self tail calls allocate nothing (translation plan §5.6).

A jump to an outlined join point must still pass something for those
parameters. The join point's variant carries every variable its body uses
(and its arm binds them under their own names), so the values passed
beside it are never read: a jump passes placeholders (`zeroValue`), never
the parameters themselves. Passing a parameter would keep it alive across
the jump, so that an array the loop updates before jumping (`a.set! i v`)
would be shared and copied at every iteration.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Emit declaration `d` lowered as state machine `sm` with its parameters
alongside: the dispatching function (its parameters `params`, then the
entry point) over the lowered entry code `block` and the outlined join
points' variants (`LowerState.smArms`), the declaration's function, which
enters at its own variant, and the entry-point enum. -/
def emitStateMachineAlongside (d : Decl .pure) (sm : StateMachine) (params : Array (String × RR.Ty)) (ret : RR.Ty)
    (block : RR.Block) : LowerM Unit := do
  let arms := (← get).smArms
  -- A shared enum: Reussir miscompiles `[value]` enums whose arms have
  -- different layouts (translation plan §9); Reussir reuses the cell of
  -- the matched value.
  let mode := RR.Item.enum sm.mode false
    (#[(sm.entry, #[])] ++ arms.map fun (v, fps, _) => (v, fps.map (·.2)))
  let mkArm (v : String) (names : Array String) (b : RR.Block) : RR.Arm :=
    { ty := sm.mode, ctor := some v, binders := names.map some, body := b }
  let matchArms := #[mkArm sm.entry #[] block] ++ arms.map fun (v, fps, b) => mkArm v (fps.map (·.1)) b
  let m ← fresh "m"
  modify fun s => { s with
    typeItems := s.typeItems.push mode
    fns := s.fns
      |>.push (.fn sm.fn (params.push (m, .named sm.mode)) ret (.ofExpr (.mtch (.var m) matchArms)))
      |>.push (.fn (fnName d.name) params ret
          (.ofExpr (.call sm.fn #[] ((params.map fun (n, _) => RR.Expr.var n).push (.ctor sm.mode (some sm.entry) #[])))))
    smArms := #[] }

/-- The form of state machine this pass plans and handles. -/
def alongsideForm : Name := `alongside

/-- A self tail call of the declaration: the new arguments, then the
nullary entry. -/
def alongsideSelfCall (sm : StateMachine) (args : Array RR.Expr) : LowerM RR.Expr :=
  return .call sm.fn #[] (args.push (.ctor sm.mode (some sm.entry) #[]))

/-- A jump to an outlined join point's variant: placeholders for the
parameters beside it (see the module comment), then the variant. -/
def alongsideJumpCall (sm : StateMachine) (variant : String) (fields : Array RR.Expr) : LowerM RR.Expr := do
  let some d := (← read).decls.find? sm.self | throwError "lean2rr: no declaration {sm.self}"
  let (ps, _) := splitFnType d.type sm.arity
  let placeholders ← ps.mapM fun p => do zeroValue (← lowerType p)
  return .call sm.fn #[] (placeholders.push (.ctor sm.mode (some variant) fields))

/-- Registry entry point: the state machines the earlier hooks plan take
this form; the hooks handle it and leave other forms to the earlier ones. -/
def Opt.StateMachines.install (c : PassConfig) : PassConfig :=
  let prev := c.lower.stateMachine
  { c with lower := { c.lower with stateMachine :=
      { plan := fun d body outlined pnames =>
          (prev.plan d body outlined pnames).map ({ · with form := alongsideForm })
        emit := fun d sm params ret block =>
          if sm.form == alongsideForm then emitStateMachineAlongside d sm params ret block
          else prev.emit d sm params ret block
        selfCall := fun sm args =>
          if sm.form == alongsideForm then alongsideSelfCall sm args else prev.selfCall sm args
        jumpCall := fun sm variant fields =>
          if sm.form == alongsideForm then alongsideJumpCall sm variant fields
          else prev.jumpCall sm variant fields } } }

end LeanToReussir
