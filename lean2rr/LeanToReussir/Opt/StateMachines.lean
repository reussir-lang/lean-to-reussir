import Lean
import LeanToReussir.PassConfig

/-!
# State machines entered without allocation (optimization `state-machines`)

The core lowers a loop through outlined join points as a state machine
whose entry variant `e` carries the declaration's parameters (J4,
`Lower/StateMachine`). This pass passes the parameters alongside the entry
point instead, unchanged when entering a join point, so that `e` is
nullary: calling the declaration (through its wrapper) and its self tail
calls allocate nothing (translation plan §5.6). A parameter is then still
referenced at a jump to a join point that does not use it, which keeps an
array the loop updates shared (copied on update) when it is passed both as
that parameter and in the join point's variant.
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

/-- Registry entry point: the core's plan, with the parameters alongside. -/
def Opt.StateMachines.install (c : PassConfig) : PassConfig :=
  let prev := c.lower.stateMachine
  { c with lower := { c.lower with stateMachine :=
      { plan := fun d body outlined pnames => (prev.plan d body outlined pnames).map ({ · with alongside := true })
        emit := emitStateMachineAlongside } } }

end LeanToReussir
