import LeanToReussir.Lower.JoinPoints

/-!
# Loops through outlined join points: state machines (J4)

When an outlined join point (J3) of a declaration calls the declaration
back in tail position (a loop whose body is a DAG of join points, e.g. a
chain of `if`s with shared continuations), J3 alone makes the loop mutually
recursive: LLVM turns a mutual tail call into a jump only when it is a
sibling call, and Reussir's reference counting after the call can keep it
from being one, so such a loop would use stack per iteration where native
Lean runs in constant stack (translation plan §5.6). The declaration is
then one function over an enum of entry points: `e`, carrying the
declaration's parameters, and one variant per outlined join point (its
captured variables and parameters). Self tail calls and jumps to those join
points are self tail calls of that function, which LLVM turns into a loop.

This is the core translation's form: every value a jump needs travels in
its variant, so no value is kept alive by being passed along (an array
updated before the jump stays unique). Opt/StateMachines passes the
parameters alongside instead, so that `e` is nullary and entering the
declaration allocates nothing.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Does `c` contain a tail call `let x := f args; return x` of `f` with
`arity` arguments (outside nested join-point bodies, which are checked on
their own when outlined)? -/
partial def hasSelfTailCall (f : Name) (arity : Nat) : Code .pure → Bool
  | .let d k =>
    match d.value, k with
    | .const g _ args _, .return x => (g == f && args.size == arity && x == d.fvarId) || hasSelfTailCall f arity k
    | _, _ => hasSelfTailCall f arity k
  | .fun _ k _ => hasSelfTailCall f arity k
  | .jp d k => hasSelfTailCall f arity d.value || hasSelfTailCall f arity k
  | .cases c => c.alts.any (hasSelfTailCall f arity ·.getCode)
  | _ => false

/-- The bodies of the outlined join points of `c`. -/
partial def outlinedBodies (c : Code .pure) (outlined : FVarIdSet) : Array (Code .pure) :=
  go c #[]
where
  go (c : Code .pure) (acc : Array (Code .pure)) : Array (Code .pure) :=
    match c with
    | .let _ k => go k acc
    | .fun d k _ => go k (go d.value acc)
    | .jp d k => go k (go d.value (if outlined.contains d.fvarId then acc.push d.value else acc))
    | .cases cs => cs.alts.foldl (fun acc alt => go alt.getCode acc) acc
    | _ => acc

/-- The state machine of declaration `d` (body `body`, outlined join points
`outlined`, parameter names `pnames`): J4 when an outlined join point
tail-calls the declaration, so that a loop passes through it. (Other calls
need no state machine; going through its entry wrapper would only cost an
allocation per call.) -/
def stateMachinePlan (d : Decl .pure) (body : Code .pure) (outlined : FVarIdSet) (pnames : Array String) :
    Option StateMachine :=
  let callsBack := outlinedBodies body outlined |>.any (hasSelfTailCall d.name d.params.size)
  if !callsBack || d.params.isEmpty then none
  else
    let base := fnName d.name
    some { fn := base ++ "_sm", mode := base ++ "_mode", self := d.name, arity := d.params.size, params := pnames }

/-- Emit declaration `d` lowered as state machine `sm` (parameters carried by
the entry variant): the dispatching function over its entry point, whose
arms are the lowered entry code `block` and the outlined join points'
variants (`LowerState.smArms`); the declaration's function, which enters at
its own variant with its parameters `params`; and the entry-point enum. -/
def emitStateMachine (d : Decl .pure) (sm : StateMachine) (params : Array (String × RR.Ty)) (ret : RR.Ty)
    (block : RR.Block) : LowerM Unit := do
  let arms := (← get).smArms
  -- A shared enum: Reussir miscompiles `[value]` enums whose arms have
  -- different layouts (translation plan §9); Reussir reuses the cell of
  -- the matched value.
  let mode := RR.Item.enum sm.mode false
    (#[(sm.entry, params.map (·.2))] ++ arms.map fun (v, fps, _) => (v, fps.map (·.2)))
  let mkArm (v : String) (names : Array String) (b : RR.Block) : RR.Arm :=
    { ty := sm.mode, ctor := some v, binders := names.map some, body := b }
  let matchArms := #[mkArm sm.entry (params.map (·.1)) block] ++ arms.map fun (v, fps, b) => mkArm v (fps.map (·.1)) b
  let m ← fresh "m"
  modify fun s => { s with
    typeItems := s.typeItems.push mode
    fns := s.fns
      |>.push (.fn sm.fn #[(m, .named sm.mode)] ret (.ofExpr (.mtch (.var m) matchArms)))
      |>.push (.fn (fnName d.name) params ret
          (.ofExpr (.call sm.fn #[] #[.ctor sm.mode (some sm.entry) (params.map fun (n, _) => RR.Expr.var n)])))
    smArms := #[] }

end LeanToReussir
