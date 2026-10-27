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
`arity` arguments, also in the bodies of the join points `c` declares (not
in local functions' bodies)? (A nested join point that is outlined is
one of `outlinedBodies` too, so `stateMachinePlan`'s answer is the same.) -/
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

/-- The code that the function of an outlined join point with body `c`
contains: `c`, and the bodies (`bodies`) of the join points it jumps to that
are not outlined, transitively. Those are inlined at the jump (J1 or J1′; a
J2 join point is jumped to from an outlined body only when that body
declares it, and then `c` contains its body already). -/
partial def withInlinedJps (bodies : Std.HashMap FVarId (Code .pure)) (outlined : FVarIdSet) (c : Code .pure) :
    Array (Code .pure) := Id.run do
  let mut out := #[c]
  let mut seen : FVarIdSet := {}
  let mut todo := (jumpsIn c {}).toArray
  while let some j := todo.back? do
    todo := todo.pop
    if seen.contains j || outlined.contains j then continue
    seen := seen.insert j
    if let some b := bodies[j]? then
      out := out.push b
      todo := todo ++ (jumpsIn b {}).toArray
  return out

/-- The declarations `c` calls in tail position (`let x := g args;
return x`, also in join points' bodies, not in local functions' bodies),
each with its number of arguments. -/
partial def tailCallees (c : Code .pure) (acc : Array (Name × Nat) := #[]) : Array (Name × Nat) :=
  match c with
  | .let d k =>
    let acc := match d.value, k with
      | .const g _ args _, .return x => if x == d.fvarId then acc.push (g, args.size) else acc
      | _, _ => acc
    tailCallees k acc
  | .fun _ k _ => tailCallees k acc
  | .jp d k => tailCallees k (tailCallees d.value acc)
  | .cases cs => cs.alts.foldl (fun acc alt => tailCallees alt.getCode acc) acc
  | _ => acc

/-- The cycles of tail calls between declarations: the strongly connected
groups, of two or more declarations, of the graph whose edges are the
saturated tail calls (`tailCallees`) of one declaration of `decls` to
another. Each declaration of a group maps to the group's declarations in
program order. Only declarations with code and parameters take part.
The lowering runs each group as one state machine (`lowerGroup`). -/
def tailCallGroups (decls : Array (Decl .pure)) : NameMap (Array Name) := Id.run do
  let arity : NameMap Nat := decls.foldl (init := {}) fun m d =>
    if d.value matches .code _ && !d.params.isEmpty then m.insert d.name d.params.size else m
  let byName : NameMap (Decl .pure) := decls.foldl (fun m d => m.insert d.name d) {}
  let order : NameMap Nat := decls.zipIdx.foldl (fun m (d, i) => m.insert d.name i) {}
  let succ (n : Name) : List Name := match byName.find? n with
    | some { value := .code c, .. } => (tailCallees c).toList.filterMap fun (g, k) =>
        if g != n && arity.find? g == some k then some g else none
    | _ => []
  let names := decls.filterMap fun d => if arity.contains d.name then some d.name else none
  let mut out : NameMap (Array Name) := {}
  for g in Lean.SCC.scc names.toList succ do
    if g.length < 2 then continue
    let members := g.toArray.qsort fun a b => (order.find? a).getD 0 < (order.find? b).getD 0
    for n in members do out := out.insert n members
  return out

/-- The state machine of declaration `d` (body `body`, outlined join points
`outlined`, parameter names `pnames`): J4 when an outlined join point
tail-calls the declaration, so that a loop passes through it, also from a
join point inlined into it. (Other calls need no state machine; going
through its entry wrapper would only cost an allocation per call.) With
`entryFn? = some fn`, a state machine of a cycle of tail calls whose first
declaration is `d` (`lowerGroup`), whatever its join points: entered by
function `fn`, named after it (`fn_sm`, `fn_mode`), as `d` keeps its own
function. -/
def stateMachinePlan (d : Decl .pure) (body : Code .pure) (outlined : FVarIdSet) (pnames : Array String)
    (entryFn? : Option String) : Option StateMachine :=
  let bodies := jpBodiesOf body
  let callsBack := entryFn?.isSome || (outlinedBodies body outlined).any fun c =>
    (withInlinedJps bodies outlined c).any (hasSelfTailCall d.name d.params.size)
  if !callsBack || d.params.isEmpty then none
  else
    let entryFn := entryFn?.getD (fnName d.name)
    some { fn := entryFn ++ "_sm", mode := entryFn ++ "_mode", self := d.name, arity := d.params.size,
           params := pnames, entryFn }

/-- The `let`s of the longest path through code `c` (a join point's body
continues the paths of its scope; a `cases` counts its longest
alternative): with the parameters, `cycleWeight`. -/
partial def longestPathLets : Code .pure → Nat
  | .let _ k => longestPathLets k + 1
  | .fun _ k _ => longestPathLets k
  | .jp d k => longestPathLets d.value + longestPathLets k
  | .cases cs => cs.alts.foldl (fun n alt => max n (longestPathLets alt.getCode)) 0
  | _ => 0

/-- An estimate of the stack frame of declaration `d` (code `body`): its
parameters and the `let`s of its longest path (`longestPathLets`), the
values its frame may have to hold at once. `lightMembers` compares the
declarations of a cycle of tail calls by it. -/
def cycleWeight (d : Decl .pure) (body : Code .pure) : Nat :=
  d.params.size + longestPathLets body

/-- Which declarations of a cycle of tail calls are light (their
`cycleWeight`s `ws`): at most 32, or at most twice the lightest one's. The
cycle gets a light state machine of its light declarations
(`lowerGroup`) when it has two or more light and one or more heavy
declarations. -/
def lightMembers (ws : Array Nat) : Array Bool :=
  let wmin := ws.foldl min (ws[0]?.getD 0)
  ws.map (· ≤ max 32 (2 * wmin))

/-- A self tail call of the state machine's declaration with arguments
`args`: entering it at the declaration's own entry, which carries them. -/
def stateMachineSelfCall (sm : StateMachine) (args : Array RR.Expr) : LowerM RR.Expr :=
  return .call sm.fn #[] #[.ctor sm.mode (some sm.entry) args]

/-- A jump entering the state machine at join-point variant `variant` with
its fields `fields` (captured variables, then the jump's arguments). -/
def stateMachineJumpCall (sm : StateMachine) (variant : String) (fields : Array RR.Expr) : LowerM RR.Expr :=
  return .call sm.fn #[] #[.ctor sm.mode (some variant) fields]

/-- Emit declaration `d` lowered as state machine `sm` (parameters carried by
the entry variant): the dispatching function over its entry point, whose
arms are the lowered entry code `block` and the outlined join points'
variants (`LowerState.smArms`, with the entries of the other declarations
of its cycle, `sm.members`); the function that enters at its own variant
with its parameters `params` (`sm.entryFn`: the declaration's function, or
for a cycle's state machine its entry function), and the entry functions
of the other declarations, each entering at its variant; and the
entry-point enum. -/
def emitStateMachine (d : Decl .pure) (sm : StateMachine) (params : Array (String × RR.Ty)) (ret : RR.Ty)
    (block : RR.Block) : LowerM Unit := do
  let arms ← getPart (·.smArms)
  -- A shared enum: Reussir reuses the cell of the matched value for the
  -- variant of the next call or jump (token reuse), so a jump stores its
  -- fields into that cell. A `[value]` enum would move the whole variant at
  -- every jump, which ran more instructions where the variants are wide
  -- (RtSmDecode with `state-machines` off, 2026-10-19: 239 to 370 million,
  -- though 42,835 to 135 allocations).
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
      |>.push (.fn sm.entryFn params ret
          (.ofExpr (.call sm.fn #[] #[.ctor sm.mode (some sm.entry) (params.map fun (n, _) => RR.Expr.var n)])))
      |>.append (sm.members.map fun mb => .fn mb.entryFn mb.params ret
          (.ofExpr (.call sm.fn #[] #[.ctor sm.mode (some mb.variant) (mb.params.map fun (n, _) => RR.Expr.var n)])))
    smArms := #[] }

end LeanToReussir
