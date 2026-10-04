import Lean
import LeanToReussir.PassConfig

/-!
# State machines entered and re-entered without allocation (optimization `state-machines`)

The core lowers a loop through outlined join points as a state machine
over an enum of entry points (J4, `Lower/StateMachine`): the entry variant
`e` carries the declaration's parameters and each outlined join point's
variant its fields (the variables its body uses, then its parameters), so
every call and every jump allocates a variant. This pass passes all those
values as parameters of the state machine's function instead, so that
every variant is nullary: calling the declaration, its self tail calls and
its jumps allocate nothing (translation plan §5.6).

The function's parameters are slots, one per type and position: a variant
puts its `i`-th field of type `T` in the `i`-th slot of type `T` (a field
named like a parameter of the declaration, a variable the jump passes on
unchanged, takes that parameter's slot), so there are as many slots of
type `T` as the variant with the most fields of type `T` has. Each arm of
the function binds its fields from their slots. A jump passes its fields
in their slots and a placeholder in every other slot: never a live value,
which would be kept alive across the jump (an array the loop updates
before jumping, `a.set! i v`, would then be shared and copied at every
iteration). Placeholders are cheap: `zeroValue`'s (a constant, or a value
built once and kept in a once-cell), and for a string one shared empty
string (`l2r_str_shared_empty`, no once-cell).

Soundness guard (checked on every state machine): a slot's placeholder is
evaluated at every jump that does not fill it, so a type without a finite
placeholder (`zeroFinite`: a type without a finite value, such as `Empty`)
gets no slot: such a field stays in its variant, which is then allocated as
in the core form.

Jumps and self tail calls are lowered before every variant is known, so
they are emitted as `fn(values…, mode::v)` and put in slots when the state
machine is emitted (`smCall`).
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- The placeholder of a slot of type `t` (see the module comment), if `t`
has a finite one (`zeroFinite`, the soundness guard). -/
def slotPlaceholder? (t : RR.Ty) : LowerM (Option RR.Expr) := do
  if t == .named "LStr" then return some (.call "l2r_str_shared_empty" #[] #[])
  if ← zeroFinite t then return some (← zeroValue t)
  return none

mutual
  /-- `e` with every call `f(args)` replaced by `g f args` where that gives
  an expression. -/
  partial def rewriteCallsE (g : String → Array RR.Expr → LowerM (Option RR.Expr)) : RR.Expr → LowerM RR.Expr
    | .call f tys args => do
      let args ← args.mapM (rewriteCallsE g)
      return (← g f args).getD (.call f tys args)
    | .apply f a => return .apply (← rewriteCallsE g f) (← rewriteCallsE g a)
    | .ctor t v args => return .ctor t v (← args.mapM (rewriteCallsE g))
    | .field e i => return .field (← rewriteCallsE g e) i
    | .cast e t => return .cast (← rewriteCallsE g e) t
    | .lam p t b => return .lam p t (← rewriteCallsB g b)
    | .ite c t e => return .ite (← rewriteCallsE g c) (← rewriteCallsB g t) (← rewriteCallsB g e)
    | .mtch s arms => return .mtch (← rewriteCallsE g s) (← arms.mapM fun a => return { a with body := ← rewriteCallsB g a.body })
    | .block b => return .block (← rewriteCallsB g b)
    | e => return e

  partial def rewriteCallsB (g : String → Array RR.Expr → LowerM (Option RR.Expr)) (b : RR.Block) : LowerM RR.Block := do
    return ⟨← b.lets.mapM fun (x, t, e) => return (x, t, ← rewriteCallsE g e), ← rewriteCallsE g b.result⟩
end

/-- Where a state machine's values go: its slots (name, type, placeholder)
and, per variant, the slot of each field (`none`: it stays in the
variant). -/
structure SlotLayout where
  slots : Array (String × RR.Ty × RR.Expr) := #[]
  fields : Std.HashMap String (Array (Option Nat)) := {}

/-- The slots of the variants `variants` (the entry, carrying the
declaration's parameters, first); see the module comment. -/
def slotLayout (variants : Array (String × Array (String × RR.Ty))) : LowerM SlotLayout := do
  let mut ok : Std.HashMap RR.Ty (Option RR.Expr) := {}
  let mut lay : SlotLayout := {}
  let mut paramSlot : Std.HashMap String Nat := {}
  for h : vi in [:variants.size] do
    let (v, fs) := variants[vi]
    let mut used : Std.HashSet Nat := {}
    let mut out : Array (Option Nat) := Array.replicate fs.size none
    -- Variables passed on unchanged keep their parameter's slot.
    for h : i in [:fs.size] do
      let (n, t) := fs[i]
      if let some s := paramSlot[n]? then
        if lay.slots[s]!.2.1 == t && !used.contains s then
          out := out.set! i (some s)
          used := used.insert s
    for h : i in [:fs.size] do
      if out[i]!.isSome then continue
      let (n, t) := fs[i]
      let ph? ← match ok[t]? with
        | some r => pure r
        | none => do
          -- The soundness guard: no slot for a type without a finite
          -- placeholder.
          let r ← slotPlaceholder? t
          ok := ok.insert t r
          pure r
      let some ph := ph? | continue
      let free := (List.range lay.slots.size).find? fun s => lay.slots[s]!.2.1 == t && !used.contains s
      let s ← match free with
        | some s => pure s
        | none => do
          let name ← fresh "s"
          lay := { lay with slots := lay.slots.push (name, t, ph) }
          pure (lay.slots.size - 1)
      out := out.set! i (some s)
      used := used.insert s
      if vi == 0 then paramSlot := paramSlot.insert n s
    lay := { lay with fields := lay.fields.insert v out }
  return lay

/-- The call entering state machine `sm` at variant `v` (fields `fs`) with
values `vals` (in field order): each value in its slot, placeholders in the
other slots, then the variant with the fields that have no slot. Values
other than variables and literals are bound first, in their order. -/
def smCall (sm : StateMachine) (lay : SlotLayout) (v : String) (fs : Array (String × RR.Ty))
    (vals : Array RR.Expr) : LowerM RR.Expr := do
  let some out := lay.fields[v]? | throwError "lean2rr: unknown state-machine variant {v}"
  let mut lets := #[]
  let mut args := lay.slots.map (·.2.2)
  let mut rest := #[]
  for h : i in [:vals.size] do
    let val ← match vals[i] with
      | e@(.var _) | e@(.atom _) => pure e
      | e => do
        let x ← fresh "sv"
        lets := lets.push (x, fs[i]?.map (·.2), e)
        pure (.var x)
    match out[i]? with
    | some (some s) => args := args.set! s val
    | _ => rest := rest.push val
  let call := RR.Expr.call sm.fn #[] (args.push (.ctor sm.mode (some v) rest))
  return if lets.isEmpty then call else .block ⟨lets, call⟩

/-- Emit declaration `d` lowered as state machine `sm` with its values in
slots (see the module comment): the dispatching function (the slots, then
the entry point) over the lowered entry code `block` and the outlined join
points' variants (`LowerState.smArms`), the declaration's function, which
enters at its own variant, and the entry-point enum. -/
def emitStateMachineAlongside (d : Decl .pure) (sm : StateMachine) (params : Array (String × RR.Ty)) (ret : RR.Ty)
    (block : RR.Block) : LowerM Unit := do
  let arms := (← get).smArms
  let variants := #[(sm.entry, params)] ++ arms.map fun (v, fps, _) => (v, fps)
  let lay ← slotLayout variants
  let fieldsOf : Std.HashMap String (Array (String × RR.Ty)) := variants.foldl (fun m (v, fs) => m.insert v fs) {}
  -- The calls the lowering left as `fn(values…, mode::v)`.
  let place (f : String) (args : Array RR.Expr) : LowerM (Option RR.Expr) := do
    if f != sm.fn then return none
    let some (.ctor m (some v) #[]) := args.back? | return none
    if m != sm.mode then return none
    let some fs := fieldsOf[v]? | return none
    return some (← smCall sm lay v fs args.pop)
  -- The fields of variant `v` without a slot.
  let kept (v : String) (fs : Array (String × RR.Ty)) : Array (String × RR.Ty) :=
    let out := lay.fields.getD v #[]
    (fs.zipIdx.filter fun (_, i) => (out[i]?.join).isNone).map (·.1)
  -- A shared enum: Reussir miscompiles `[value]` enums whose arms have
  -- different layouts (translation plan §9). Its variants are nullary
  -- unless a field has no slot.
  let mode := RR.Item.enum sm.mode false (variants.map fun (v, fs) => (v, (kept v fs).map (·.2)))
  let mkArm (v : String) (fs : Array (String × RR.Ty)) (b : RR.Block) : LowerM RR.Arm := do
    let out := lay.fields.getD v #[]
    let bind := fs.zipIdx.filterMap fun ((n, t), i) =>
      (out[i]?.join).map fun s => (n, some t, RR.Expr.var lay.slots[s]!.1)
    let b ← rewriteCallsB place b
    return { ty := sm.mode, ctor := some v, binders := (kept v fs).map (some ·.1), body := ⟨bind ++ b.lets, b.result⟩ }
  let mut matchArms := #[← mkArm sm.entry params block]
  for (v, fps, b) in arms do matchArms := matchArms.push (← mkArm v fps b)
  let m ← fresh "m"
  let slotParams := lay.slots.map fun (n, t, _) => (n, t)
  let enter ← smCall sm lay sm.entry params (params.map fun (n, _) => RR.Expr.var n)
  modify fun s => { s with
    typeItems := s.typeItems.push mode
    fns := s.fns
      |>.push (.fn sm.fn (slotParams.push (m, .named sm.mode)) ret (.ofExpr (.mtch (.var m) matchArms)))
      |>.push (.fn (fnName d.name) params ret (.ofExpr enter))
    smArms := #[] }

/-- The form of state machine this pass plans and handles. -/
def alongsideForm : Name := `alongside

/-- A self tail call of the declaration: the new arguments, then the
entry, put in slots when the state machine is emitted. -/
def alongsideSelfCall (sm : StateMachine) (args : Array RR.Expr) : LowerM RR.Expr :=
  return .call sm.fn #[] (args.push (.ctor sm.mode (some sm.entry) #[]))

/-- A jump to an outlined join point's variant: its fields, then the
variant, put in slots when the state machine is emitted. -/
def alongsideJumpCall (sm : StateMachine) (variant : String) (fields : Array RR.Expr) : LowerM RR.Expr :=
  return .call sm.fn #[] (fields.push (.ctor sm.mode (some variant) #[]))

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
