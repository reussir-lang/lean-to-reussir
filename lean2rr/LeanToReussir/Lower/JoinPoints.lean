import LeanToReussir.Lower.Values

/-!
# Join-point strategy

The choice between J1 (single jump: inline), J2 (all paths join:
structured `let`) and J3 (outline) for each join point (translation plan
§5.6), and the variable-use analyses of LCNF code that the lowering and
its optional passes share. J4 (state machines, `Lower/StateMachine`) is
core; J1′ (small join points duplicated) and the sinking of join points
before the choice are optional passes (Opt/JpSmall, Opt/JpSink), and so is
the allocation-free form of J4's state machines (Opt/StateMachines).
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Number of jumps to each join point. -/
partial def countJumps : Code .pure → Std.HashMap FVarId Nat → Std.HashMap FVarId Nat
  | .jmp j _, m => m.insert j (m.getD j 0 + 1)
  | .let _ k, m => countJumps k m
  | .fun d k _, m | .jp d k, m => countJumps k (countJumps d.value m)
  | .cases c, m => c.alts.foldl (fun m alt => countJumps alt.getCode m) m
  | _, m => m

/-- Does every path through `c` end in a jump to one of `targets` (or in
`unreach`)? Nested join points in `outlined` are functions, so jumping to
them does not count. -/
partial def endsInJumps (c : Code .pure) (targets : FVarIdSet) (outlined : FVarIdSet) : Bool :=
  match c with
  | .let _ k => endsInJumps k targets outlined
  | .fun _ k _ => endsInJumps k targets outlined
  | .jmp j _ => targets.contains j
  | .unreach _ => true
  | .return _ => false
  | .cases cs => cs.alts.all fun alt => endsInJumps alt.getCode targets outlined
  | .jp d k =>
    if !outlined.contains d.fvarId && endsInJumps d.value targets outlined then
      endsInJumps k (targets.insert d.fvarId) outlined
    else endsInJumps k targets outlined
  | _ => false

/-- Join points jumped to from inside the body of join point `inside`. -/
partial def jumpsIn : Code .pure → FVarIdSet → FVarIdSet
  | .jmp j _, s => s.insert j
  | .let _ k, s => jumpsIn k s
  | .fun d k _, s | .jp d k, s => jumpsIn k (jumpsIn d.value s)
  | .cases c, s => c.alts.foldl (fun s alt => jumpsIn alt.getCode s) s
  | _, s => s

/-- The bodies of the join points of `c` (binders are unique). -/
partial def jpBodiesOf (c : Code .pure) (acc : Std.HashMap FVarId (Code .pure) := {}) :
    Std.HashMap FVarId (Code .pure) :=
  match c with
  | .let _ k => jpBodiesOf k acc
  | .fun d k _ => jpBodiesOf k (jpBodiesOf d.value acc)
  | .jp d k => jpBodiesOf k (jpBodiesOf d.value (acc.insert d.fvarId d.value))
  | .cases cs => cs.alts.foldl (fun acc alt => jpBodiesOf alt.getCode acc) acc
  | _ => acc

/-- Choose a strategy for every join point of a declaration body: the set
of outlined (J3) join points; others are J1 (single jump), J2, or
duplicated at their jumps (J1′, those `duplicate` selects: the lowering hook
`LowerHooks.duplicateJp`, given the bodies of all join points and the
number of jumps). -/
partial def chooseOutlined (duplicate : Std.HashMap FVarId (Code .pure) → FunDecl .pure → Nat → Bool)
    (body : Code .pure) : FVarIdSet := Id.run do
  let counts := countJumps body {}
  -- All join points with their scope.
  let mut jps : Array (FunDecl .pure × Code .pure) := #[]
  let rec gather (c : Code .pure) (acc : Array (FunDecl .pure × Code .pure)) : Array (FunDecl .pure × Code .pure) :=
    match c with
    | .let _ k => gather k acc
    | .fun d k _ => gather k (gather d.value acc)
    | .jp d k => gather k (gather d.value (acc.push (d, k)))
    | .cases cs => cs.alts.foldl (fun acc alt => gather alt.getCode acc) acc
    | _ => acc
  jps := gather body #[]
  let bodies := jpBodiesOf body
  let mut outlined : FVarIdSet := {}
  let mut changed := true
  while changed do
    changed := false
    for (d, k) in jps do
      if outlined.contains d.fvarId then continue
      let single := counts.getD d.fvarId 0 ≤ 1
      -- A J2 join point cannot be the target of a jump from inside an outlined body.
      let jumpedFromOutlined := jps.any fun (d', _) =>
        outlined.contains d'.fvarId && (jumpsIn d'.value {}).contains d.fvarId
      let ok := single || duplicate bodies d (counts.getD d.fvarId 0) ||
        (endsInJumps k (({} : FVarIdSet).insert d.fvarId) outlined && !jumpedFromOutlined)
      if !ok then
        outlined := outlined.insert d.fvarId
        changed := true
  return outlined

/-! ## Variable uses -/

/-- Whether `x` occurs in `c`. -/
partial def hasFVar (x : FVarId) (c : Code .pure) : Bool :=
  let inArg : Arg .pure → Bool := fun | .fvar y => y == x | _ => false
  let inValue : LetValue .pure → Bool := fun
    | .fvar f args => f == x || args.any inArg
    | .const _ _ args _ => args.any inArg
    | .proj _ _ y _ => y == x
    | _ => false
  match c with
  | .let d k => inValue d.value || hasFVar x k
  | .fun d k _ | .jp d k => hasFVar x d.value || hasFVar x k
  | .jmp _ args => args.any inArg
  | .cases cs => cs.discr == x || cs.alts.any (hasFVar x ·.getCode)
  | .return y => y == x
  | .unreach _ => false

/-- Variables used in a let value. -/
def valueUses (v : LetValue .pure) (acc : Std.HashSet FVarId) : Std.HashSet FVarId :=
  let args (as : Array (Arg .pure)) (acc : Std.HashSet FVarId) :=
    as.foldl (fun acc a => match a with | .fvar y => acc.insert y | _ => acc) acc
  match v with
  | .fvar f as => args as (acc.insert f)
  | .const _ _ as _ => args as acc
  | .proj _ _ y _ => acc.insert y
  | _ => acc

/-- Variables used in `c`. -/
partial def codeUses (c : Code .pure) (acc : Std.HashSet FVarId) : Std.HashSet FVarId :=
  match c with
  | .let d k => codeUses k (valueUses d.value acc)
  | .fun d k _ | .jp d k => codeUses k (codeUses d.value acc)
  | .jmp _ as => as.foldl (fun acc a => match a with | .fvar y => acc.insert y | _ => acc) acc
  | .cases cs => cs.alts.foldl (fun acc alt => codeUses alt.getCode acc) (acc.insert cs.discr)
  | .return y => acc.insert y
  | .unreach _ => acc

end LeanToReussir
