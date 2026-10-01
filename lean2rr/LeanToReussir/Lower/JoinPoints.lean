import LeanToReussir.Lower.Values

/-! # Join-point strategy -/

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

/-- Choose a strategy for every join point of a declaration body: the set
of outlined (J3) join points; others are J1 (single jump), J2, or
duplicated at their jumps (J1′, those `duplicate` selects: the lowering hook
`LowerHooks.duplicateJp`). -/
partial def chooseOutlined (duplicate : FunDecl .pure → Bool) (body : Code .pure) : FVarIdSet := Id.run do
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
      let ok := single || duplicate d ||
        (endsInJumps k (({} : FVarIdSet).insert d.fvarId) outlined && !jumpedFromOutlined)
      if !ok then
        outlined := outlined.insert d.fvarId
        changed := true
  return outlined

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

/-- Whether `x` is used in `c` or by a join point that `c` jumps to (`jps`:
the bodies of the join points declared outside `c`). -/
partial def usesVar (jps : Std.HashMap FVarId (Code .pure)) (x : FVarId) (c : Code .pure) : Bool :=
  go {} c
where
  go (seen : FVarIdSet) (c : Code .pure) : Bool :=
    if hasFVar x c then true else jumpsUsing seen c
  jumpsUsing (seen : FVarIdSet) (c : Code .pure) : Bool :=
    match c with
    | .let _ k => jumpsUsing seen k
    | .fun d k _ | .jp d k => jumpsUsing seen d.value || jumpsUsing seen k
    | .jmp j _ =>
      match jps[j]? with
      | some b => !seen.contains j && go (seen.insert j) b
      | none => false
    | .cases cs => cs.alts.any (jumpsUsing seen ·.getCode)
    | .return _ | .unreach _ => false

/-- Whether `x` is a field of a constructor application in `c` (or in a join
point that `c` jumps to). -/
partial def usedAsField (env : Environment) (jps : Std.HashMap FVarId (Code .pure)) (x : FVarId)
    (c : Code .pure) : Bool :=
  go {} c
where
  go (seen : FVarIdSet) (c : Code .pure) : Bool :=
    match c with
    | .let d k =>
      (match d.value with
       | .const f _ args _ =>
         env.isConstructor f && args.any fun a => match a with | .fvar y => y == x | _ => false
       | _ => false) || go seen k
    | .fun d k _ | .jp d k => go seen d.value || go seen k
    | .jmp j _ =>
      match jps[j]? with
      | some b => !seen.contains j && go (seen.insert j) b
      | none => false
    | .cases cs => cs.alts.any (go seen ·.getCode)
    | .return _ | .unreach _ => false

/-- Whether `c` returns `x` itself, or passes it to a join point (which may
return it), following jumps to the join points in scope (`jps`). -/
partial def returnedWhole (jps : Std.HashMap FVarId (Code .pure)) (x : FVarId) (c : Code .pure) : Bool :=
  go {} c
where
  go (seen : FVarIdSet) (c : Code .pure) : Bool :=
    match c with
    | .let _ k => go seen k
    | .fun d k _ | .jp d k => go seen d.value || go seen k
    | .jmp j args =>
      args.any (fun | .fvar y => y == x | _ => false) ||
        match jps[j]? with
        | some b => !seen.contains j && go (seen.insert j) b
        | none => false
    | .cases cs => cs.alts.any (go seen ·.getCode)
    | .return y => y == x
    | .unreach _ => false

/-- One pass over `c` for a matched value `x`: whether `c` uses `x` (as
`usesVar`, with `jps` the bodies of the join points declared outside `c`),
and the variables used in `c` outside the alternatives (of `cases` in `c`)
that do not use `x`. The latter are the fields of `x` that must be bound
before `c` when `x` stays live in `c`. Uses in local functions and join
points count (conservatively). A `cases` with one alternative (a structure)
is no branch: its code counts as the rest of `c`, since it is lowered
without `lowerAlt`. The state caches whether a join point's body uses `x`. -/
partial def liveScan (jps : Std.HashMap FVarId (Code .pure)) (x : FVarId) (c : Code .pure) :
    StateM (Std.HashMap FVarId Bool) (Bool × Std.HashSet FVarId) := do
  let inArg : Arg .pure → Bool := fun | .fvar y => y == x | _ => false
  let argUses (as : Array (Arg .pure)) : Std.HashSet FVarId :=
    as.foldl (fun acc a => match a with | .fvar y => acc.insert y | _ => acc) {}
  match c with
  | .let d k =>
    let (m, e) ← liveScan jps x k
    let here := match d.value with
      | .fvar f args => f == x || args.any inArg
      | .const _ _ args _ => args.any inArg
      | .proj _ _ y _ => y == x
      | _ => false
    return (m || here, valueUses d.value e)
  | .fun d k _ =>
    let (m, e) ← liveScan jps x k
    return (m || hasFVar x d.value, codeUses d.value e)
  | .jp d k =>
    let (mj, _) ← liveScan jps x d.value
    modify (·.insert d.fvarId mj)
    let (m, e) ← liveScan jps x k
    return (m || mj, codeUses d.value e)
  | .jmp j as =>
    let f ← match (← get)[j]? with
      | some b => pure b
      | none =>
        let b := match jps[j]? with
          | some body => usesVar jps x body
          | none => false
        modify (·.insert j b)
        pure b
    return (as.any inArg || f, argUses as)
  | .cases cs =>
    let mut m := cs.discr == x
    let mut e : Std.HashSet FVarId := ({} : Std.HashSet FVarId).insert cs.discr
    for alt in cs.alts do
      let (ma, ea) ← liveScan jps x alt.getCode
      m := m || ma
      -- Merge the smaller set into the larger (deep chains stay linear).
      if cs.alts.size == 1 || ma then
        e := if ea.size ≥ e.size then e.fold (·.insert ·) ea else ea.fold (·.insert ·) e
    return (m, e)
  | .return y => return (y == x, ({} : Std.HashSet FVarId).insert y)
  | .unreach _ => return (false, {})

/-- The fields to bind before `c` when `x` stays live in `c` (see
`liveScan`), added to `acc`. -/
def usesWhileLive (jps : Std.HashMap FVarId (Code .pure)) (x : FVarId) (c : Code .pure)
    (acc : Std.HashSet FVarId) : Std.HashSet FVarId :=
  ((liveScan jps x c).run' {}).2.fold (·.insert ·) acc

end LeanToReussir
