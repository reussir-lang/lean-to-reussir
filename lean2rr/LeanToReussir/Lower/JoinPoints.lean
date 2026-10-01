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

/-- Does `c` jump to `j`? -/
partial def hasJumpTo (j : FVarId) : Code .pure → Bool
  | .jmp j' _ => j == j'
  | .let _ k => hasJumpTo j k
  | .fun d k _ | .jp d k => hasJumpTo j d.value || hasJumpTo j k
  | .cases c => c.alts.any (hasJumpTo j ·.getCode)
  | _ => false

/-- Place join point `d` (whose scope is `k`) as deep as possible: into the
single branch, join-point body or continuation containing all its jumps.
Free variables of `d` stay in scope (binders are unique), and code does not
grow. Sunk into the subtree its jumps come from, a join point is more often
structured (J2) instead of outlined: an outlined join point that calls the
enclosing function back makes a loop mutually recursive, which LLVM does not
turn into a loop. -/
partial def sinkInto (d : FunDecl .pure) (k : Code .pure) : Code .pure :=
  let j := d.fvarId
  match k with
  | .let x k' => .let x (sinkInto d k')
  | .fun f k' _ => if hasJumpTo j f.value then .jp d k else .fun f (sinkInto d k')
  | .jp d2 k2 =>
    match hasJumpTo j d2.value, hasJumpTo j k2 with
    | true, true => .jp d k
    | true, false => .jp (FunDecl.mk d2.fvarId d2.binderName d2.params d2.type (sinkInto d d2.value)) k2
    | false, true => .jp d2 (sinkInto d k2)
    | false, false => k
  | .cases c =>
    if (c.alts.filter (hasJumpTo j ·.getCode)).size == 1 then
      .cases ⟨c.typeName, c.resultType, c.discr, c.alts.map fun alt =>
        if hasJumpTo j alt.getCode then
          match alt with
          | .alt ctor ps code _ => .alt ctor ps (sinkInto d code)
          | .default code => .default (sinkInto d code)
          | other => other
        else alt⟩
    else .jp d k
  | _ => .jp d k

/-- Sink every join point of `c` (innermost first). -/
partial def sinkJoinPoints : Code .pure → Code .pure
  | .let x k => .let x (sinkJoinPoints k)
  | .fun d k _ =>
    .fun (FunDecl.mk d.fvarId d.binderName d.params d.type (sinkJoinPoints d.value)) (sinkJoinPoints k)
  | .jp d k =>
    sinkInto (FunDecl.mk d.fvarId d.binderName d.params d.type (sinkJoinPoints d.value)) (sinkJoinPoints k)
  | .cases c =>
    .cases ⟨c.typeName, c.resultType, c.discr, c.alts.map fun
      | .alt ctor ps code _ => .alt ctor ps (sinkJoinPoints code)
      | .default code => .default (sinkJoinPoints code)
      | other => other⟩
  | c => c

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

/-- Size of a code block (bindings, alternatives and exits), counted up to
`cap`. -/
partial def codeSize (c : Code .pure) (cap : Nat) : Nat :=
  go c 0
where
  go (c : Code .pure) (acc : Nat) : Nat :=
    if acc ≥ cap then acc else
    match c with
    | .let _ k => go k (acc + 1)
    | .fun d k _ | .jp d k => go k (go d.value (acc + 1))
    | .cases cs => cs.alts.foldl (fun acc alt => go alt.getCode (acc + 1)) (acc + 1)
    | _ => acc + 1

/-- Small join points (nested join points included, since sinking nests
them) are duplicated at their jumps (like J1) rather than
outlined: outlining one on a loop's path makes the loop a state machine
(J4) or mutually recursive (J3), and keeps the reuse of cells matched
before the jump from reaching constructions after it. -/
def isSmallJp (d : FunDecl .pure) : Bool := codeSize d.value 41 ≤ 40

/-- Choose a strategy for every join point of a declaration body: the set
of outlined (J3) join points; others are J1 (single jump) or J2. -/
partial def chooseOutlined (body : Code .pure) : FVarIdSet := Id.run do
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
      let ok := single || isSmallJp d ||
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
