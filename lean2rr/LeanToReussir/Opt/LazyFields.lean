import Lean
import LeanToReussir.PassConfig

/-!
# Fields of a live matched value bound where used (optimization `lazy-fields`)

Reussir projects a match's fields at the match. When the matched value stays
live in the alternative, because it is stored whole in a new constructor or
returned whole (`simp` turns `t@(node l k r)` rebuilt into `t`: a BST insert
of a key already present), each field projected there is an extra reference
(inc and dec), and its release looks like a reusable cell to Reussir's
token reuse, which prefers it to the cell actually freed and then never
reuses anything (Reussir bug 7: TreeMap's `balance` rebuilt every node of
the path; a BST insert with `Nat` keys, whose comparison is a call before
the branch, every node).

So such an alternative binds at the match only the fields needed while the
value is live (`usesWhileLive`); a field used only in inner alternatives
that do not use the value is bound there, by matching the value again
(structures: by projecting it) in `lazyLowerAlt`. Values only passed to
calls are not treated so: there reusing the cell (merge's `go l₁ ys (y ::
acc)`) measured slower for mergesort, whose lists then keep the scattered
order of the input cells. The pending fields are recorded in the context
(`CodeCtx.lazy`, `LazyMatch`).

Without this pass every field is bound at the match.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-! ## Liveness of a matched value -/

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

/-! ## The hooks -/

/-- The binding of a structure alternative's fields: when the structure is a
shared value that stays live because it is stored or returned whole, only
the fields used while it is live are projected here; the others are
projected in the inner alternatives that use them (`lazyLowerAlt`), as for
the constructors of an enum (`lazyEnumFields`). -/
def lazyStructFields (ctx : CodeCtx) (arm : CasesArm) : LowerM (ArmLets × CodeCtx) := do
  let k := arm.code
  let lazyOk := arm.shared &&
    (usedAsField (← getEnv) ctx.jpBodies arm.discr k || returnedWhole ctx.jpBodies arm.discr k)
  if !lazyOk then return ← bindStructFields ctx arm
  let mut ctx' := ctx
  let mut lets := #[]
  let early := usesWhileLive ctx.jpBodies arm.discr k {}
  let used := codeUses k {}
  let mut pending := #[]
  for h : i in [:arm.params.size] do
    let p := arm.params[i]
    match arm.layout.fields[i]? with
    | some (some (j, ft)) =>
      if !early.contains p.fvarId then
        if used.contains p.fvarId then pending := pending.push (p.fvarId, j, ft)
      else
        let x ← fresh "f"
        lets := lets.push (x, some ft, RR.Expr.field (.var arm.scrut) j)
        ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, ft) }
    | _ => ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId ("L2RUnit::u{}", .unit) }
  if !pending.isEmpty then
    let l : LazyMatch := { discr := arm.discr, scrut := arm.scrut, ty := arm.ty, variant := arm.layout.variant,
                           nbinders := 0, fields := pending, pending, struct := true }
    ctx' := { ctx' with lazy := ctx'.lazy.push l }
  return (lets, ctx')

/-- The fields of an enum alternative in which the matched value stays live
because it is stored or returned whole: only the fields needed while it is
live stay bound by the match; the others are unbound, and recorded to be
bound by matching the value again where they are used (`lazyLowerAlt`). -/
def lazyEnumFields (ctx : CodeCtx) (arm : CasesArm) (binders : Array (Option String)) :
    LowerM (Array (Option String) × CodeCtx) := do
  let k := arm.code
  unless !binders.isEmpty && arm.shared &&
      (usedAsField (← getEnv) ctx.jpBodies arm.discr k || returnedWhole ctx.jpBodies arm.discr k) do
    return (binders, ctx)
  let mut binders := binders
  let mut ctx' := ctx
  let early := usesWhileLive ctx.jpBodies arm.discr k {}
  let used := codeUses k {}
  let mut fields := #[]
  let mut pending := #[]
  for h : i in [:arm.params.size] do
    let p := arm.params[i]
    if let some (some (j, ft)) := arm.layout.fields[i]? then
      if used.contains p.fvarId then fields := fields.push (p.fvarId, j, ft)
      if !early.contains p.fvarId then
        binders := binders.set! j none
        ctx' := { ctx' with vars := ctx'.vars.erase p.fvarId }
        if used.contains p.fvarId then pending := pending.push (p.fvarId, j, ft)
  if !fields.isEmpty then
    let l : LazyMatch :=
      { discr := arm.discr, scrut := arm.scrut, ty := arm.ty, variant := arm.layout.variant,
        nbinders := binders.size, fields, pending }
    ctx' := { ctx' with lazy := ctx'.lazy.push l }
  return (binders, ctx')

/-- Lower the code `k` of an alternative (`self`: this function; `code`:
`lowerCode`). A lazily matched value whose fields the alternative uses is
matched again first. When the alternative does not use the value itself,
the value dies here: this match consumes it and binds every field the
alternative uses (also those bound before, which are then only borrowed).
Otherwise it binds the pending fields needed while the value is live. -/
def lazyLowerAlt (self code : CodeCtx → Code .pure → LowerM RR.Block) (ctx : CodeCtx) (retTy : RR.Ty)
    (k : Code .pure) : LowerM RR.Block := do
  if ctx.lazy.isEmpty then return ← code ctx k
  let used := codeUses k {}
  for h : i in [:ctx.lazy.size] do
    let l := ctx.lazy[i]
    let live := usesVar ctx.jpBodies l.discr k
    if l.struct then
      -- A structure: project the pending fields this code uses (while
      -- the structure is live, only those needed before it dies).
      let need := l.pending.filter (used.contains ·.1)
      let now := if live && !need.isEmpty then
          let early := usesWhileLive ctx.jpBodies l.discr k {}
          need.filter (early.contains ·.1)
        else need
      if now.isEmpty then continue
      let scrut := match ctx.vars[l.discr]? with
        | some (n, _) => n
        | none => l.scrut
      let mut lets := #[]
      let mut ctx' := ctx
      for (p, j, ft) in now do
        let x ← fresh "f"
        lets := lets.push (x, some ft, RR.Expr.field (.var scrut) j)
        ctx' := { ctx' with vars := ctx'.vars.insert p (x, ft) }
      let rest := l.pending.filter fun q => !now.any (·.1 == q.1)
      ctx' := { ctx' with lazy :=
        if rest.isEmpty then ctx'.lazy.eraseIdx! i else ctx'.lazy.set! i { l with pending := rest } }
      let body ← self ctx' k
      return { body with lets := lets ++ body.lets }
    let now := if live then
        let need := l.pending.filter (used.contains ·.1)
        if need.isEmpty then need else
          let early := usesWhileLive ctx.jpBodies l.discr k {}
          need.filter (early.contains ·.1)
      else l.fields.filter (used.contains ·.1)
    if now.isEmpty then continue
    -- The value's current name: the match of an enclosing lazy value may
    -- have bound it again (it is a field of that value).
    let scrut := match ctx.vars[l.discr]? with
      | some (n, _) => n
      | none => l.scrut
    let mut binders := Array.replicate l.nbinders (none : Option String)
    let mut ctx' := ctx
    for (p, j, ft) in now do
      let x ← fresh "f"
      binders := binders.set! j (some x)
      ctx' := { ctx' with vars := ctx'.vars.insert p (x, ft) }
    let rest := l.pending.filter fun q => !now.any (·.1 == q.1)
    ctx' := { ctx' with lazy :=
      if live then ctx'.lazy.set! i { l with pending := rest } else ctx'.lazy.eraseIdx! i }
    let body ← self ctx' k
    return .ofExpr (.mtch (.var scrut) #[
      { ty := l.ty, ctor := some l.variant, binders, body },
      { ty := l.ty, ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[retTy] #[]) }])
  code ctx k

/-- Registry entry point. -/
def Opt.LazyFields.install (c : PassConfig) : PassConfig :=
  { c with lower := { c.lower with
      structFields := lazyStructFields, enumFields := lazyEnumFields, lowerAlt := lazyLowerAlt } }

end LeanToReussir
