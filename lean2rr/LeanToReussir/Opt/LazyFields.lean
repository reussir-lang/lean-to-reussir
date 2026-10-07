import Lean
import LeanToReussir.PassConfig

/-!
# Fields of a live matched value bound where used (optimization `lazy-fields`)

Reussir projects a match's fields at the match. When the matched value stays
live in the alternative, because it is stored whole in a new constructor,
returned whole (`simp` turns `t@(node l k r)` rebuilt into `t`: a BST insert
of a key already present) or passed whole to a call (merge's `go l₁ ys (y ::
acc)`, where `y :: ys` is the matched value), each field projected there is
an extra reference (inc and dec), and its release looks like a reusable cell
to Reussir's token reuse, which prefers it to the cell actually freed and
then never reuses anything (Reussir issue 7, a missed optimization: TreeMap's
`balance` rebuilt every node of the path; a BST insert with `Nat` keys, whose
comparison is a call before the branch, every node; `List.mergeSort`'s merge
allocated a cell at every step and freed the matched one).

So such an alternative binds at the match only the fields needed while the
value is live (`usesWhileLive`); a field used only in inner alternatives
that do not use the value is bound there, by matching the value again
(structures: by projecting it) in `lazyLowerAlt`. A merge then reuses the
cell it takes apart, as native Lean does, and its result keeps the input's
cells. Allocating instead made the result's memory order depend on the
allocator: when mimalloc has few free cells of the size, it hands back cells
freed across the whole heap, and walking the result costs a cache miss per
cell (a sort and every later walk 5-9x native, at list lengths depending on
the length modulo a page's capacity). The pending fields are this pass's
state in the context (`LazyFieldsState` in `CodeCtx.ext`).

Without this pass every field is bound at the match.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-! ## Liveness of a matched value -/

/-- Results of an analysis per join point (whether its body, following its
own jumps, has the property), so that each join point's body is walked
once per analysis: a chain of join points whose bodies each jump twice to
the next outer one would otherwise be walked once per path, exponentially
often. -/
abbrev JpMemo := Std.HashMap FVarId Bool

/-- `usesVar` with the memo of the join points' results. -/
partial def usesVarM (jps : Std.HashMap FVarId (Code .pure)) (x : FVarId) (c : Code .pure) :
    StateM JpMemo Bool :=
  go c
where
  go (c : Code .pure) : StateM JpMemo Bool := do
    if hasFVar x c then return true
    jumpsUsing c
  jumpsUsing (c : Code .pure) : StateM JpMemo Bool := do
    match c with
    | .let _ k => jumpsUsing k
    | .fun d k _ | .jp d k => if ← jumpsUsing d.value then return true else jumpsUsing k
    | .jmp j _ =>
      match jps[j]? with
      | some b =>
        if let some r := (← get)[j]? then return r
        let r ← go b
        modify (·.insert j r)
        return r
      | none => return false
    | .cases cs => cs.alts.anyM (jumpsUsing ·.getCode)
    | .return _ | .unreach _ => return false

/-- Whether `x` is used in `c` or by a join point that `c` jumps to (`jps`:
the bodies of the join points declared outside `c`). -/
def usesVar (jps : Std.HashMap FVarId (Code .pure)) (x : FVarId) (c : Code .pure) : Bool :=
  (usesVarM jps x c).run' {}

/-- Whether `x` is an argument of an application in `c` (or in a join point
that `c` jumps to): a field of a constructor application, or an argument of
a call (merge's `go l₁ ys (y :: acc)`, where `y :: ys` is the matched
value). -/
partial def usedAsArg (jps : Std.HashMap FVarId (Code .pure)) (x : FVarId)
    (c : Code .pure) : Bool :=
  (go c).run' {}
where
  go (c : Code .pure) : StateM JpMemo Bool := do
    match c with
    | .let d k =>
      let isX : Arg .pure → Bool := fun a => match a with | .fvar y => y == x | _ => false
      let here := match d.value with
        | .const _ _ args _ => args.any isX
        | .fvar _ args => args.any isX
        | _ => false
      if here then return true else go k
    | .fun d k _ | .jp d k => if ← go d.value then return true else go k
    | .jmp j _ =>
      match jps[j]? with
      | some b =>
        if let some r := (← get)[j]? then return r
        let r ← go b
        modify (·.insert j r)
        return r
      | none => return false
    | .cases cs => cs.alts.anyM (go ·.getCode)
    | .return _ | .unreach _ => return false

/-- Whether `c` returns `x` itself, or passes it to a join point (which may
return it), following jumps to the join points in scope (`jps`). -/
partial def returnedWhole (jps : Std.HashMap FVarId (Code .pure)) (x : FVarId) (c : Code .pure) : Bool :=
  (go c).run' {}
where
  go (c : Code .pure) : StateM JpMemo Bool := do
    match c with
    | .let _ k => go k
    | .fun d k _ | .jp d k => if ← go d.value then return true else go k
    | .jmp j args =>
      if args.any (fun | .fvar y => y == x | _ => false) then return true
      match jps[j]? with
      | some b =>
        if let some r := (← get)[j]? then return r
        let r ← go b
        modify (·.insert j r)
        return r
      | none => return false
    | .cases cs => cs.alts.anyM (go ·.getCode)
    | .return y => return y == x
    | .unreach _ => return false

/-- One pass over `c` for a matched value `x`: whether `c` uses `x` (as
`usesVar`, with `jps` the bodies of the join points declared outside `c`),
and the variables used in `c` outside the alternatives (of `cases` in `c`)
that do not use `x`. The latter are the fields of `x` that must be bound
before `c` when `x` stays live in `c`. Uses in local functions and join
points count (conservatively). A `cases` with one alternative (a structure)
is no branch: its code counts as the rest of `c`, since it is lowered
without `lowerAlt`. The state caches whether a join point's body uses `x`
(shared with `usesVarM`). -/
partial def liveScan (jps : Std.HashMap FVarId (Code .pure)) (x : FVarId) (c : Code .pure) :
    StateM JpMemo (Bool × Std.HashSet FVarId) := do
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
        let b ← match jps[j]? with
          | some body => usesVarM jps x body
          | none => pure false
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

/-! ## The pass's state -/

/-- A matched value that stays live in its arm, whose fields are bound where
they are used. `fields` are the arm's field parameters that the arm uses,
with their binder index, their type in the record and the parameter's own
type (`bindField`); `pending` those not bound yet. -/
structure LazyMatch where
  discr : FVarId
  scrut : String
  ty : String
  variant : String
  nbinders : Nat
  fields : Array (FVarId × Nat × RR.Ty × RR.Ty)
  pending : Array (FVarId × Nat × RR.Ty × RR.Ty)
  /-- A structure: its pending fields are projected where they are used
  (Reussir has no structure patterns). -/
  struct : Bool := false

/-- The pass's state in the code-lowering context (`CodeCtx.ext`): the
matched values whose fields are bound lazily, outermost first. -/
structure LazyFieldsState where
  values : Array LazyMatch := #[]

deriving instance TypeName for LazyFieldsState

/-- The key of the pass's state in the context. -/
def lazyFieldsKey : Name := `lazyFields

/-- The lazily matched values of the context. -/
def CodeCtx.lazyMatches (ctx : CodeCtx) : Array LazyMatch :=
  ((ctx.getExt? LazyFieldsState lazyFieldsKey).map (·.values)).getD #[]

/-- The context with lazily matched values `ms`. -/
def CodeCtx.withLazyMatches (ctx : CodeCtx) (ms : Array LazyMatch) : CodeCtx :=
  ctx.setExt lazyFieldsKey ({ values := ms } : LazyFieldsState)

/-! ## The hooks -/

/-- The binding of a structure alternative's fields: when the structure is a
shared value that stays live because it is stored, returned or passed whole,
only the fields used while it is live are projected here; the others are
projected in the inner alternatives that use them (`lazyLowerAlt`), as for
the constructors of an enum (`lazyEnumFields`). -/
def lazyStructFields (prev : CodeCtx → CasesArm → LowerM (ArmLets × CodeCtx)) (ctx : CodeCtx) (arm : CasesArm) :
    LowerM (ArmLets × CodeCtx) := do
  let k := arm.code
  let lazyOk := arm.shared &&
    (usedAsArg ctx.jpBodies arm.discr k || returnedWhole ctx.jpBodies arm.discr k)
  if !lazyOk then return ← prev ctx arm
  let mut ctx' := ctx
  let mut lets := #[]
  let early := usesWhileLive ctx.jpBodies arm.discr k {}
  let used := codeUses k {}
  let mut pending := #[]
  for h : i in [:arm.params.size] do
    let p := arm.params[i]
    match arm.layout.fields[i]? with
    | some (some (j, ft)) =>
      let pt ← lowerType p.type
      if !early.contains p.fvarId then
        if used.contains p.fvarId then pending := pending.push (p.fvarId, j, ft, pt)
      else
        let x ← fresh "f"
        lets := lets.push (x, some ft, RR.Expr.field (.var arm.scrut) j)
        let (conv, c) ← bindField ctx' p.fvarId pt x ft
        lets := lets ++ conv
        ctx' := c
    | _ => ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId ("L2RUnit::u{}", .unit) }
  if !pending.isEmpty then
    let l : LazyMatch := { discr := arm.discr, scrut := arm.scrut, ty := arm.ty, variant := arm.layout.variant,
                           nbinders := 0, fields := pending, pending, struct := true }
    ctx' := ctx'.withLazyMatches (ctx'.lazyMatches.push l)
  return (lets, ctx')

/-- The fields of an enum alternative in which the matched value stays live
because it is stored, returned or passed whole: only the fields needed
while it is live stay bound by the match; the others are unbound, and
recorded to be bound by matching the value again where they are used
(`lazyLowerAlt`). -/
def lazyEnumFields (prev : CodeCtx → CasesArm → Array (Option String) → LowerM (Array (Option String) × CodeCtx))
    (ctx : CodeCtx) (arm : CasesArm) (binders : Array (Option String)) :
    LowerM (Array (Option String) × CodeCtx) := do
  let (binders, ctx) ← prev ctx arm binders
  let k := arm.code
  unless !binders.isEmpty && arm.shared &&
      (usedAsArg ctx.jpBodies arm.discr k || returnedWhole ctx.jpBodies arm.discr k) do
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
      let pt ← lowerType p.type
      if used.contains p.fvarId then fields := fields.push (p.fvarId, j, ft, pt)
      if !early.contains p.fvarId then
        binders := binders.set! j none
        ctx' := { ctx' with vars := ctx'.vars.erase p.fvarId }
        if used.contains p.fvarId then pending := pending.push (p.fvarId, j, ft, pt)
  if !fields.isEmpty then
    let l : LazyMatch :=
      { discr := arm.discr, scrut := arm.scrut, ty := arm.ty, variant := arm.layout.variant,
        nbinders := binders.size, fields, pending }
    ctx' := ctx'.withLazyMatches (ctx'.lazyMatches.push l)
  return (binders, ctx')

/-- Lower the code `k` of an alternative (`self`: this function; `code`:
`lowerCode`). A lazily matched value whose fields the alternative uses is
matched again first. When the alternative does not use the value itself,
the value dies here: this match consumes it and binds every field the
alternative uses (also those bound before, which are then only borrowed),
except a field bound before and converted to its parameter's own type,
which keeps that conversion (no second unboxing). Otherwise it binds the
pending fields needed while the value is live. Conversions the code does
not use are dropped (`dropUnusedConvs`). -/
def lazyLowerAlt (prev : (self code : CodeCtx → Code .pure → LowerM RR.Block) → CodeCtx → RR.Ty → Code .pure →
      LowerM RR.Block)
    (self code : CodeCtx → Code .pure → LowerM RR.Block) (ctx : CodeCtx) (retTy : RR.Ty)
    (k : Code .pure) : LowerM RR.Block := do
  let lazy := ctx.lazyMatches
  if lazy.isEmpty then return ← prev self code ctx retTy k
  -- Code uses of the fields, except of variables another hook bound again
  -- here (`CodeCtx.pinned`), which keep that binding.
  let used := (codeUses k {}).filter (!ctx.pinned.contains ·)
  for h : i in [:lazy.size] do
    let l := lazy[i]
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
      for (p, j, ft, pt) in now do
        let x ← fresh "f"
        lets := lets.push (x, some ft, RR.Expr.field (.var scrut) j)
        let (conv, c) ← bindField ctx' p pt x ft
        lets := lets ++ conv
        ctx' := c
      let rest := l.pending.filter fun q => !now.any (·.1 == q.1)
      let convs := fieldConvNames ctx' (now.map (·.1))
      ctx' := ctx'.withLazyMatches (if rest.isEmpty then lazy.eraseIdx! i else lazy.set! i { l with pending := rest })
      let body ← self ctx' k
      return { body with lets := dropUnusedConvs lets convs body ++ body.lets }
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
    let mut conv := #[]
    for (p, j, ft, pt) in now do
      -- A field bound before (while the value was live) and converted to
      -- its own type keeps that conversion: the match drops the field.
      if let some y := ctx'.fieldConv[p]? then
        if ctx'.vars[p]? == some (y, pt) then continue
      let x ← fresh "f"
      binders := binders.set! j (some x)
      let (c, ctx2) ← bindField ctx' p pt x ft
      conv := conv ++ c
      ctx' := ctx2
    let rest := l.pending.filter fun q => !now.any (·.1 == q.1)
    ctx' := ctx'.withLazyMatches (if live then lazy.set! i { l with pending := rest } else lazy.eraseIdx! i)
    let body ← self ctx' k
    conv := dropUnusedConvs conv (conv.foldl (fun s (y, _, _) => s.insert y) {}) body
    return .ofExpr (.mtch (.var scrut) #[
      { ty := l.ty, ctor := some l.variant, binders, body := { body with lets := conv ++ body.lets } },
      { ty := l.ty, ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[retTy] #[]) }])
  prev self code ctx retTy k

/-- Registry entry point: each hook handles the arms this pass binds lazily
and leaves the others to the hooks installed before it. -/
def Opt.LazyFields.install (c : PassConfig) : PassConfig :=
  { c with lower := { c.lower with
      structFields := lazyStructFields c.lower.structFields
      enumFields := lazyEnumFields c.lower.enumFields
      lowerAlt := lazyLowerAlt c.lower.lowerAlt } }

end LeanToReussir
