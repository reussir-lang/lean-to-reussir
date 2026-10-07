import LeanToReussir.Lower.Hooks

/-! # Code -/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Free variable names of an RR expression/block (for outlined join points). -/
partial def rrFreeVars (e : RR.Expr) (bound : Std.HashSet String) (acc : Std.HashSet String) : Std.HashSet String :=
  match e with
  | .var n => if bound.contains n || n.startsWith "L2RUnit" then acc else acc.insert n
  | .atom _ => acc
  | .call _ _ args => args.foldl (fun acc a => rrFreeVars a bound acc) acc
  | .apply f a => rrFreeVars a bound (rrFreeVars f bound acc)
  | .ctor _ _ args => args.foldl (fun acc a => rrFreeVars a bound acc) acc
  | .field e _ => rrFreeVars e bound acc
  | .cast e _ => rrFreeVars e bound acc
  | .lam x _ b => blockFreeVars b (bound.insert x) acc
  | .ite c t f => blockFreeVars f bound (blockFreeVars t bound (rrFreeVars c bound acc))
  | .mtch s arms => arms.foldl (fun acc arm =>
      let bound := arm.binders.foldl (fun b x => match x with | some x => b.insert x | none => b) bound
      blockFreeVars arm.body bound acc) (rrFreeVars s bound acc)
  | .block b => blockFreeVars b bound acc
where
  blockFreeVars (b : RR.Block) (bound : Std.HashSet String) (acc : Std.HashSet String) : Std.HashSet String :=
    let (bound, acc) := b.lets.foldl (fun (bound, acc) (x, _, e) => (bound.insert x, rrFreeVars e bound acc)) (bound, acc)
    rrFreeVars b.result bound acc

/-- The names of the conversions `bindField` made for field parameters
`ps` (`CodeCtx.fieldConv`), in context `ctx` right after the binding. -/
def fieldConvNames (ctx : CodeCtx) (ps : Array FVarId) : Std.HashSet String :=
  ps.foldl (fun acc p => match ctx.fieldConv[p]? with
    | some y => acc.insert y
    | none => acc) {}

/-- The `lets` that bind an alternative's fields (projections, and the
conversions `bindField` made: the names `convs`), without the conversions
that the alternative's code `body` does not use. Every site that binds
fields filters them so: enum and structure alternatives (`lowerCases`) and
Opt/LazyFields' later bindings. -/
def dropUnusedConvs (lets : ArmLets) (convs : Std.HashSet String) (body : RR.Block) : ArmLets :=
  if !lets.any (convs.contains ·.1) then lets else
  let free := rrFreeVars.blockFreeVars body {} {}
  lets.filter fun (y, _, _) => !convs.contains y || free.contains y

/-- The number of constructors from which the release of an inductive's
value is wide: rrc expands every release of an enum in line into a match
over its variants. -/
def wideReleaseCtors : Nat := 8

/-- Whether rrc's release of a value of type `t` is wide: `t` is an
inductive with constructors that hold fields, at least `wideReleaseCtors` of
them. -/
def hasWideRelease (t : RR.Ty) : LowerM Bool := do
  let .named n := t | return false
  let some info := (← get).typeInfos[n]? | return false
  return info.shape == .enum && info.ctorOrder.size ≥ wideReleaseCtors

/-- The wildcard arm of a `match` that covers two or more constructors
releases out of line (`let us = l2r_sink<T>(v);`, `l2r_sink` in the
prelude, kept out of rrc's inliner) the values of wide release
(`hasWideRelease`) that the other arms use and it does not.

Why: rrc copies a wildcard arm into every constructor it covers, and in
each copy releases the values the other arms use, each in line, a match
over the variants of its type. A derived `BEq`, `DecidableEq` or `Ord` on
an inductive with N constructors matches `y` inside each of the N arms of a
match on `x`, with an unreachable wildcard (the constructor indices were
compared first), while the fields of `x` are held; a hand-written
two-scrutinee equality has the same shape with a `_, _ => false` arm. That
is N arms, N - 1 copies each, an N-variant release of each held field of
the inductive's type in every copy: N^3 code, over which rrc's SCCP then
takes superlinear time (40 constructors: a 9-minute build, round-6 finding
PRG6-02). Out of line, a copy makes one call per such value. The value is
released at the arm's entry as before, only by the call; the other arms are
unchanged (they use the value as before), and so is the scrutinee, whose
release in a copy knows its constructor and is small. -/
def sinkWildcardHeld (ctx : CodeCtx) (scrut : String) (nCtors : Nat) (arms : Array RR.Arm) :
    LowerM (Array RR.Arm) := do
  let some w := arms.findIdx? (·.ctor.isNone) | return arms
  let some wild := arms[w]? | return arms
  -- Constructors the wildcard covers: rrc's copies of it.
  if nCtors - (arms.size - 1) < 2 then return arms
  let varTys : Std.HashMap String RR.Ty := ctx.vars.fold (fun m _ (n, t) => m.insert n t) {}
  let freeIn (a : RR.Arm) (acc : Std.HashSet String) : Std.HashSet String :=
    rrFreeVars.blockFreeVars a.body (a.binders.foldl (fun b x => match x with | some x => b.insert x | none => b) {}) acc
  let own := freeIn wild {}
  let mut used : Std.HashSet String := {}
  for h : j in [:arms.size] do
    if j != w then used := freeIn arms[j] used
  let mut sinks := #[]
  for n in used.toArray.qsort (· < ·) do
    if n == scrut || own.contains n then continue
    let some t := varTys[n]? | continue
    unless ← hasWideRelease t do continue
    sinks := sinks.push (← fresh "us", some (RR.Ty.named "u64"), RR.Expr.call "l2r_sink" #[t] #[.var n])
  if sinks.isEmpty then return arms
  return arms.set! w { wild with body := { wild.body with lets := sinks ++ wild.body.lets } }

/-- Whether constant `f`'s value is a literal that a box holds as an
immediate: its code returns a `UInt8`/`UInt16`/`UInt32` literal or a
`UInt64`/`USize` literal below 2^63, possibly through other such constants
(up to `fuel` deep). -/
partial def constIsImmediate (f : Name) (fuel : Nat := 8) : LowerM Bool := do
  let some { params := #[], value := .code body, .. } := (← read).decls.find? f | return false
  let rec go (c : Code .pure) (vals : Std.HashMap FVarId (LetValue .pure)) : LowerM Bool := do
    match c with
    | .let d k => go k (vals.insert d.fvarId d.value)
    | .return x =>
      match vals[x]? with
      | some (.lit (.uint64 n)) | some (.lit (.usize n)) => return n.toNat < 2 ^ 63
      | some (.lit (.uint8 _)) | some (.lit (.uint16 _)) | some (.lit (.uint32 _)) => return true
      | some (.const g _ #[] _) => return fuel > 0 && (← constIsImmediate g (fuel - 1))
      | _ => return false
    | _ => return false
  go body {}

/-- The value `e` of a `let` with Lean value `v`, if boxing treats it as
native Lean does (`boxOf`, `LowerState.closedLets`): a placeholder (`◾`,
`zeroValue`), a call of a declaration of the program without parameters
(a constant or closed term, cached in a once-cell or recomputed by
`cheap-consts`, which cannot trace or panic), or a `UInt64`/`USize`
literal from 2^63 (smaller ones are immediates). Not a closed term
evaluated where it is used (`uncachedConsts`): calling it again for its
box would run it twice (a trace, a panic). -/
def closedLetValue (v : LetValue .pure) (e : RR.Expr) : LowerM (Option RR.Expr) := do
  match v, e with
  | .erased, .call _ #[] #[] => return some e
  | .const f _ #[] _, .call _ #[] #[] =>
    if (← read).uncachedConsts.contains f then return none
    match (← read).decls.find? f with
    | some { params := #[], value := .code _, .. } =>
      -- A constant whose value is a literal that boxes as an immediate
      -- (`def k : UInt64 := 77`): boxed in line, which LLVM folds, not
      -- read from a once-cell.
      if ← constIsImmediate f then return none
      return some e
    | _ => return none
  | .lit (.uint64 n), .atom _ | .lit (.usize n), .atom _ =>
    return if n.toNat ≥ 2 ^ 63 then some e else none
  | _, _ => return none

section
variable (H : LowerHooks)

mutual
  /-- Lower a code block whose value has Reussir type `retTy`. -/
  partial def lowerCode (ctx : CodeCtx) (outlined : FVarIdSet) (retTy : RR.Ty) (c : Code .pure) :
      LowerM RR.Block := do
    match c with
    | .let .. =>
      -- A run of `let`s is lowered in a loop and prepended once, and each
      -- value is lowered with a map of just the variables it reads (all
      -- that `lowerLetValue` looks up), while the run's own variables
      -- collect in a map of their own, merged once at the end: so a long
      -- straight-line body (a spliced literal) costs linear time, where
      -- growing the context's map would copy it at every `let`.
      let base := { ctx with vars := {} }
      let outer := ctx.vars
      let mut runVars : Std.HashMap FVarId (String × RR.Ty) := {}
      let mut runCalls := ctx.letCalls
      let mut c := c
      let mut lets : Array (String × Option RR.Ty × RR.Expr) := #[]
      repeat
        let .let d k := c | break
        let t ← lowerType d.type
        let used := valueUses d.value {}
        let small := used.fold (init := ({} : Std.HashMap FVarId (String × RR.Ty))) fun m x =>
          match runVars[x]?, outer[x]? with
          | some v, _ | none, some v => m.insert x v
          | none, none => m
        let ctx := { base with vars := small }
        -- J4: a self tail call re-enters the state machine.
        if let some sm := ctx.sm then
          if let .const f _ args _ := d.value then
            if f == sm.self && args.size == sm.arity && t == retTy then
              if let .return x := k then
                if x == d.fvarId then
                  let some selfDecl := (← read).decls.find? f | throwError "lean2rr: no declaration {f}"
                  let (ps, _) := splitFnType selfDecl.type sm.arity
                  -- Rule 4a: the arguments of the parameters it takes.
                  let keep := keepMask (selfDecl.params.map (·.type))
                  let mut vals := #[]
                  for h : i in [:min args.size ps.size] do
                    if keep[i]?.getD true then vals := vals.push (← lowerArg ctx args[i]! (← lowerType ps[i]!))
                  return ⟨lets, ← H.stateMachine.selfCall sm vals⟩
        let e ← try lowerLetValue ctx d.value d.type t
          catch ex => throwError "{ex.toMessageData}\n  in let {d.binderName} : {d.type}"
        let x ← fresh "x"
        lets := lets.push (x, some t, e)
        runVars := runVars.insert d.fvarId (x, t)
        if let some v ← closedLetValue d.value e then
          modify fun s => { s with closedLets := s.closedLets.insert x (v, t) }
        if let .const f _ args _ := d.value then
          if !args.isEmpty then runCalls := runCalls.insert d.fvarId (f, args.size)
        c := k
      let vars := runVars.fold (init := outer) fun m k v => m.insert k v
      let b ← lowerCode { base with vars, letCalls := runCalls } outlined retTy c
      return { b with lets := lets ++ b.lets }
    | .return x =>
      if let some (e, t) := ctx.rebuild[x]? then return .ofExpr (← coerce e t retTy)
      match ctx.vars[x]? with
      | some (n, t) => return .ofExpr (← coerce (.var n) t retTy)
      | none => throwError "lean2rr: return of unbound variable (internal error)"
    | .unreach _ => return .ofExpr (.call "l2r_unreachable" #[retTy] #[])
    | .cases cs => return .ofExpr (← lowerCases ctx outlined retTy cs)
    | .jmp j args =>
      -- The arguments of the parameters the join point takes (rule 4:
      -- not the erased ones), for the jumps that pass arguments.
      let taken : Array (Arg .pure) := match ctx.jpKeep[j]? with
        | some keep => (args.zipIdx.filter fun (_, i) => keep[i]?.getD true).map (·.1)
        | none => args
      match ctx.jumps[j]? with
      | some (.inline params body) =>
        -- J1: bind the parameters to the arguments, then the body.
        let mut ctx' := ctx
        let mut lets := #[]
        for (p, a) in params.zip args do
          let t ← lowerType p.type
          let x ← fresh "j"
          lets := lets.push (x, some t, ← lowerArg ctx a t)
          ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, t) }
        let b ← lowerCode ctx' outlined retTy body
        return { b with lets := lets ++ b.lets }
      | some (.yield tys) =>
        let vals ← (taken.zip tys).mapM fun (a, t) => lowerArg ctx a t
        match vals.size with
        | 0 => return .ofExpr .unitVal
        | 1 => return .ofExpr vals[0]!
        | _ => return .ofExpr (.ctor (← tupleType tys) none vals)
      | some (.call fn captured) =>
        let tys := ctx.jpParams.getD j #[]
        let vals ← (taken.zip tys).mapM fun (a, t) => lowerArg ctx a t
        return .ofExpr (.call fn #[] (captured.map .var ++ vals))
      | some (.enter variant captured) =>
        let some sm := ctx.sm | throwError "lean2rr: state-machine jump outside a state machine"
        let tys := ctx.jpParams.getD j #[]
        let vals ← (taken.zip tys).mapM fun (a, t) => lowerArg ctx a t
        return .ofExpr (← H.stateMachine.jumpCall sm variant (captured.map .var ++ vals))
      | none => throwError "lean2rr: jump to unknown join point (internal error)"
    | .jp d k =>
      -- Rule 4: a join point takes no erased parameter (bound to the unit
      -- value in its body).
      let keepJ := d.params.map fun p => !erasedDom p.type
      let params := (d.params.zip keepJ).filterMap fun (p, b) => if b then some p else none
      let unitVars (m : Std.HashMap FVarId (String × RR.Ty)) : Std.HashMap FVarId (String × RR.Ty) :=
        (d.params.zip keepJ).foldl (init := m) fun m (p, b) => if b then m else m.insert p.fvarId ("L2RUnit::u{}", .unit)
      let ptys ← params.mapM (lowerType ·.type)
      let ctx := { ctx with jpParams := ctx.jpParams.insert d.fvarId ptys,
                            jpKeep := ctx.jpKeep.insert d.fvarId keepJ,
                            jpBodies := ctx.jpBodies.insert d.fvarId d.value }
      if outlined.contains d.fvarId then
        -- J3: outline the body into a function over its free variables.
        let pnames ← params.mapM fun _ => fresh "p"
        let vars := (params.zip (pnames.zip ptys)).foldl (fun m (p, nt) => m.insert p.fvarId nt) (unitVars ctx.vars)
        let bodyCtx := { ctx with vars }
        let body ← lowerCode bodyCtx outlined retTy d.value
        let bound := pnames.foldl (·.insert ·) ({} : Std.HashSet String)
        let free := (rrFreeVars.blockFreeVars body bound {}).toArray.qsort (· < ·)
        -- The variables in scope: those `vars` names, and those captured
        -- by the outlined join points in scope, which the body's jumps to
        -- them pass by name even where `vars` names them differently.
        let varTys : Std.HashMap String RR.Ty := ctx.vars.fold (fun m _ (n, t) => m.insert n t) ctx.captured
        let captured := free.filter varTys.contains
        let capturedTys := captured.map fun n => (n, varTys.getD n .unit)
        let fparams := capturedTys ++ pnames.zip ptys
        let ctx := { ctx with captured := capturedTys.foldl (fun m (n, t) => m.insert n t) ctx.captured }
        if let some sm := ctx.sm then
          -- J4: a variant of the state machine.
          let variant ← fresh "j"
          modify fun s => { s with smArms := s.smArms.push (variant, fparams, body) }
          return ← lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.enter variant captured) } outlined retTy k
        let fn ← fresh "jp_"
        modify fun s => { s with fns := s.fns.push (.fn fn fparams retTy body) }
        lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.call fn captured) } outlined retTy k
      else
        let jumps := (countJumps k {}).getD d.fvarId 0
        if jumps ≤ 1 || (H.duplicateJp { bodies := ctx.jpBodies, single := ctx.jpSingle, loop := ctx.loop } d jumps &&
            !endsInJumps k (({} : FVarIdSet).insert d.fvarId) outlined) then
          -- J1, or a small join point that is not J2: its body at each jump.
          let jpSingle := if jumps ≤ 1 then ctx.jpSingle.insert d.fvarId else ctx.jpSingle
          lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.inline d.params d.value), jpSingle }
            outlined retTy k
        else
          -- J2: the scope computes the join point's arguments.
          let resTy ← match ptys.size with
            | 0 => pure RR.Ty.unit
            | 1 => pure ptys[0]!
            | _ => pure (RR.Ty.named (← tupleType ptys))
          let scope ← lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.yield ptys) } outlined resTy k
          let r ← fresh "jv"
          let mut lets : Array (String × Option RR.Ty × RR.Expr) := #[(r, some resTy, .block scope)]
          let mut ctx' := { ctx with vars := unitVars ctx.vars }
          for h : i in [:params.size] do
            let p := params[i]
            let x ← fresh "y"
            let e := if ptys.size == 1 then RR.Expr.var r else .field (.var r) i
            lets := lets.push (x, some ptys[i]!, e)
            ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, ptys[i]!) }
          let b ← lowerCode ctx' outlined retTy d.value
          return { b with lets := lets ++ b.lets }
    | .fun d k _ =>
      -- Lambda lifting normally removes local functions; lower defensively:
      -- nested Reussir closures, one per domain of the function's type at
      -- run time (rule 4: a phantom domain has none; a unit domain at a
      -- parameter the function does not take, `keepMask`, is ignored).
      let fty ← lowerType d.type
      let keep := keepMask (d.params.map (·.type))
      let mut vars := ctx.vars
      let mut layers : Array (String × RR.Ty) := #[]
      let mut pre : Array (String × Option RR.Ty × RR.Expr) := #[]
      let mut t := fty
      for h : i in [:d.params.size] do
        let p := d.params[i]
        -- `lowerType` gives a domain (unit, phantom or data) for every
        -- domain of the Lean type, and a local function's type has one per
        -- parameter (Lean's invariant), so this holds.
        let .fn dom c := t | throwError "lean2rr: local function {d.binderName}: its type {d.type} has fewer domains than its {d.params.size} parameters (internal error)"
        if dom == RR.Ty.phantom then
          -- No argument at run time: a placeholder for a parameter it takes.
          if keep[i]! && !erasedDom p.type then
            let x ← fresh "lp"
            let pt ← lowerType p.type
            pre := pre.push (x, some pt, ← zeroValue pt)
            vars := vars.insert p.fvarId (x, pt)
          else vars := vars.insert p.fvarId ("L2RUnit::u{}", .unit)
        else
          let x ← fresh "lp"
          layers := layers.push (x, t)
          vars := vars.insert p.fvarId (if keep[i]! then (x, dom) else ("L2RUnit::u{}", .unit))
        t := c
      if layers.isEmpty then
        throwError "lean2rr: local function {d.binderName}: every domain of its type {d.type} is phantom (internal error: its last domain stays, `keptErasedHead`)"
      let bodyCtx := { ctx with vars }
      let body ← lowerCode bodyCtx outlined t d.value
      let mut lam := RR.Expr.block { body with lets := pre ++ body.lets }
      for (n, lt) in layers.reverse do
        lam := rawFnValue lt n (.ofExpr lam)
      let x ← fresh "f"
      let b ← lowerCode { ctx with vars := ctx.vars.insert d.fvarId (x, fty) } outlined retTy k
      return { b with lets := #[(x, some fty, lam)] ++ b.lets }
    | _ => throwError "lean2rr: impure code (internal error)"

  partial def lowerCases (ctx : CodeCtx) (outlined : FVarIdSet) (retTy : RR.Ty) (cs : Cases .pure) :
      LowerM RR.Expr := do
    let some (scrut0, sty0) := ctx.vars[cs.discr]? | throwError "lean2rr: cases on unbound variable"
    -- A `cases` on a value of statically unknown type: unbox it to the
    -- inductive's one type first (`uniformType`).
    if sty0 == RR.Ty.box then
      let uty ← uniformType cs.typeName
      let u ← fresh "uv"
      let conv ← coerce (.var scrut0) RR.Ty.box uty
      let ctx' := { ctx with vars := ctx.vars.insert cs.discr (u, uty) }
      return .block ⟨#[(u, some uty, conv)], ← lowerCases ctx' outlined retTy cs⟩
    -- A cast value (see `castCases`): converted first, or matched through
    -- the corresponding constructors of its own type.
    let mut view : Option String := none
    match ← castCases sty0 cs.typeName with
    | .same => pure ()
    | .view _ dn => view := some dn
    | .convert dty =>
      let u ← fresh "cv"
      let conv ← coerce (.var scrut0) sty0 dty
      let ctx' := { ctx with vars := ctx.vars.insert cs.discr (u, dty) }
      return .block ⟨#[(u, some dty, conv)], ← lowerCases ctx' outlined retTy cs⟩
    | .unit =>
      -- No data: the only alternative, its fields carry nothing.
      let some alt := cs.alts[0]? | return .call "l2r_unreachable" #[retTy] #[]
      let ctx' := alt.getParams.foldl (fun c p => { c with vars := c.vars.insert p.fvarId ("L2RUnit::u{}", .unit) }) ctx
      return .block (← lowerCode ctx' outlined retTy alt.getCode)
    let (scrut, sty) := (scrut0, sty0)
    let altFor (ctor : Name) : Option (Alt .pure) := cs.alts.find? fun
      | .alt c _ _ _ => c == ctor
      | _ => false
    let dflt : Option (Code .pure) := cs.alts.findSome? fun
      | .default k => some k
      | _ => none
    match sty with
    | .named "bool" =>
      let branch (ctor : Name) : LowerM RR.Block := do
        match altFor ctor with
        | some alt => lowerAlt ctx outlined retTy alt.getCode
        | none =>
          match dflt with
          | some k => lowerAlt ctx outlined retTy k
          | none => return .ofExpr (.call "l2r_unreachable" #[retTy] #[])
      return .ite (.var scrut) (← branch ``Bool.true) (← branch ``Bool.false)
    | .named tn =>
      let some info := (← get).typeInfos[tn]?
        | throwError "lean2rr: cases on non-nominal type {tn} ({cs.typeName})"
      -- The alternatives' constructors, at each constructor position of
      -- the matched type, and their layouts over its records.
      let (actors, layoutOf) ← match view with
        | none => pure (info.ctorOrder, fun c => info.ctors.find? c)
        | some dn =>
          let some di := (← get).typeInfos[dn]? | throwError "lean2rr: no type {dn}"
          let mut m : NameMap CtorLayout := {}
          for (sc, dc) in info.ctorOrder.zip di.ctorOrder do
            if let (some sl, some dl) := (info.ctors.find? sc, di.ctors.find? dc) then
              m := m.insert dc (← viewLayout sc dc sl dl)
          pure (di.ctorOrder, fun c => m.find? c)
      match info.shape with
      | .struct =>
        let some alt := cs.alts[0]? | throwError "lean2rr: empty cases"
        match alt with
        | .alt ctor ps k _ =>
          let some layout := layoutOf ctor | throwError "lean2rr: bad constructor"
          -- The fields, projected (a hook may bind some later: Opt/LazyFields).
          let arm : CasesArm := { discr := cs.discr, scrut, ty := tn, layout, params := ps, code := k,
                                  shared := !info.value && view.isNone }
          let (lets, ctx') ← H.structFields ctx arm
          let convs := fieldConvNames ctx' (ps.map (·.fvarId))
          let b ← lowerCode ctx' outlined retTy k
          return .block { b with lets := dropUnusedConvs lets convs b ++ b.lets }
        | .default k => return .block (← lowerCode ctx outlined retTy k)
        | _ => throwError "lean2rr: impure alternative"
      | _ =>
        let mut arms := #[]
        for ctor in actors do
          let some layout := layoutOf ctor | continue
          match altFor ctor with
          | some (.alt _ ps k _) =>
            let mut ctx' := ctx
            let mut binders := Array.replicate (layout.fields.filter (·.isSome)).size (none : Option String)
            for h : i in [:ps.size] do
              let p := ps[i]
              match layout.fields[i]? with
              | some (some (j, ft)) =>
                let x ← fresh "f"
                binders := binders.set! j (some x)
                ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, ft) }
              | _ => ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId ("L2RUnit::u{}", .unit) }
            -- Hooks: fields bound later instead (Opt/LazyFields), bindings
            -- before the arm's code (Opt/NullaryScrutinee).
            let arm : CasesArm := { discr := cs.discr, scrut, ty := tn, layout, params := ps, code := k,
                                    shared := info.shape == .enum, view := view.isSome }
            let (armBinders, armCtx) ← H.enumFields ctx' arm binders
            let (pre, armCtx) ← H.armPrelude armCtx arm armBinders
            -- The fields bound by the match, at their parameters' own types
            -- (`bindField`); a hook may have left some to be bound later
            -- (Opt/LazyFields), and the binders keep the fields' values as
            -- the record holds them (Opt/FreshRebuild rebuilds from them).
            let mut conv := #[]
            let mut armCtx := armCtx
            for h : i in [:ps.size] do
              let p := ps[i]
              let some (some (j, ft)) := layout.fields[i]? | continue
              let some (some x) := armBinders[j]? | continue
              unless armCtx.vars[p.fvarId]? == some (x, ft) do continue
              let (c, ctx2) ← bindField armCtx p.fvarId (← lowerType p.type) x ft
              conv := conv ++ c
              armCtx := ctx2
            let body ← lowerAlt armCtx outlined retTy k
            conv := dropUnusedConvs conv (conv.foldl (fun s (y, _, _) => s.insert y) {}) body
            arms := arms.push { ty := tn, ctor := some layout.variant, binders := armBinders,
                                body := { body with lets := pre ++ conv ++ body.lets } }
          | _ => pure ()
        if arms.size < info.ctorOrder.size then
          let body ← match dflt with
            | some k => lowerAlt ctx outlined retTy k
            | none => pure (.ofExpr (.call "l2r_unreachable" #[retTy] #[]))
          arms := arms.push { ty := tn, ctor := none, binders := #[], body }
        return .mtch (.var scrut) (← sinkWildcardHeld ctx scrut info.ctorOrder.size arms)
    | t => throwError "lean2rr: cases on value of type {t.render} ({cs.typeName})"

  /-- Lower the code of an alternative, after its fields are bound (a hook
  may bind more first: Opt/LazyFields). -/
  partial def lowerAlt (ctx : CodeCtx) (outlined : FVarIdSet) (retTy : RR.Ty) (k : Code .pure) :
      LowerM RR.Block :=
    H.lowerAlt (lowerAlt · outlined retTy) (lowerCode · outlined retTy) ctx retTy k
end

/-- Lower a declaration with code to a Reussir function. -/
def lowerDecl (d : Decl .pure) : LowerM Unit := do
  let .code body := d.value | return
  let body := H.prepareBody body
  let (ps, r) := splitFnType d.type d.params.size
  let _ := ps
  let ret ← lowerType r
  -- Rule 4a: the Reussir function takes an erased parameter only when it
  -- is the last one (one unit for the trailing erased ones); the others
  -- are bound to the unit value.
  let keep := keepMask (d.params.map (·.type))
  let mut params : Array (String × RR.Ty) := #[]
  let mut vars : Std.HashMap FVarId (String × RR.Ty) := {}
  for h : i in [:d.params.size] do
    let p := d.params[i]
    if keep[i]! then
      let x ← fresh "a"
      let t ← lowerType p.type
      params := params.push (x, t)
      vars := vars.insert p.fvarId (x, t)
    else vars := vars.insert p.fvarId ("L2RUnit::u{}", .unit)
  let pnames := params.map (·.1)
  -- `IO.Process.output`: generated glue instead of Lean's body (see
  -- `processOutputBody`).
  let orig := ((← read).keys.find? d.name).map (·.decl) |>.getD d.name
  if orig == ``IO.Process.output && d.params.size == 3 then
    let block ← processOutputBody params ret r
    modify fun s => { s with fns := s.fns.push (.fn (fnName d.name) params ret block) }
    return
  let loop := ((← read).callCycles.find? d.name).getD {}
  let outlined := chooseOutlined H.duplicateJp loop body
  -- J4: the declaration as one state machine when an outlined join point
  -- calls it back in tail position (`LowerHooks.stateMachine`).
  let sm? := H.stateMachine.plan d body outlined pnames
  modify fun s => { s with smArms := #[] }
  let ctx : CodeCtx := { vars, sm := sm?, loop, used := codeUses body {} }
  -- The body of a declaration without parameters runs once: a constant
  -- boxed there is boxed in line (`boxOf`), not given a once-cell.
  modify fun s => { s with inConstBody := d.params.isEmpty }
  let block ← try lowerCode H ctx outlined ret body
    catch e => throwError "{e.toMessageData}\n  while lowering {d.name}"
  modify fun s => { s with inConstBody := false }
  if let some sm := sm? then
    H.stateMachine.emit d sm params ret block
    return
  -- A constant is cached in a once-cell, unless a hook has it recomputed
  -- at each use (Opt/CheapConsts) or it is a closed term evaluated where
  -- it is used (`uncachedConsts`, `chainConsts`).
  if d.params.isEmpty && !(← H.recomputeConst body) && !(← read).uncachedConsts.contains d.name then
    let acc ← cafAccessor (fnName d.name) ret
    modify fun s => { s with fns := s.fns.push (.fn (fnName d.name ++ "_init") #[] ret block) |>.push acc }
  else
    modify fun s => { s with fns := s.fns.push (.fn (fnName d.name) params ret block) }

end

end LeanToReussir
