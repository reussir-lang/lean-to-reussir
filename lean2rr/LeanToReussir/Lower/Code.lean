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

section
variable (H : LowerHooks)

mutual
  /-- Lower a code block whose value has Reussir type `retTy`. -/
  partial def lowerCode (ctx : CodeCtx) (outlined : FVarIdSet) (retTy : RR.Ty) (c : Code .pure) :
      LowerM RR.Block := do
    match c with
    | .let d k =>
      let t ← lowerType d.type
      -- J4: a self tail call re-enters the state machine.
      if let some sm := ctx.sm then
        if let .const f _ args _ := d.value then
          if f == sm.self && args.size == sm.arity && t == retTy then
            if let .return x := k then
              if x == d.fvarId then
                let some selfDecl := (← read).decls.find? f | throwError "lean2rr: no declaration {f}"
                let (ps, _) := splitFnType selfDecl.type sm.arity
                let vals ← (args.zip ps).mapM fun (a, p) => do lowerArg ctx a (← lowerType p)
                return .ofExpr (sm.selfCall vals)
      let e ← try lowerLetValue ctx d.value d.type t
        catch ex => throwError "{ex.toMessageData}\n  in let {d.binderName} : {d.type}"
      let x ← fresh "x"
      let b ← lowerCode { ctx with vars := ctx.vars.insert d.fvarId (x, t) } outlined retTy k
      return { b with lets := #[(x, some t, e)] ++ b.lets }
    | .return x =>
      match ctx.vars[x]? with
      | some (n, t) => return .ofExpr (← coerce (.var n) t retTy)
      | none => throwError "lean2rr: return of unbound variable (internal error)"
    | .unreach _ => return .ofExpr (.call "l2r_unreachable" #[retTy] #[])
    | .cases cs => return .ofExpr (← lowerCases ctx outlined retTy cs)
    | .jmp j args =>
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
        let vals ← (args.zip tys).mapM fun (a, t) => lowerArg ctx a t
        match vals.size with
        | 0 => return .ofExpr .unitVal
        | 1 => return .ofExpr vals[0]!
        | _ => return .ofExpr (.ctor (← tupleType tys) none vals)
      | some (.call fn captured) =>
        let tys := ctx.jpParams.getD j #[]
        let vals ← (args.zip tys).mapM fun (a, t) => lowerArg ctx a t
        return .ofExpr (.call fn #[] (captured.map .var ++ vals))
      | some (.enter variant captured) =>
        let some sm := ctx.sm | throwError "lean2rr: state-machine jump outside a state machine"
        let tys := ctx.jpParams.getD j #[]
        let vals ← (args.zip tys).mapM fun (a, t) => lowerArg ctx a t
        return .ofExpr (sm.jumpCall variant (captured.map .var ++ vals))
      | none => throwError "lean2rr: jump to unknown join point (internal error)"
    | .jp d k =>
      let ptys ← d.params.mapM (lowerType ·.type)
      let ctx := { ctx with jpParams := ctx.jpParams.insert d.fvarId ptys,
                            jpBodies := ctx.jpBodies.insert d.fvarId d.value }
      if outlined.contains d.fvarId then
        -- J3: outline the body into a function over its free variables.
        let pnames ← d.params.mapM fun _ => fresh "p"
        let vars := (d.params.zip (pnames.zip ptys)).foldl (fun m (p, nt) => m.insert p.fvarId nt) ctx.vars
        let bodyCtx := { ctx with vars }
        let body ← lowerCode bodyCtx outlined retTy d.value
        let bound := pnames.foldl (·.insert ·) ({} : Std.HashSet String)
        let free := (rrFreeVars.blockFreeVars body bound {}).toArray.qsort (· < ·)
        let varTys : Std.HashMap String RR.Ty := ctx.vars.fold (fun m _ (n, t) => m.insert n t) {}
        let captured := free.filter varTys.contains
        let fparams := captured.map (fun n => (n, varTys.getD n .unit)) ++ pnames.zip ptys
        if let some sm := ctx.sm then
          -- J4: a variant of the state machine.
          let variant ← fresh "j"
          modify fun s => { s with smArms := s.smArms.push (variant, fparams, body) }
          return ← lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.enter variant captured) } outlined retTy k
        let fn ← fresh "jp_"
        modify fun s => { s with fns := s.fns.push (.fn fn fparams retTy body) }
        lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.call fn captured) } outlined retTy k
      else if (countJumps k {}).getD d.fvarId 0 ≤ 1 ||
          (H.duplicateJp d && !endsInJumps k (({} : FVarIdSet).insert d.fvarId) outlined) then
        -- J1, or a small join point that is not J2: its body at each jump.
        lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.inline d.params d.value) } outlined retTy k
      else
        -- J2: the scope computes the join point's arguments.
        let resTy ← match ptys.size with
          | 0 => pure RR.Ty.unit
          | 1 => pure ptys[0]!
          | _ => pure (RR.Ty.named (← tupleType ptys))
        let scope ← lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.yield ptys) } outlined resTy k
        let r ← fresh "jv"
        let mut lets : Array (String × Option RR.Ty × RR.Expr) := #[(r, some resTy, .block scope)]
        let mut ctx' := ctx
        for h : i in [:d.params.size] do
          let p := d.params[i]
          let x ← fresh "y"
          let e := if ptys.size == 1 then RR.Expr.var r else .field (.var r) i
          lets := lets.push (x, some ptys[i]!, e)
          ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, ptys[i]!) }
        let b ← lowerCode ctx' outlined retTy d.value
        return { b with lets := lets ++ b.lets }
    | .fun d k _ =>
      -- Lambda lifting normally removes local functions; lower defensively.
      let ptys ← d.params.mapM (lowerType ·.type)
      let pnames ← d.params.mapM fun _ => fresh "lp"
      let (_, rt) := splitFnType d.type d.params.size
      let rt ← lowerType rt
      let vars := (d.params.zip (pnames.zip ptys)).foldl (fun m (p, nt) => m.insert p.fvarId nt) ctx.vars
      let bodyCtx := { ctx with vars }
      let body ← lowerCode bodyCtx outlined rt d.value
      let mut lam := RR.Expr.block body
      let mut lt := rt
      for (n, t) in (pnames.zip ptys).reverse do
        lt := .fn t lt
        lam := rawFnValue lt n (.ofExpr lam)
      let fty := lt
      let x ← fresh "f"
      let b ← lowerCode { ctx with vars := ctx.vars.insert d.fvarId (x, fty) } outlined retTy k
      return { b with lets := #[(x, some fty, lam)] ++ b.lets }
    | _ => throwError "lean2rr: impure code (internal error)"

  partial def lowerCases (ctx : CodeCtx) (outlined : FVarIdSet) (retTy : RR.Ty) (cs : Cases .pure) :
      LowerM RR.Expr := do
    let some (scrut0, sty0) := ctx.vars[cs.discr]? | throwError "lean2rr: cases on unbound variable"
    -- A `cases` on a value of statically unknown type: convert it to the
    -- inductive's uniform instance first.
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
          let b ← lowerCode ctx' outlined retTy k
          return .block { b with lets := lets ++ b.lets }
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
                                    shared := info.shape == .enum }
            let (armBinders, armCtx) ← H.enumFields ctx' arm binders
            let (pre, armCtx) ← H.armPrelude armCtx arm armBinders
            let body ← lowerAlt armCtx outlined retTy k
            arms := arms.push { ty := tn, ctor := some layout.variant, binders := armBinders,
                                body := { body with lets := pre ++ body.lets } }
          | _ => pure ()
        if arms.size < info.ctorOrder.size then
          let body ← match dflt with
            | some k => lowerAlt ctx outlined retTy k
            | none => pure (.ofExpr (.call "l2r_unreachable" #[retTy] #[]))
          arms := arms.push { ty := tn, ctor := none, binders := #[], body }
        return .mtch (.var scrut) arms
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
  let ptys ← d.params.mapM (lowerType ·.type)
  let ret ← lowerType r
  let pnames ← d.params.mapM fun _ => fresh "a"
  -- `IO.Process.output`: generated glue instead of Lean's body (see
  -- `processOutputBody`).
  let orig := ((← read).keys.find? d.name).map (·.decl) |>.getD d.name
  if orig == ``IO.Process.output && d.params.size == 3 then
    let block ← processOutputBody (pnames.zip ptys) ret
    modify fun s => { s with fns := s.fns.push (.fn (fnName d.name) (pnames.zip ptys) ret block) }
    return
  let outlined := chooseOutlined H.duplicateJp body
  -- J4: the declaration as one state machine when an outlined join point
  -- calls it back in tail position (`LowerHooks.stateMachine`).
  let sm? := H.stateMachine.plan d body outlined pnames
  modify fun s => { s with smArms := #[] }
  let ctx : CodeCtx := { vars := (d.params.zip (pnames.zip ptys)).foldl (fun m (p, nt) => m.insert p.fvarId nt) {}, sm := sm? }
  let block ← try lowerCode H ctx outlined ret body
    catch e => throwError "{e.toMessageData}\n  while lowering {d.name}"
  if let some sm := sm? then
    H.stateMachine.emit d sm (pnames.zip ptys) ret block
    return
  -- A constant is cached in a once-cell, unless a hook has it recomputed
  -- at each use (Opt/CheapConsts) or it is a closed term evaluated where
  -- it is used (`uncachedConsts`, `chainConsts`).
  if d.params.isEmpty && !(← H.recomputeConst body) && !(← read).uncachedConsts.contains d.name then
    let acc ← cafAccessor (fnName d.name) ret
    modify fun s => { s with fns := s.fns.push (.fn (fnName d.name ++ "_init") #[] ret block) |>.push acc }
  else
    modify fun s => { s with fns := s.fns.push (.fn (fnName d.name) (pnames.zip ptys) ret block) }

end

end LeanToReussir
