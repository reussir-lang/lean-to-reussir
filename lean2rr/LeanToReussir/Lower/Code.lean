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
                return .ofExpr (.call sm.fn #[] (vals.push (.ctor sm.mode (some sm.entry) #[])))
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
        return .ofExpr (.call sm.fn #[] (sm.params.map .var |>.push (.ctor sm.mode (some variant) (captured.map .var ++ vals))))
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
          let mut ctx' := ctx
          let mut lets := #[]
          -- A shared structure that stays live because it is stored or
          -- returned whole binds only the fields used while it is live; the
          -- others are projected in the inner alternatives that use them
          -- (`lowerAlt`), as for the constructors of an enum (below): a
          -- field projected here would be an extra reference whose release
          -- Reussir's token reuse takes for a freed cell.
          let lazyOk := !info.value && view.isNone &&
            (usedAsField (← getEnv) ctx.jpBodies cs.discr k || returnedWhole ctx.jpBodies cs.discr k)
          let early := if lazyOk then usesWhileLive ctx.jpBodies cs.discr k {} else {}
          let used := if lazyOk then codeUses k {} else {}
          let mut pending := #[]
          for h : i in [:ps.size] do
            let p := ps[i]
            match layout.fields[i]? with
            | some (some (j, ft)) =>
              if lazyOk && !early.contains p.fvarId then
                if used.contains p.fvarId then pending := pending.push (p.fvarId, j, ft)
              else
                let x ← fresh "f"
                lets := lets.push (x, some ft, RR.Expr.field (.var scrut) j)
                ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, ft) }
            | _ => ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId ("L2RUnit::u{}", .unit) }
          if !pending.isEmpty then
            let l : LazyMatch := { discr := cs.discr, scrut, ty := tn, variant := layout.variant, nbinders := 0,
                                   fields := pending, pending, struct := true }
            ctx' := { ctx' with lazy := ctx'.lazy.push l }
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
            -- An arm in which the matched value stays live because it is
            -- stored whole in a new constructor, or returned whole (`simp`
            -- turns `t@(node l k r)` rebuilt into `t`: a BST insert of a key
            -- already present), binds only the fields needed while it is
            -- live; a field used only in inner alternatives that do not use
            -- the value is bound there, by matching the value again
            -- (`lowerAlt`). Reussir projects a match's fields at the match:
            -- a field of a value that stays live is then an extra reference
            -- (inc and dec), and its release looks like a reusable cell to
            -- Reussir's token reuse, which prefers it to the cell actually
            -- freed and then never reuses anything (TreeMap's `balance`
            -- rebuilt every node of the path; a BST insert with `Nat` keys,
            -- whose comparison is a call before the branch, every node).
            -- Not for values only passed to calls: there reusing the cell
            -- (merge's `go l₁ ys (y :: acc)`) measured slower for mergesort,
            -- whose lists then keep the scattered order of the input cells.
            if !binders.isEmpty && info.shape == .enum &&
                (usedAsField (← getEnv) ctx.jpBodies cs.discr k || returnedWhole ctx.jpBodies cs.discr k) then
              let early := usesWhileLive ctx.jpBodies cs.discr k {}
              let used := codeUses k {}
              let mut fields := #[]
              let mut pending := #[]
              for h : i in [:ps.size] do
                let p := ps[i]
                if let some (some (j, ft)) := layout.fields[i]? then
                  if used.contains p.fvarId then fields := fields.push (p.fvarId, j, ft)
                  if !early.contains p.fvarId then
                    binders := binders.set! j none
                    ctx' := { ctx' with vars := ctx'.vars.erase p.fvarId }
                    if used.contains p.fvarId then pending := pending.push (p.fvarId, j, ft)
              if !fields.isEmpty then
                let l : LazyMatch :=
                  { discr := cs.discr, scrut, ty := tn, variant := layout.variant,
                    nbinders := binders.size, fields, pending }
                ctx' := { ctx' with lazy := ctx'.lazy.push l }
            -- In the arm of a constructor without fields, the matched value
            -- is that constructor, which costs nothing to build (`leaf` used
            -- as the children of a new node).
            let mut pre := #[]
            if binders.isEmpty && hasFVar cs.discr k then
              let x ← fresh "nc"
              pre := #[(x, some sty, RR.Expr.ctor tn (some layout.variant) #[])]
              ctx' := { ctx' with vars := ctx'.vars.insert cs.discr (x, sty),
                                  lazy := ctx'.lazy.map fun l =>
                                    { l with fields := l.fields.filter (·.1 != cs.discr),
                                             pending := l.pending.filter (·.1 != cs.discr) } }
            let body ← lowerAlt ctx' outlined retTy k
            arms := arms.push { ty := tn, ctor := some layout.variant, binders, body := { body with lets := pre ++ body.lets } }
          | _ => pure ()
        if arms.size < info.ctorOrder.size then
          let body ← match dflt with
            | some k => lowerAlt ctx outlined retTy k
            | none => pure (.ofExpr (.call "l2r_unreachable" #[retTy] #[]))
          arms := arms.push { ty := tn, ctor := none, binders := #[], body }
        return .mtch (.var scrut) arms
    | t => throwError "lean2rr: cases on value of type {t.render} ({cs.typeName})"

  /-- Lower the code of an alternative. A lazily matched value (see
  `lowerCases`) whose fields the alternative uses is matched again first.
  When the alternative does not use the value itself, the value dies here:
  this match consumes it and binds every field the alternative uses (also
  those bound before, which are then only borrowed). Otherwise it binds the
  pending fields needed while the value is live. -/
  partial def lowerAlt (ctx : CodeCtx) (outlined : FVarIdSet) (retTy : RR.Ty) (k : Code .pure) :
      LowerM RR.Block := do
    if ctx.lazy.isEmpty then return ← lowerCode ctx outlined retTy k
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
        let body ← lowerAlt ctx' outlined retTy k
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
      let body ← lowerAlt ctx' outlined retTy k
      return .ofExpr (.mtch (.var scrut) #[
        { ty := l.ty, ctor := some l.variant, binders, body },
        { ty := l.ty, ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[retTy] #[]) }])
    lowerCode ctx outlined retTy k
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
  -- J4 when an outlined join point tail-calls the declaration: a loop
  -- passes through it. (Other calls need no state machine; going through
  -- its entry wrapper would only cost an allocation per call.)
  let callsBack := outlinedBodies body outlined |>.any (hasSelfTailCall d.name d.params.size)
  let sm? : Option StateMachine ← do
    if !callsBack || d.params.isEmpty || (← IO.getEnv "L2R_NO_J4").isSome then pure none
    else
      let base := fnName d.name
      pure (some { fn := base ++ "_sm", mode := base ++ "_mode", self := d.name, arity := d.params.size, params := pnames })
  modify fun s => { s with smArms := #[] }
  let ctx : CodeCtx := { vars := (d.params.zip (pnames.zip ptys)).foldl (fun m (p, nt) => m.insert p.fvarId nt) {}, sm := sm? }
  let block ← try lowerCode H ctx outlined ret body
    catch e => throwError "{e.toMessageData}\n  while lowering {d.name}"
  if let some sm := sm? then
    let arms := (← get).smArms
    -- A shared enum: Reussir miscompiles `[value]` enums whose arms have
    -- different layouts (translation plan §9); Reussir reuses the cell of
    -- the matched value.
    let mode := RR.Item.enum sm.mode false
      (#[(sm.entry, #[])] ++ arms.map fun (v, fps, _) => (v, fps.map (·.2)))
    let mkArm (v : String) (names : Array String) (b : RR.Block) : RR.Arm :=
      { ty := sm.mode, ctor := some v, binders := names.map some, body := b }
    let matchArms := #[mkArm sm.entry #[] block] ++ arms.map fun (v, fps, b) => mkArm v (fps.map (·.1)) b
    let m ← fresh "m"
    modify fun s => { s with
      typeItems := s.typeItems.push mode
      fns := s.fns
        |>.push (.fn sm.fn ((pnames.zip ptys).push (m, .named sm.mode)) ret (.ofExpr (.mtch (.var m) matchArms)))
        |>.push (.fn (fnName d.name) (pnames.zip ptys) ret
            (.ofExpr (.call sm.fn #[] ((pnames.map .var).push (.ctor sm.mode (some sm.entry) #[])))))
      smArms := #[] }
    return
  -- A constant is cached in a once-cell, unless a hook has it recomputed
  -- at each use (Opt/CheapConsts) or evaluated where it is used
  -- (`uncachedConsts`, Opt/ClosedChains).
  if d.params.isEmpty && !(← H.recomputeConst body) && !(← read).uncachedConsts.contains d.name then
    let acc ← cafAccessor (fnName d.name) ret
    modify fun s => { s with fns := s.fns.push (.fn (fnName d.name ++ "_init") #[] ret block) |>.push acc }
  else
    modify fun s => { s with fns := s.fns.push (.fn (fnName d.name) (pnames.zip ptys) ret block) }

end

end LeanToReussir
