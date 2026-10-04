import Lean
import LeanToReussir.PassConfig

/-!
# Updates of uniform containers without round trips (optimization `uniform-updates`)

Stage 3 (translation plan §4): a container whose element type depends on a
value (`data : Array ty.denote` in a structure, where `ty` is a field) has
the mono type `Array lcAny`, so its representation is an array of `Box`es.
Where Lean uses it at a precise type (`d.push i` in the branch where
`ty = .nat`), the plain translation converts it element by element to that
type, runs the operation, and converts the result back element by element
when it is stored in the `Array lcAny` field again: two copies of the whole
array per update, so a loop of updates is quadratic, where natively the cast
is free and the update is in place (review RV9C-02).

This pass runs such an operation on the uniform array instead: an `Array`
extern (`push`, `set`, `pop`, `get`, `size`, …), which does not depend on its
type arguments, is called at its instance at `lcAny`, so only the single
element crosses representations (boxed going in, unboxed coming out); and a
constructor application whose result goes to a uniform position (`i :: d`
with `d : List lcAny`, stored in a `List lcAny` field) is built at that
uniform type. A call is changed only if it receives a uniform value it would
otherwise convert (directly, or through another call this pass changes), its
other arguments then need at most a box, and, when its result is a uniform
container, every use of the result expects exactly that type (so no
conversion moves elsewhere). Code that never meets a uniform container is
unchanged.
-/

namespace LeanToReussir
open Lean Compiler LCNF

namespace UniformUpdates

/-- How a variable is used: as argument `i` of the `let` binding `y`, as
argument `i` of a jump to `j`, returned, or otherwise (a projection, a
`cases`, a closure application). -/
inductive Use where
  | arg (y : FVarId) (i : Nat)
  | jmp (j : FVarId) (i : Nat)
  | ret
  | other

structure Body where
  types : Std.HashMap FVarId Expr := {}
  values : Std.HashMap FVarId (LetValue .pure) := {}
  uses : Std.HashMap FVarId (Array Use) := {}
  jpParams : Std.HashMap FVarId (Array Expr) := {}
  /-- The parameters of each join point. -/
  jpParamIds : Std.HashMap FVarId (Array FVarId) := {}
  /-- The arguments of each jump, per join point. -/
  jumps : Std.HashMap FVarId (Array (Array (Arg .pure))) := {}

def Body.use (b : Body) (x : FVarId) (u : Use) : Body :=
  { b with uses := b.uses.insert x ((b.uses.getD x #[]).push u) }

partial def scan (c : Code .pure) (b : Body) : Body :=
  match c with
  | .let d k =>
    let b := { b with types := b.types.insert d.fvarId d.type, values := b.values.insert d.fvarId d.value }
    let b := match d.value with
      | .const _ _ args _ => args.zipIdx.foldl (fun b (a, i) => match a with
          | .fvar x => b.use x (.arg d.fvarId i)
          | _ => b) b
      | .fvar g args => args.foldl (fun b a => match a with
          | .fvar x => b.use x .other
          | _ => b) (b.use g .other)
      | .proj _ _ x => b.use x .other
      | _ => b
    scan k b
  | .jp d k | .fun d k _ =>
    let b := { b with
      types := d.params.foldl (fun m p => m.insert p.fvarId p.type) (b.types.insert d.fvarId d.type)
      jpParams := b.jpParams.insert d.fvarId (d.params.map (·.type))
      jpParamIds := b.jpParamIds.insert d.fvarId (d.params.map (·.fvarId)) }
    scan k (scan d.value b)
  | .cases cs =>
    let b := b.use cs.discr .other
    cs.alts.foldl (fun b alt =>
      let b := alt.getParams.foldl (fun b p => { b with types := b.types.insert p.fvarId p.type }) b
      scan alt.getCode b) b
  | .return x => b.use x .ret
  | .jmp j args =>
    let b := { b with jumps := b.jumps.insert j ((b.jumps.getD j #[]).push args) }
    args.zipIdx.foldl (fun b (a, i) => match a with
      | .fvar x => b.use x (.jmp j i)
      | _ => b) b
  | .unreach _ => b

/-- The change planned for a `let` or a join point's parameter: the callee it
calls instead (an extern's instance at `lcAny`; `none` for a constructor or
a parameter), the parameter types of what it then calls (for a constructor:
its field types, after the parameters), and the binder's new type, if it
changes. -/
structure Plan where
  callee : Option Name
  params : Array Expr
  newTy : Option Expr
  /-- For an extern: the extern and its base declaration, whose instance at
  `lcAny` is `callee` (made again for the plans kept, see
  `uniformUpdatesDecl`). -/
  ext : Option (Name × Decl .pure × Array Expr) := none

def isPlaceholder (b : Body) (a : Arg .pure) : Bool :=
  match a with
  | .fvar x => match b.values[x]? with
    | some .erased => true
    | _ => false
  | _ => true

/-- The type a use expects, in a body `b` of a declaration whose result type
is `declRet`, given the planned changes. -/
def expectedType (b : Body) (declRet : Expr) (plans : Std.HashMap FVarId Plan) (u : Use) :
    MRetypeM (Option Expr) := do
  match u with
  | .ret => return some declRet
  | .jmp j i =>
    if let some x := (b.jpParamIds[j]?).bind (·[i]?) then
      if let some nt := (plans[x]?).bind (·.newTy) then return some nt
    return (b.jpParams[j]?).bind (·[i]?)
  | .other => return none
  | .arg y i =>
    if let some p := plans[y]? then return p.params[i]?
    let some (.const g _ args _) := b.values[y]? | return none
    if let some (.ctorInfo ci) := (← getEnv).find? g then
      if i < ci.numParams then return none
      return (← ctorFieldTypes g (b.types.getD y anyExpr))[i - ci.numParams]?
    let some sig := (← get).sigs[g]? | return none
    if args.size > sig.params.size then return none
    return sig.params[i]?

/-- The scan of a declaration's body, its parameters included. -/
def bodyOf (d : Decl .pure) (c : Code .pure) : Body :=
  scan c (d.params.foldl (fun b p => { b with types := b.types.insert p.fvarId p.type }) {})

end UniformUpdates

open UniformUpdates in
/-- Run the containers' updates of `d` on their uniform representation (see
the module comment). -/
partial def uniformUpdatesDecl (d : Decl .pure) : MRetypeM (Decl .pure) := do
  let .code c := d.value | return d
  let b := bodyOf d c
  let env ← getEnv
  let keys := (← get).keys
  let declRet := (splitArrows d.type d.params.size).2
  let tyOf (x : FVarId) : Expr := b.types.getD x anyExpr
  let same (t u : Expr) : MRetypeM Bool := return (← norm t) == (← norm u)
  -- Candidates: calls of `Array` externs at precise types (their instance at
  -- `lcAny`), constructor applications (planned after the externs).
  -- The extern instances made while planning are made again for the plans
  -- kept only, so that a declaration where nothing changes gets none.
  let saved ← get
  let mut plans : Std.HashMap FVarId Plan := {}
  for (x, v) in b.values.toList do
    let .const f _ args _ := v | continue
    let some k := keys.find? f | continue
    unless k.dicts.isEmpty && k.decl.getPrefix == `Array && !k.typeArgs.isEmpty do continue
    if k.typeArgs.all (· == anyExpr) then continue
    let some base ← getBaseDecl? k.decl | continue
    unless base.value matches .extern _ do continue
    let some cur := (← get).sigs[f]? | continue
    unless args.size == cur.params.size do continue
    let uargs := k.typeArgs.map fun _ => anyExpr
    let u ← externInstance k.decl base uargs
    let some sig := (← get).sigs[u]? | continue
    let newTy ← if (← unknown sig.ret) && sig.ret.consumeMData != anyExpr then pure (some sig.ret) else pure none
    -- A result of another type than the binder's that is not a box: no.
    if newTy.isNone && sig.ret.consumeMData != anyExpr && !(← same sig.ret (tyOf x)) then continue
    plans := plans.insert x { callee := some u, params := sig.params, newTy, ext := some (k.decl, base, uargs) }
  -- The type a use of `x` expects, given the plans.
  let expected := expectedType b declRet
  -- The arguments of a planned `let` fit the new parameters (equal, or a box
  -- at a bare `lcAny`), and one of them is a uniform value that the current
  -- call converts (or a planned uniform result).
  let argsFit (plans : Std.HashMap FVarId Plan) (x : FVarId) (args : Array (Arg .pure))
      (curParams : Array Expr) (p : Plan) : MRetypeM Bool := do
    let mut gain := false
    for h : i in [:args.size] do
      let a := args[i]
      if isPlaceholder b a then continue
      let .fvar y := a | continue
      let some pt := p.params[i]? | return false
      let ty := (plans[y]?.bind (·.newTy)).getD (tyOf y)
      unless (← same ty pt) || pt.consumeMData == anyExpr do return false
      if (plans[y]?.bind (·.newTy)).isSome then gain := true
      else if let some cp := curParams[i]? then
        if (← unknown (tyOf y)) && !(← same (tyOf y) cp) then gain := true
    let _ := x
    return gain
  -- Join points' parameters of a precise container type that a jump passes a
  -- uniform value (or a planned uniform result) to, and whose uses expect a
  -- uniform type: that type.
  -- (Repeated until no parameter is added: a jump's argument can be the
  -- parameter of another join point planned in an earlier round.)
  let mut added := true
  while added do
   added := false
   for (j, ps) in b.jpParamIds.toList do
    for h : i in [:ps.size] do
      let x := ps[i]
      if plans.contains x then continue
      let ty := tyOf x
      if ← unknown ty then continue
      let mut u? : Option Expr := none
      for use in b.uses.getD x #[] do
        if u?.isNone then
          if let some e ← expected plans use then
            if (← unknown e) && refines (← norm e) (← norm ty) then u? := some e
      let some u := u? | continue
      let mut gain := false
      for args in b.jumps.getD j #[] do
        if let some (.fvar y) := (args[i]? : Option (Arg .pure)) then
          if (plans[y]?.bind (·.newTy)).isSome || (← unknown (tyOf y)) then gain := true
      if gain then
        plans := plans.insert x { callee := none, params := #[], newTy := some u }
        added := true
  -- The uses of a planned uniform value `x` of type `nt`: each expects `nt`,
  -- or a precise type that `nt` converts to (a read that does not flow back:
  -- a fold at `Array Nat`, a closure capturing it; the conversion runs there,
  -- on that use's own path, review C02R-02); and one of them takes it back to
  -- a uniform position (a field, a uniform parameter, a planned update), the
  -- round trip being what is avoided. A planned read (`size`, `get`) accepts
  -- a uniform array but does not take it anywhere.
  let usesFit (plans : Std.HashMap FVarId Plan) (x : FVarId) (nt : Expr) : MRetypeM Bool := do
    let mut back := false
    for u in b.uses.getD x #[] do
      match ← expected plans u with
      | some e =>
        if ← same e nt then
          let read := match u with
            | .arg y _ => match plans[y]? with
              | some q => q.newTy.isNone
              | none => false
            | _ => false
          unless read do back := true
        else unless refines (← norm nt) (← norm e) do return false
      | none => return false
    return back
  -- Greatest fixpoint over the extern and join point plans: drop a plan whose
  -- arguments (a join point's: the jumps' arguments) do not fit or whose
  -- uniform result has a use that expects another type.
  let mut changed := true
  while changed do
    changed := false
    for (x, p) in plans.toList do
      if p.callee.isNone then
        -- A join point's parameter.
        let some nt := p.newTy | continue
        let some (j, i) := b.jpParamIds.toList.findSome? fun (j, ps) => (ps.idxOf? x).map (j, ·) | continue
        -- A jump passes a uniform value; another may pass a precise one that
        -- `nt` refines (a fresh array on a rare path), converted at that jump.
        let mut ok := true
        let mut gain := false
        for args in b.jumps.getD j #[] do
          match (args[i]? : Option (Arg .pure)) with
          | some a@(.fvar y) =>
            unless isPlaceholder b a do
              let ty := (plans[y]?.bind (·.newTy)).getD (tyOf y)
              if ← same ty nt then gain := true
              else unless refines (← norm nt) (← norm ty) do ok := false
          | _ => pure ()
        unless gain && (← usesFit plans x nt) do ok := false
        unless ok do
          plans := plans.erase x
          changed := true
        continue
      let some (.const f _ args _) := b.values[x]? | continue
      let curParams := ((← get).sigs[f]?).map (·.params) |>.getD #[]
      let mut ok ← argsFit plans x args curParams p
      if ok then
        if let some nt := p.newTy then
          unless ← usesFit plans x nt do ok := false
      unless ok do
        plans := plans.erase x
        changed := true
  -- Constructor applications whose uses all expect one uniform type.
  for (x, v) in b.values.toList do
    let .const g _ args _ := v | continue
    let some (.ctorInfo ci) := env.find? g | continue
    let ty := tyOf x
    let some use0 := (b.uses.getD x #[])[0]? | continue
    let some u ← expected plans use0 | continue
    unless (← unknown u) && !(← same u ty) && refines (← norm u) (← norm ty) do continue
    let mut agree := true
    for use in b.uses.getD x #[] do
      match ← expected plans use with
      | some e => unless ← same e u do agree := false
      | none => agree := false
    unless agree do continue
    let fs ← ctorFieldTypes g u
    let cur ← ctorFieldTypes g ty
    let params := (List.replicate ci.numParams erasedExpr).toArray ++ fs
    let curParams := (List.replicate ci.numParams erasedExpr).toArray ++ cur
    if ← argsFit plans x args curParams { callee := none, params, newTy := some u } then
      plans := plans.insert x { callee := none, params, newTy := some u }
  set saved
  if plans.isEmpty then return d
  for (x, p) in plans.toList do
    if let some (e, base, uargs) := p.ext then
      let u ← externInstance e base uargs
      plans := plans.insert x { p with callee := some u }
  return { d with value := .code (rewrite plans c) }
where
  rewrite (plans : Std.HashMap FVarId UniformUpdates.Plan) (c : Code .pure) : Code .pure :=
    match c with
    | .let dl k =>
      let dl := match plans[dl.fvarId]?, dl.value with
        | some p, .const f us args _ =>
          { dl with value := .const (p.callee.getD f) us args, type := p.newTy.getD dl.type }
        | _, _ => dl
      .let dl (rewrite plans k)
    | .jp dj k =>
      let params := dj.params.map fun p => match (plans[p.fvarId]?).bind (·.newTy) with
        | some t => { p with type := t }
        | none => p
      .jp (FunDecl.mk dj.fvarId dj.binderName params dj.type (rewrite plans dj.value)) (rewrite plans k)
    | .fun dj k _ => .fun (FunDecl.mk dj.fvarId dj.binderName dj.params dj.type (rewrite plans dj.value)) (rewrite plans k)
    | .cases cs => .cases ⟨cs.typeName, cs.resultType, cs.discr, cs.alts.map fun
        | .alt ctor ps code _ => .alt ctor ps (rewrite plans code)
        | .default code => .default (rewrite plans code)
        | a => a⟩
    | c => c

open UniformUpdates in
/-- A parameter of a precise array type (`Array Nat`) that every call site,
partial applications included, passes a uniform array (`Array lcAny`):
typically a closure capturing an updated column (`fun _ => d'.size`, lifted
to `_lam_N d'`), whose capture would convert the column at every step
(review C02R-02). It becomes uniform when, with that type, the
declaration's body (after `uniformUpdatesDecl`) uses it only where a uniform
array is expected: its reads run on the uniform array, and no call site
converts. Returns the new declarations, or `none` if nothing changed. -/
def uniformParams (decls : Array (Decl .pure)) : MRetypeM (Option (Array (Decl .pure))) := do
  let types := decls.map fun d => match d.value with
    | .code c => (bodyOf d c).types.fold (fun m k v => m.insert k v) ({} : Types)
    | _ => {}
  let cs ← callSites decls types
  let uniformArr := mkApp (mkConst ``Array) anyExpr
  let mut out := decls
  let mut any := false
  for h : i in [:decls.size] do
    let d := decls[i]
    let .code _ := d.value | continue
    for h' : j in [:d.params.size] do
      let p := d.params[j]
      let t := p.type.consumeMData
      unless t.isAppOfArity ``Array 1 && !(← unknown t) do continue
      if cs.blocked.contains (d.name, j) then continue
      let some argTys := cs.args[(d.name, j)]? | continue
      if argTys.isEmpty then continue
      let mut ok := true
      for argTy? in argTys do
        if let some argTy := argTy? then
          unless (← norm argTy) == (← norm uniformArr) do ok := false
      unless ok do continue
      -- Tentatively: the body with the parameter uniform, its updates and
      -- reads planned; then every use of the parameter must expect it.
      let params := d.params.set! j { p with type := uniformArr }
      let d' := withSig d params (splitArrows d.type d.params.size).2
      modify fun s => { s with sigs := s.sigs.insert d.name (declSig d') }
      let d'' ← uniformUpdatesDecl d'
      let .code c'' := d''.value | continue
      let b := bodyOf d'' c''
      let declRet := (splitArrows d''.type d''.params.size).2
      let mut fits := true
      for u in b.uses.getD p.fvarId #[] do
        match ← expectedType b declRet {} u with
        | some e => unless (← norm e) == (← norm uniformArr) do fits := false
        | none => fits := false
      -- Its own recursive calls pass a uniform array there too (call sites in
      -- the declaration itself are not among `callSites`' arguments).
      for (_, v) in b.values.toList do
        if let .const g _ args _ := v then
          if g == d.name then
            match (args[j]? : Option (Arg .pure)) with
            | some (.fvar y) =>
              unless isPlaceholder b (.fvar y) do
                unless (← norm (b.types.getD y anyExpr)) == (← norm uniformArr) do fits := false
            | _ => pure ()
      if fits then
        out := out.set! i d''
        any := true
        break
      else
        modify fun s => { s with sigs := s.sigs.insert d.name (declSig d) }
  return if any then some out else none

/-- Registry entry point. -/
def Opt.UniformUpdates.install (c : PassConfig) : PassConfig :=
  let prev := c.stage3.uniformUpdates
  { c with stage3 := { c.stage3 with uniformUpdates := fun decls => do
      let mut decls ← (← prev decls).mapM uniformUpdatesDecl
      -- Parameters that callers now pass uniform arrays (a few rounds: a
      -- declaration retyped may pass its parameter on).
      for _ in [:4] do
        match ← uniformParams decls with
        | some ds => decls := ds
        | none => break
      return decls } }

end LeanToReussir
