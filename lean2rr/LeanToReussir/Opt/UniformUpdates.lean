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
      jpParams := b.jpParams.insert d.fvarId (d.params.map (·.type)) }
    scan k (scan d.value b)
  | .cases cs =>
    let b := b.use cs.discr .other
    cs.alts.foldl (fun b alt =>
      let b := alt.getParams.foldl (fun b p => { b with types := b.types.insert p.fvarId p.type }) b
      scan alt.getCode b) b
  | .return x => b.use x .ret
  | .jmp j args => args.zipIdx.foldl (fun b (a, i) => match a with
      | .fvar x => b.use x (.jmp j i)
      | _ => b) b
  | .unreach _ => b

/-- The change planned for a `let`: the callee it calls instead (an extern's
instance at `lcAny`; `none` for a constructor), the parameter types of what
it then calls (for a constructor: its field types, after the parameters),
and the binder's new type, if it changes. -/
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

end UniformUpdates

open UniformUpdates in
/-- Run the containers' updates of `d` on their uniform representation (see
the module comment). -/
partial def uniformUpdatesDecl (d : Decl .pure) : MRetypeM (Decl .pure) := do
  let .code c := d.value | return d
  let b := d.params.foldl (fun b p => { b with types := b.types.insert p.fvarId p.type }) ({} : Body)
  let b := scan c b
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
  let expected (plans : Std.HashMap FVarId Plan) (u : Use) : MRetypeM (Option Expr) := do
    match u with
    | .ret => return some declRet
    | .jmp j i => return (b.jpParams[j]?).bind (·[i]?)
    | .other => return none
    | .arg y i =>
      if let some p := plans[y]? then return p.params[i]?
      let some (.const g _ args _) := b.values[y]? | return none
      if let some (.ctorInfo ci) := env.find? g then
        if i < ci.numParams then return none
        return (← ctorFieldTypes g (tyOf y))[i - ci.numParams]?
      let some sig := (← get).sigs[g]? | return none
      if args.size > sig.params.size then return none
      return sig.params[i]?
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
  -- Greatest fixpoint over the extern plans: drop a plan whose arguments do
  -- not fit or whose uniform result has a use that expects another type.
  let mut changed := true
  while changed do
    changed := false
    for (x, p) in plans.toList do
      let some (.const f _ args _) := b.values[x]? | continue
      let curParams := ((← get).sigs[f]?).map (·.params) |>.getD #[]
      let mut ok ← argsFit plans x args curParams p
      if ok then
        if let some nt := p.newTy then
          for u in b.uses.getD x #[] do
            match ← expected plans u with
            | some e => unless ← same e nt do ok := false
            | none => ok := false
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
    | .jp dj k => .jp (FunDecl.mk dj.fvarId dj.binderName dj.params dj.type (rewrite plans dj.value)) (rewrite plans k)
    | .fun dj k _ => .fun (FunDecl.mk dj.fvarId dj.binderName dj.params dj.type (rewrite plans dj.value)) (rewrite plans k)
    | .cases cs => .cases ⟨cs.typeName, cs.resultType, cs.discr, cs.alts.map fun
        | .alt ctor ps code _ => .alt ctor ps (rewrite plans code)
        | .default code => .default (rewrite plans code)
        | a => a⟩
    | c => c

/-- Registry entry point. -/
def Opt.UniformUpdates.install (c : PassConfig) : PassConfig :=
  let prev := c.stage3.uniformUpdates
  { c with stage3 := { c.stage3 with uniformUpdates := fun decls => do
      (← prev decls).mapM uniformUpdatesDecl } }

end LeanToReussir
