import Lean
import LeanToReussir.Relevance

/-!
# Stage 3: exact recovery of types lost in mono

Lean's mono passes create binders whose types are inferred through erased
signatures — a constructor's mono type is `List.cons : lcAny → List lcAny →
List lcAny`, so `structProjCases` or `simp` may produce `cases p : Prod …
| Prod.mk (fst : lcAny) (snd : lcAny)` even though `p`'s type is exact
(translation plan §4). This pass recomputes such binder types from their
context, but only when the context determines them:

* a `cases` field gets its constructor's field type, instantiated at the
  discriminant's (exact) type arguments and passed through `toMonoType`;
* a `let` of a constructor application gets the inductive applied to the
  type arguments determined by first-order matching of the field types
  against the argument types;
* a `let` of a projection gets the field type of the structure;
* a join-point parameter gets the type of its jump arguments, if they agree.

The pass iterates to a fixpoint. It never guesses: whatever stays unknown
keeps `lcAny` and is represented by the uniform `Box` in Stage 4.
-/

namespace LeanToReussir
open Lean Compiler LCNF

abbrev Types := Std.HashMap FVarId Expr

def isUnknown (table : RelevanceTable) (t : Expr) : Bool := hasRelevantAny table t

/-- First-order matching of `pat` against `target`, where the placeholder
free variables `holes` stand for unknown inductive parameters; records
their assignments. -/
partial def matchTy (holes : Array FVarId) (pat target : Expr) (assign : Array (Option Expr)) :
    Array (Option Expr) :=
  let pat := pat.consumeMData
  let target := target.consumeMData
  match pat with
  | .fvar id =>
    match holes.idxOf? id with
    | some i =>
      match assign[i]! with
      | none => if target.isErased || target == anyExpr then assign else assign.set! i (some target)
      | some _ => assign
    | none => assign
  | .app .. =>
    if target.isApp && pat.getAppFn == target.getAppFn && pat.getAppNumArgs == target.getAppNumArgs then
      (pat.getAppArgs.zip target.getAppArgs).foldl (fun a (p, t) => matchTy holes p t a) assign
    else assign
  | .forallE _ d b _ =>
    match target with
    | .forallE _ d' b' _ => matchTy holes b b' (matchTy holes d d' assign)
    | _ => assign
  | _ => assign

/-- Field types (mono) of constructor `ctor` at inductive arguments `args`. -/
def ctorFieldTypes (ctor : Name) (args : Array Expr) : CoreM (Array Expr) := do
  let some (.ctorInfo c) := (← getEnv).find? ctor | return #[]
  let mut ty ← instantiateForall (← getOtherDeclBaseType ctor []) args[:c.numParams].toArray
  let mut out := #[]
  repeat
    match ty.headBeta with
    | .forallE _ d b _ =>
      out := out.push (← toMonoType d)
      ty := b.instantiate1 anyExpr
    | _ => break
  return out

/-- The mono type of a constructor application with argument types `argTys`
(parameters first, then fields), when matching determines it. -/
def ctorAppType (ctor : Name) (argTys : Array Expr) : CoreM (Option Expr) := do
  let some (.ctorInfo c) := (← getEnv).find? ctor | return none
  let holes ← (List.range c.numParams).toArray.mapM fun _ => mkFreshFVarId
  let mut ty ← instantiateForall (← getOtherDeclBaseType ctor []) (holes.map .fvar)
  let mut assign : Array (Option Expr) := Array.replicate c.numParams none
  let mut i := c.numParams
  repeat
    match ty.headBeta with
    | .forallE _ d b _ =>
      if let some argTy := argTys[i]? then
        assign := matchTy holes d argTy assign
      ty := b.instantiate1 anyExpr
      i := i + 1
    | _ => break
  if assign.any Option.isNone then return none
  let indTy := mkAppN (.const c.induct []) (assign.map Option.get!)
  return some (← toMonoType indTy)

structure RetypeCtx where
  table : RelevanceTable
  /-- Result types of the program's declarations and externs. -/
  sigs : NameMap Expr

partial def retypeMonoCode (ctx : RetypeCtx) (types : Types) :
    Code .pure → StateT Bool CoreM (Code .pure × Types)
  | .let d k => do
    let mut d := d
    if isUnknown ctx.table d.type then
      let refined? ← match d.value with
        | .const f _ args _ =>
          if (← getEnv).isConstructor f then
            let argTys := args.map fun
              | .fvar x => types.getD x anyExpr
              | _ => erasedExpr
            ctorAppType f argTys
          else pure none
        | .proj s i x _ =>
          match types[x]? with
          | some st =>
            let st := st.consumeMData.headBeta
            let some (.inductInfo iv) := (← getEnv).find? s | pure none
            let ctor := iv.ctors[0]!
            let fs ← ctorFieldTypes ctor st.getAppArgs
            pure fs[i]?
          | none => pure none
        | _ => pure none
      if let some t := refined? then
        if !isUnknown ctx.table t then
          d := { d with type := t }
          set true
    let types := types.insert d.fvarId d.type
    let (k, types) ← retypeMonoCode ctx types k
    return (.let d k, types)
  | .jp d k => do
    -- Scope first, to learn the jump argument types.
    let (k, types) ← retypeMonoCode ctx types k
    let mut params := d.params
    for i in [:params.size] do
      let p := params[i]!
      if isUnknown ctx.table p.type then
        let cands := jumpArgTypes d.fvarId k i types #[]
        let known := cands.filter (!isUnknown ctx.table ·)
        if let some t := known[0]? then
          if known.all (· == t) then
            params := params.set! i { p with type := t }
            set true
    let types := params.foldl (fun m p => m.insert p.fvarId p.type) types
    let (value, types) ← retypeMonoCode ctx types d.value
    return (.jp (FunDecl.mk d.fvarId d.binderName params d.type value) k, types)
  | .fun d k _ => do
    let types := d.params.foldl (fun m p => m.insert p.fvarId p.type) types
    let (value, types) ← retypeMonoCode ctx types d.value
    let types := types.insert d.fvarId d.type
    let (k, types) ← retypeMonoCode ctx types k
    return (.fun (FunDecl.mk d.fvarId d.binderName d.params d.type value) k, types)
  | .cases cs => do
    let discrTy := (types.getD cs.discr anyExpr).consumeMData.headBeta
    let mut types := types
    let mut alts := #[]
    for alt in cs.alts do
      match alt with
      | .alt ctor ps code _ =>
        let mut ps := ps
        if ps.any (isUnknown ctx.table ·.type) && discrTy.getAppFn.isConst then
          let fs ← ctorFieldTypes ctor discrTy.getAppArgs
          for i in [:ps.size] do
            let p := ps[i]!
            if isUnknown ctx.table p.type then
              if let some t := fs[i]? then
                if !isUnknown ctx.table t then
                  ps := ps.set! i { p with type := t }
                  set true
        types := ps.foldl (fun m p => m.insert p.fvarId p.type) types
        let (code, types') ← retypeMonoCode ctx types code
        types := types'
        alts := alts.push (.alt ctor ps code)
      | .default code =>
        let (code, types') ← retypeMonoCode ctx types code
        types := types'
        alts := alts.push (.default code)
      | other => alts := alts.push other
    return (.cases ⟨cs.typeName, cs.resultType, cs.discr, alts⟩, types)
  | c => return (c, types)
where
  jumpArgTypes (j : FVarId) (c : Code .pure) (i : Nat) (types : Types) (acc : Array Expr) : Array Expr :=
    match c with
    | .jmp j' args =>
      if j' == j then
        match args[i]? with
        | some (.fvar x) => acc.push (types.getD x anyExpr)
        | _ => acc
      else acc
    | .let _ k => jumpArgTypes j k i types acc
    | .fun d k _ | .jp d k => jumpArgTypes j k i types (jumpArgTypes j d.value i types acc)
    | .cases cs => cs.alts.foldl (fun acc alt => jumpArgTypes j alt.getCode i types acc) acc
    | _ => acc

/-- Stage 3 on all mono declarations (bounded fixpoint). -/
def retypeMono (table : RelevanceTable) (decls : Array (Decl .pure)) : CoreM (Array (Decl .pure)) := do
  let ctx : RetypeCtx := { table, sigs := {} }
  decls.mapM fun d => do
    let .code c := d.value | return d
    let mut c := c
    for _ in [:6] do
      let types : Types := d.params.foldl (fun m p => m.insert p.fvarId p.type) {}
      let ((c', _), changed) ← (retypeMonoCode ctx types c).run false
      c := c'
      unless changed do break
    return { d with value := .code c }

end LeanToReussir
