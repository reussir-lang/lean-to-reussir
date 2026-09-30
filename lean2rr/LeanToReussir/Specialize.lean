import Lean
import LeanToReussir.Collect
import LeanToReussir.Relevance
import LeanToReussir.Retype

/-!
# Monomorphization (dry run)

The typed translation emits one Reussir function per *instance*: a reachable
declaration with its type-former parameters fixed to ground types. This
module computes the set of instances by a worklist from the root, and records
every place where the typed design would need the uniform `Box` fallback:

* **non-ground sites** — a type argument that still mentions a type variable
  after substitution (e.g. a type obtained from an existential field), or a
  partial application that leaves a type parameter open;
* **relevant `lcAny`** — an instantiated type with `lcAny` in a relevant
  position (see `Relevance`);
* **dynamic dictionary calls** — a local variable applied to type arguments
  (a polymorphic method projected from a dictionary) whose dictionary is not
  statically known, so the method cannot be resolved to a first-order call.

Types are instantiated the same way Lean's own LCNF specializer does it:
`Decl.internalize` with the type parameters substituted, which beta-reduces
every type. LCNF represents higher-kinded type arguments as type-level
lambdas (`StateT Nat Id` is `fun α => Nat → α × Nat` after `toLCNFType`), so
this yields normal forms. The instance is then re-typed (`Retype`) so that
binders Lean left as `lcAny` get their now-known types before sites are
counted.

This is a dry run: it walks code but does not yet produce specialized
declarations. Instance dictionaries are tracked only as "statically known or
not", which is enough to decide feasibility.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- A declaration with its type-former parameters fixed, plus which of its
instance parameters receive statically known dictionaries. -/
structure Instance where
  decl : Name
  typeArgs : Array Expr
  staticInsts : Array Bool
  deriving BEq, Hashable, Inhabited

def Instance.describe (i : Instance) : String :=
  if i.typeArgs.isEmpty then toString i.decl
  else s!"{i.decl} [{", ".intercalate (i.typeArgs.toList.map toString)}]"

structure SpecState where
  table : RelevanceTable
  decls : NameMap (Decl .pure)
  maxInstances : Nat
  seen : Std.HashSet Instance := {}
  work : Array Instance := #[]
  instances : Array Instance := #[]
  externInstances : Array Instance := #[]
  nonGround : Array String := #[]
  anySites : Array String := #[]
  dictCalls : Nat := 0
  dynamicDictCalls : Array String := #[]
  polyLocalFuns : Nat := 0
  truncated : Bool := false

abbrev SpecM := StateRefT SpecState CoreM

/-- Per-instance context while walking a body. -/
structure SpecCtx where
  inst : Instance
  /-- Type parameters of the instance ↦ their ground types. -/
  subst : FVarIdMap Expr
  /-- Type parameters of local polymorphic functions; they are instantiated
  per call of the local function, not here. -/
  localTypeVars : FVarIdSet := {}
  /-- Variables holding a statically known dictionary or a local function. -/
  static : FVarIdSet := {}

/-- Instantiate type parameters, beta-reduce, and drop universe levels
(representation never depends on them, so instances must not either). -/
def normType (subst : FVarIdMap Expr) (e : Expr) : CoreM Expr := do
  let e := e.replace fun
    | .fvar id => subst.get? id
    | _ => none
  let e ← Core.betaReduce e
  return e.replace fun
    | .const n (_ :: _) => some (.const n [])
    | _ => none

def SpecCtx.hasFree (ctx : SpecCtx) (e : Expr) : Bool :=
  e.hasAnyFVar fun id => !ctx.localTypeVars.contains id

def enqueue (inst : Instance) : SpecM Unit := do
  let s ← get
  if s.seen.contains inst then return
  if s.seen.size ≥ s.maxInstances then
    modify ({ · with truncated := true })
    return
  modify fun s => { s with seen := s.seen.insert inst, work := s.work.push inst }

def checkType (ctx : SpecCtx) (ty : Expr) (what : String) : SpecM Unit := do
  let ty' ← normType ctx.subst ty
  if ctx.hasFree ty' then
    modify fun s => { s with nonGround := s.nonGround.push s!"{ctx.inst.describe}: {what} : {ty'}" }
  else if hasRelevantAny (← get).table ty' then
    modify fun s => { s with anySites := s.anySites.push s!"{ctx.inst.describe}: {what} : {ty'}" }

/-- Record the instance a constant application needs. Returns whether all of
its instance arguments are statically known, or `none` when the application
cannot be instantiated (a type argument is missing or not ground). Constants
without a declaration (constructors) return `some true`. -/
def visitConstApp (ctx : SpecCtx) (f : Name) (args : Array (Arg .pure)) : SpecM (Option Bool) := do
  let some callee := (← get).decls.find? f | return some true
  let mut typeArgs := #[]
  let mut staticInsts := #[]
  for h : i in [:callee.params.size] do
    let p := callee.params[i]
    if isTypeFormerType p.type then
      match args[i]? with
      | some (.type e _) =>
        let e' ← normType ctx.subst e
        if ctx.hasFree e' then
          modify fun s => { s with nonGround := s.nonGround.push s!"{ctx.inst.describe}: type argument of {f} : {e'}" }
          return none
        typeArgs := typeArgs.push e'
      | some _ => typeArgs := typeArgs.push erasedExpr
      | none =>
        modify fun s => { s with nonGround := s.nonGround.push s!"{ctx.inst.describe}: partial application of {f} leaves type parameter {p.binderName} open" }
        return none
    else if (← isClass? p.type).isSome then
      staticInsts := staticInsts.push <| match args[i]? with
        | some (.fvar x) => ctx.static.contains x
        | _ => false
  enqueue { decl := f, typeArgs, staticInsts }
  return some (staticInsts.all id)

mutual
  partial def visitCode (ctx : SpecCtx) : Code .pure → SpecM Unit
    | .let d k => do visitCode (← visitLet ctx d) k
    | .fun d k _ => do
      visitFun ctx d
      visitCode { ctx with static := ctx.static.insert d.fvarId } k
    | .jp d k => do
      visitFun ctx d
      visitCode ctx k
    | .cases c => do
      for alt in c.alts do
        for p in alt.getParams do
          checkType ctx p.type s!"field {p.binderName} of {c.typeName}"
        visitCode ctx alt.getCode
    | _ => pure ()

  partial def visitFun (ctx : SpecCtx) (d : FunDecl .pure) : SpecM Unit := do
    let typeParams := d.params.filter (isTypeFormerType ·.type)
    if !typeParams.isEmpty then
      modify fun s => { s with polyLocalFuns := s.polyLocalFuns + 1 }
    let ctx := { ctx with localTypeVars := typeParams.foldl (·.insert ·.fvarId) ctx.localTypeVars }
    for p in d.params do
      unless isTypeFormerType p.type do
        checkType ctx p.type s!"param {p.binderName} of local {d.binderName}"
    visitCode ctx d.value

  partial def visitLet (ctx : SpecCtx) (d : LetDecl .pure) : SpecM SpecCtx := do
    checkType ctx d.type s!"let {d.binderName}"
    let markStatic (b : Bool) := if b then { ctx with static := ctx.static.insert d.fvarId } else ctx
    match d.value with
    | .const f _ args _ =>
      let insts ← visitConstApp ctx f args
      let isDict := (← isClass? d.type).isSome
      return markStatic (isDict && insts == some true)
    | .fvar g args =>
      if args.any (· matches .type ..) then
        modify fun s => { s with dictCalls := s.dictCalls + 1 }
        unless ctx.static.contains g do
          modify fun s => { s with dynamicDictCalls := s.dynamicDictCalls.push s!"{ctx.inst.describe}: {d.binderName}" }
      return ctx
    | .proj _ _ s _ => return markStatic (ctx.static.contains s)
    | _ => return ctx
end

/-- Instantiate `decl`'s type-former parameters with `typeArgs` (in parameter
order) and internalize the rest, as Lean's `mkSpecDecl` does: instantiated
parameters are dropped rather than internalized, because internalizing a
parameter would rebind its substitution entry to a fresh variable. -/
def instantiateDecl (decl : Decl .pure) (typeArgs : Array Expr) : CompilerM (Decl .pure) := do
  let typeParams := decl.params.filter (isTypeFormerType ·.type)
  let subst : FVarSubst .pure := (typeParams.zip typeArgs).foldl (init := {}) fun m (p, t) =>
    m.insert p.fvarId (if t.isErased then .erased else .type t)
  let go : Internalize.InternalizeM .pure (Decl .pure) := do
    let params ← (decl.params.filter (!isTypeFormerType ·.type)).mapM Internalize.internalizeParam
    let value ← decl.value.mapCodeM Internalize.internalizeCode
    return { decl with params, value }
  go.run' subst

def processInstance (inst : Instance) : SpecM Unit := do
  let some decl := (← get).decls.find? inst.decl | return
  match decl.value with
  | .extern _ =>
    modify fun s => { s with externInstances := s.externInstances.push inst }
  | .code _ =>
    modify fun s => { s with instances := s.instances.push inst }
    let table := (← get).table
    let decl ← (do retypeDecl table (← instantiateDecl decl inst.typeArgs) : CompilerM _).run (phase := .base)
    let .code code := decl.value | return
    let mut static : FVarIdSet := {}
    let mut k := 0
    for p in decl.params do
      if (← isClass? p.type).isSome then
        if inst.staticInsts.getD k false then static := static.insert p.fvarId
        k := k + 1
    let ctx : SpecCtx := { inst, subst := {}, static }
    for p in decl.params do
      checkType ctx p.type s!"param {p.binderName}"
    visitCode ctx code

/-- Compute all instances reachable from the program root. -/
def specializeDryRun (prog : Program) (table : RelevanceTable) (maxInstances := 50000) : CoreM SpecState := do
  let decls := (prog.decls ++ prog.externs).foldl (fun m d => m.insert d.name d) {}
  let act : SpecM Unit := do
    enqueue { decl := prog.root, typeArgs := #[], staticInsts := #[] }
    repeat
      let s ← get
      if h : s.work.size > 0 then
        let inst := s.work[s.work.size - 1]
        modify fun s => { s with work := s.work.pop }
        processInstance inst
      else break
  let ((), st) ← act.run { table, decls, maxInstances }
  return st

end LeanToReussir
