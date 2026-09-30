import Lean
import LeanToReussir.Collect
import LeanToReussir.Relevance

/-!
# Stage 1: monomorphization

Turns the reachable part of a program's base-phase LCNF into a closed,
monomorphic program (translation plan §2):

* every declaration is copied once per list of type arguments it is used
  at — an *instance* — under a fresh name, so that Lean's passes in Stage 2
  only ever see these copies, never Lean's persisted polymorphic versions;
* instantiation is the substitution Lean's own specializer performs
  (`Specialize.mkSpecDecl`): type-former parameters are replaced by their
  arguments and dropped, and all types are re-normalized (beta);
* Lean's base `simp` then runs on each instance, which inlines statically
  known type-class instances and folds dictionary projections into direct
  calls;
* finally every call is redirected to the instance of its callee.

A type argument that is not statically known (it mentions a local type
variable, or it keeps growing under polymorphic recursion) is replaced by
`lcAny`; values of that type later use the uniform `Box` representation.
Nothing is rejected.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- An instance: a declaration and the (normalized, ground) arguments of its
type-former parameters, in parameter order. -/
structure InstKey where
  decl : Name
  typeArgs : Array Expr
  deriving BEq, Hashable, Inhabited

def InstKey.describe (k : InstKey) : String :=
  if k.typeArgs.isEmpty then toString k.decl
  else s!"{k.decl} [{", ".intercalate (k.typeArgs.toList.map toString)}]"

structure MonoConfig where
  /-- Type arguments larger than this (in expression nodes) are replaced by
  `lcAny`; this bounds instantiation under polymorphic recursion. -/
  maxTypeArgSize : Nat := 64
  /-- A declaration with more instances than this gets further instances at
  `lcAny` only. -/
  maxInstancesPerDecl : Nat := 128
  /-- Run Lean's base `simp` on each instance (dictionary folding). -/
  simp : Bool := true

structure MonoState where
  config : MonoConfig
  /-- Instance key ↦ fresh instance name. -/
  names : Std.HashMap InstKey Name := {}
  /-- Instances per original declaration, for the per-declaration cap. -/
  perDecl : NameMap Nat := {}
  work : Array (InstKey × Name) := #[]
  /-- Instance declarations with code, in creation order. -/
  decls : Array (Decl .pure) := #[]
  /-- Extern instances: polymorphic externs at ground types. -/
  externs : Array (Decl .pure) := #[]
  /-- Monomorphic externs referenced (kept under their own names). -/
  monoExterns : NameSet := {}
  /-- Instance name ↦ key, for diagnostics and statistics. -/
  keys : NameMap InstKey := {}
  /-- Number of type arguments replaced by `lcAny`. -/
  uniformArgs : Nat := 0

abbrev MonoM := StateRefT MonoState CoreM

/-- Replace universe levels by `0`: representation never depends on them. -/
def eraseLevels (e : Expr) : Expr :=
  e.replace fun
    | .const n (_ :: _) => some (.const n [])
    | .sort (.succ _) => some (.sort levelOne)
    | .sort (.param _) | .sort (.max ..) | .sort (.imax ..) => some (.sort levelOne)
    | _ => none

/-- Normalize a type argument: beta, erase levels, and replace anything that
is not statically known by `lcAny`. -/
def normTypeArg (e : Expr) : MonoM Expr := do
  let e ← Core.betaReduce e
  let e := eraseLevels e
  let known := !e.hasFVar && !e.hasLooseBVars && !e.hasMVar
  if !known || e.approxDepth.toNat > (← get).config.maxTypeArgSize then
    modify fun s => { s with uniformArgs := s.uniformArgs + 1 }
    return anyExpr
  return e

/-- A fresh name for an instance of `decl`. Appending a numeric component
keeps the original name readable in dumps and cannot clash with any Lean
declaration. -/
def freshInstName (decl : Name) (k : Nat) : Name :=
  .num (decl ++ `_l2r) k

/-- Look up (or create and enqueue) the instance for `key`. -/
def instanceName (key : InstKey) : MonoM Name := do
  if let some n := (← get).names[key]? then return n
  let count := (← get).perDecl.getD key.decl 0
  let key ← if count ≥ (← get).config.maxInstancesPerDecl && !key.typeArgs.all (· == anyExpr) then
      modify fun s => { s with uniformArgs := s.uniformArgs + key.typeArgs.size }
      pure { key with typeArgs := key.typeArgs.map fun _ => anyExpr }
    else pure key
  if let some n := (← get).names[key]? then return n
  let n := freshInstName key.decl count
  modify fun s => { s with
    names := s.names.insert key n
    perDecl := s.perDecl.insert key.decl (count + 1)
    work := s.work.push (key, n)
    keys := s.keys.insert n key }
  return n

/-- Positions of type-former parameters. -/
def typeParamPositions (decl : Decl .pure) : Array Nat := Id.run do
  let mut out := #[]
  for h : i in [:decl.params.size] do
    if isTypeFormerType decl.params[i].type then out := out.push i
  return out

/-- Redirect a constant application to the instance of its callee. Returns
`none` when the constant is not a declaration we instantiate (constructors,
monomorphic externs). -/
def renameApp (f : Name) (args : Array (Arg .pure)) : MonoM (Option (Name × Array (Arg .pure))) := do
  let some callee ← getBaseDecl? f | return none
  let positions := typeParamPositions callee
  if let .extern _ := callee.value then
    if positions.isEmpty then
      modify fun s => { s with monoExterns := s.monoExterns.insert f }
      return none
  let mut typeArgs := #[]
  for i in positions do
    match args[i]? with
    | some (.type e _) => typeArgs := typeArgs.push (← normTypeArg e)
    | some _ => typeArgs := typeArgs.push erasedExpr
    -- A partial application that stops before a type parameter: that
    -- parameter is kept (see `instantiate`), so it has no argument here.
    | none => typeArgs := typeArgs.push anyExpr
  let n ← instanceName { decl := f, typeArgs }
  let args := args.zipIdx.filterMap fun (a, i) => if positions.contains i then none else some a
  return some (n, args)

partial def renameCode : Code .pure → MonoM (Code .pure)
  | .let d k => do
    let d ← match d.value with
      | .const f _ args _ =>
        match ← renameApp f args with
        | some (n, args') => pure { d with value := .const n [] args' }
        | none => pure d
      | _ => pure d
    return .let d (← renameCode k)
  | .fun d k _ => do
    let value ← renameCode d.value
    return .fun (FunDecl.mk d.fvarId d.binderName d.params d.type value) (← renameCode k)
  | .jp d k => do
    let value ← renameCode d.value
    return .jp (FunDecl.mk d.fvarId d.binderName d.params d.type value) (← renameCode k)
  | .cases c => do
    let alts ← c.alts.mapM fun alt => do
      match alt with
      | .alt ctor ps code _ => return .alt ctor ps (← renameCode code)
      | .default code => return .default (← renameCode code)
      | other => return other
    return .cases ⟨c.typeName, c.resultType, c.discr, alts⟩
  | code => return code

/-- Build the instance of `decl` at `typeArgs` as Lean's `mkSpecDecl` does:
instantiate universe levels (at `0`) and type parameters, drop the
instantiated parameters, and internalize the rest. A type parameter whose
argument is `lcAny` because it was never supplied (partial application) is
kept as an erased parameter, so that the instance's arity matches what
callers pass. -/
def instantiate (decl : Decl .pure) (name : Name) (typeArgs : Array Expr) (keepMissing : Bool) :
    CompilerM (Decl .pure) := do
  let us := decl.levelParams.map fun _ => levelZero
  let positions := typeParamPositions decl
  -- Returns the kept (internalized) parameters and, per original parameter,
  -- the expression it is instantiated with (for the result type).
  let go : Internalize.InternalizeM .pure (Array (Param .pure) × Array Expr) := do
    let mut kept := #[]
    let mut instArgs := #[]
    for h : i in [:decl.params.size] do
      let p := decl.params[i]
      let p := { p with type := eraseLevels (p.type.instantiateLevelParamsNoCache decl.levelParams us) }
      match positions.idxOf? i with
      | some j =>
        let t := typeArgs[j]!
        if keepMissing && t == anyExpr then
          let p' ← Internalize.internalizeParam { p with type := erasedExpr }
          kept := kept.push p'
          instArgs := instArgs.push anyExpr
        else
          modify fun s => s.insert p.fvarId (if t.isErased then .erased else .type t)
          instArgs := instArgs.push t
      | none =>
        let p' ← Internalize.internalizeParam p
        kept := kept.push p'
        instArgs := instArgs.push (.fvar p'.fvarId)
    return (kept, instArgs)
  let code := match decl.value with
    | .code c => c.instantiateValueLevelParams decl.levelParams us
    | .extern _ => .return default
  let ((params, args), value) ← (do
      let r ← go
      let v ← match decl.value with
        | .code _ => pure (DeclValue.code (← Internalize.internalizeCode code))
        | .extern e => pure (DeclValue.extern e)
      return (r, v) : Internalize.InternalizeM .pure _).run' {}
  let declType := eraseLevels (decl.type.instantiateLevelParamsNoCache decl.levelParams us)
  let retType ← Core.betaReduce (← instantiateForall declType args)
  let type ← mkForallParams params retType
  return { decl with name, levelParams := [], params, type, value, inlineAttr? := decl.inlineAttr? }

/-- Build an extern instance. Extern declarations have no body, and their
parameter list is not in internalized form, so the instance signature is
built from the declaration's type instead: type-former binders are
instantiated, the others become fresh parameters (borrow annotations are
dropped: Reussir's ownership analysis decides borrowing). -/
def instantiateExtern (decl : Decl .pure) (name : Name) (typeArgs : Array Expr) :
    CompilerM (Decl .pure) := do
  let us := decl.levelParams.map fun _ => levelZero
  let positions := typeParamPositions decl
  let mut ty := eraseLevels (decl.type.instantiateLevelParamsNoCache decl.levelParams us)
  let mut params : Array (Param .pure) := #[]
  for h : i in [:decl.params.size] do
    let .forallE n d b _ := ty.headBeta
      | throwError "lean2rr: extern {decl.name} has fewer binders than parameters"
    let d := d.consumeMData
    match positions.idxOf? i with
    | some j =>
      let t := typeArgs[j]!
      if t == anyExpr then
        -- never supplied (partial application): keep as an erased parameter
        let p ← mkParam n erasedExpr false
        params := params.push p
        ty := b.instantiate1 anyExpr
      else
        ty := b.instantiate1 t
    | none =>
      let p ← mkParam n (← Core.betaReduce d) false
      params := params.push p
      ty := b.instantiate1 (.fvar p.fvarId)
  let retType ← Core.betaReduce ty
  let type ← mkForallParams params retType
  return { decl with name, levelParams := [], params, type }

/-- Process one instance: instantiate, simplify, rename, record. -/
def monoInstance (key : InstKey) (name : Name) : MonoM Unit := do
  let some decl ← getBaseDecl? key.decl
    | throwError "lean2rr: no base declaration for {key.decl} (internal error)"
  let keepMissing := true
  match decl.value with
  | .extern _ =>
    let inst ← (instantiateExtern decl name key.typeArgs).run (phase := .base)
    modify fun s => { s with externs := s.externs.push inst }
  | .code _ =>
    let doSimp := (← get).config.simp
    let inst ← (do
        let inst ← instantiate decl name key.typeArgs keepMissing
        if doSimp then inst.simp {} else pure inst : CompilerM _).run (phase := .base)
    let .code code := inst.value | unreachable!
    let code ← renameCode code
    modify fun s => { s with decls := s.decls.push { inst with value := .code code } }

/-- Run Stage 1 from `root`. The root instance is `(root, [])`. -/
def monomorphize (root : Name) (config : MonoConfig := {}) : CoreM (Name × MonoState) := do
  let act : MonoM Name := do
    let rootName ← instanceName { decl := root, typeArgs := #[] }
    repeat
      let s ← get
      if h : s.work.size > 0 then
        let (key, name) := s.work[s.work.size - 1]
        modify fun s => { s with work := s.work.pop }
        monoInstance key name
      else break
    return rootName
  act.run { config }

end LeanToReussir
