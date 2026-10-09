import Lean
import LeanToReussir.Relevance

/-!
# Re-typing instantiated code

After a declaration is instantiated at ground types (`Decl.internalize` with
its type parameters substituted), many binder types can be made precise that
Lean's own inference left as `lcAny` — typically the result of applying a
polymorphic local function, or a join-point parameter. This pass recomputes
every binder type that still has `lcAny` in a relevant position:

* a `let` takes the type LCNF infers for its value;
* a `cases` alternative parameter takes its constructor field type,
  instantiated with the discriminant's type arguments;
* a join-point parameter takes the type of its jump arguments, and a local
  function parameter the type of its direct application arguments, provided
  all known candidates agree.

Refining one binder can make others inferable, so the pass iterates to a
fixpoint. Binders that stay unknown are exactly the places that need the uniform
`Box` representation; the caller reports them.

The pass keeps LCNF's local context in sync (`modifyLCtx`) because LCNF type
inference reads binder types from it.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Reader: relevance table. State: whether any binder type changed. -/
abbrev RetypeM := ReaderT RelevanceTable (StateRefT Bool CompilerM)

def isUnknownType (ty : Expr) : RetypeM Bool :=
  return hasRelevantAny (← read) ty

/-- The common type of the known candidates, if they agree. -/
def agreeingType (cands : Array Expr) : Option Expr :=
  match cands[0]? with
  | some t => if cands.all (eqvTypes · t) then some t else none
  | none => none

def setParamType (p : Param .pure) (ty : Expr) : RetypeM (Param .pure) := do
  let p := { p with type := ty }
  modifyLCtx (·.addParam p)
  set true
  return p

/-- Types of `args`, dropping those that are themselves unknown. A `◾`
argument (type `lcErased`) is a placeholder that fits any type, so it is
no candidate either: `◾` arguments alone do not refine a parameter to
`lcErased` (as `MonoRetype.refineTo?`, which never refines to `◾`). -/
def knownArgTypes (args : Array (Arg .pure)) (i : Nat) : RetypeM (Option Expr) := do
  let some a := args[i]? | return none
  let t ← a.inferType
  return if t.consumeMData.isErased || (← isUnknownType t) then none else some t

def refineLet (d : LetDecl .pure) : RetypeM (LetDecl .pure) := do
  unless ← isUnknownType d.type do return d
  let ty ← d.value.inferType
  if ← isUnknownType ty then return d
  let d := { d with type := ty }
  modifyLCtx (·.addLetDecl d)
  set true
  return d

/-- Refine the parameters of a `cases` alternative from the constructor's
field types instantiated at the discriminant's type arguments. -/
def refineAltParams (discr : FVarId) (ctor : Name) (ps : Array (Param .pure)) :
    RetypeM (Array (Param .pure)) := do
  unless ← ps.anyM (isUnknownType ·.type) do return ps
  let discrTy := (← getType discr).headBeta
  let some (.ctorInfo cinfo) := (← getEnv).find? ctor | return ps
  let args := discrTy.getAppArgs
  unless discrTy.getAppFn.isConst && args.size ≥ cinfo.numParams do return ps
  let mut ty ← instantiateForall (← getOtherDeclBaseType ctor []) args[:cinfo.numParams]
  let mut out := #[]
  for p in ps do
    match ty.headBeta with
    | .forallE _ d b _ =>
      let p ← if (← isUnknownType p.type) && !(← isUnknownType d) && !d.hasLooseBVars
        then setParamType p d else pure p
      out := out.push p
      ty := b.instantiate1 (.fvar p.fvarId)
    | _ => out := out.push p
  return out

/-- Argument lists of every `jmp` to `jp` in `code`. -/
partial def jmpArgs (jp : FVarId) : Code .pure → Array (Array (Arg .pure)) → Array (Array (Arg .pure))
  | .jmp f args, acc => if f == jp then acc.push args else acc
  | .let _ k, acc => jmpArgs jp k acc
  | .fun d k _, acc | .jp d k, acc => jmpArgs jp k (jmpArgs jp d.value acc)
  | .cases c, acc => c.alts.foldl (fun acc alt => jmpArgs jp alt.getCode acc) acc
  | _, acc => acc

/-- Argument lists of every direct application of local function `f` in `code`. -/
partial def appArgs (f : FVarId) : Code .pure → Array (Array (Arg .pure)) → Array (Array (Arg .pure))
  | .let d k, acc =>
    let acc := match d.value with
      | .fvar g args => if g == f then acc.push args else acc
      | _ => acc
    appArgs f k acc
  | .fun d k _, acc | .jp d k, acc => appArgs f k (appArgs f d.value acc)
  | .cases c, acc => c.alts.foldl (fun acc alt => appArgs f alt.getCode acc) acc
  | _, acc => acc

mutual
  partial def retypeCode : Code .pure → RetypeM (Code .pure)
    | .let d k => do
      let d ← refineLet d
      return .let d (← retypeCode k)
    | .fun d k _ => do
      let k ← retypeCode k
      let d ← retypeFun d (appArgs d.fvarId k #[])
      return .fun d k
    | .jp d k => do
      let k ← retypeCode k
      let d ← retypeFun d (jmpArgs d.fvarId k #[])
      return .jp d k
    | .cases c => do
      let alts ← c.alts.mapM fun alt => do
        match alt with
        | .alt ctor ps code _ =>
          let ps ← refineAltParams c.discr ctor ps
          return .alt ctor ps (← retypeCode code)
        | .default code => return .default (← retypeCode code)
        | other => return other
      return .cases ⟨c.typeName, c.resultType, c.discr, alts⟩
    | code => return code

  /-- Refine a local function or join point from the arguments it receives,
  then its body, then recompute its type. -/
  partial def retypeFun (d : FunDecl .pure) (argLists : Array (Array (Arg .pure))) :
      RetypeM (FunDecl .pure) := do
    let mut params := d.params
    for i in [:params.size] do
      let p := params[i]!
      if ← isUnknownType p.type then
        let cands ← argLists.filterMapM (knownArgTypes · i)
        if let some t := agreeingType cands then
          params := params.set! i (← setParamType p t)
    let value ← retypeCode d.value
    let type ← mkForallParams params (← value.inferType)
    let d' := FunDecl.mk d.fvarId d.binderName params type value
    modifyLCtx (·.addFunDecl d')
    unless eqvTypes type d.type do set true
    return d'
end

/-- Re-type an internalized declaration to a fixpoint (bounded). -/
def retypeDecl (table : RelevanceTable) (decl : Decl .pure) : CompilerM (Decl .pure) := do
  let .code code := decl.value | return decl
  let mut code := code
  for _ in [:8] do
    let (c, changed) ← (retypeCode code).run table |>.run false
    code := c
    unless changed do break
  return { decl with value := .code code }

end LeanToReussir
