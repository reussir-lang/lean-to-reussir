import Lean

/-!
# Relevant type parameters

A parameter of an inductive type is *relevant* when it can influence the
runtime representation of the type's values: some constructor has a data
field (not a proof, not a type) whose type mentions the parameter in a
relevant position. Everything else is a phantom as far as code generation is
concerned. Examples:

* `List α`, `Option α`: `α` is relevant.
* `EST.Out ε σ α`: `σ` only occurs in the `Void σ` state field, which carries
  no data, so only `ε` and `α` are relevant.
* `String.Pos s`: `s` is a value, never relevant.

The distinction matters to Stage 3: an `lcAny` in a phantom position is
harmless, while an `lcAny` in a relevant position is a value of statically
unknown type (`MonoRetype.isUnknown`, `normTy`). Stage 4 does not use it:
an inductive has one Reussir type whatever its arguments.

Relevance is the least fixpoint of "occurs relevantly in a data field",
computed over a set of inductives. Builtin runtime types whose Lean model hides
their payload (`ST.Ref` stores its value behind an opaque pointer) are fixed by
`builtinRelevance`.
-/

namespace LeanToReussir
open Lean Meta

abbrev RelevanceTable := NameMap (Array Bool)

/-- Runtime types whose element parameter is data even though the Lean-level
model does not show it as a field. -/
def builtinRelevance : List (Name × Array Bool) :=
  [(``ST.Ref, #[false, true]), (``Array, #[true]), (``Thunk, #[true]), (``Task, #[true])]

/-- Free variables that occur in a relevant position of type `ty`. Function
types are treated conservatively: everything they mention is relevant. -/
partial def relevantFVars (table : RelevanceTable) (ty : Expr) : MetaM FVarIdSet := do
  let ty ← whnf ty
  match ty with
  | .fvar id => return ({} : FVarIdSet).insert id
  | .forallE .. | .lam .. => return (collectFVars {} ty).fvarSet
  | .app .. =>
    match ty.getAppFn with
    | .const name _ =>
      match table.find? name with
      | some rel =>
        let args := ty.getAppArgs
        let mut acc : FVarIdSet := {}
        for h : i in [:args.size] do
          if rel.getD i false then
            for id in ← relevantFVars table args[i] do
              acc := acc.insert id
        return acc
      | none => return (collectFVars {} ty).fvarSet
    | _ => return (collectFVars {} ty).fvarSet
  | _ => return {}

/-- One constructor's contribution: which inductive parameters occur relevantly
in its data fields, and whether a data field depends on a type-valued field
(an existential, which no monomorphic representation can express). -/
def ctorRelevance (table : RelevanceTable) (ctor : ConstructorVal) : MetaM (Array Bool × Bool) :=
  forallTelescopeReducing ctor.type fun xs _ => do
    let params := xs[:ctor.numParams].toArray
    let fields := xs[ctor.numParams:].toArray
    let mut typeFields : FVarIdSet := {}
    let mut rel := Array.replicate params.size false
    let mut existential := false
    for field in fields do
      let ty ← inferType field
      if ← isProp ty then continue
      -- Predicate-valued fields (`Pred : α → Prop`) are erased like proofs;
      -- only genuinely type-valued fields can make another field existential.
      if ← isPropFormerType ty then continue
      if ← isTypeFormerType ty then
        typeFields := typeFields.insert field.fvarId!
        continue
      let fvs ← relevantFVars table ty
      for h : i in [:params.size] do
        if fvs.contains params[i].fvarId! then rel := rel.set! i true
      if fvs.toList.any typeFields.contains then existential := true
    return (rel, existential)

/-- Relevance of every parameter of `ind`, given the current approximation. -/
def inductiveRelevance (table : RelevanceTable) (ind : Name) : MetaM (Array Bool × Bool) := do
  let .inductInfo ival ← getConstInfo ind | return (#[], false)
  let mut rel := Array.replicate ival.numParams false
  let mut existential := false
  for ctorName in ival.ctors do
    let (r, e) ← ctorRelevance table (← getConstInfoCtor ctorName)
    rel := rel.zipWith (· || ·) r
    existential := existential || e
  return (rel, existential)

/-- Least-fixpoint relevance for a set of inductive types (which should be
closed under constructor field types; unknown heads are treated as fully
relevant). Also returns the inductives with existential fields. -/
partial def computeRelevance (inds : Array Name) : MetaM (RelevanceTable × NameSet) := do
  let builtins := builtinRelevance.foldl (fun t (n, r) => t.insert n r) {}
  let mut table : RelevanceTable := builtins
  for ind in inds do
    unless table.contains ind do
      let .inductInfo ival ← getConstInfo ind | continue
      table := table.insert ind (Array.replicate ival.numParams false)
  let mut existential : NameSet := {}
  let mut changed := true
  while changed do
    changed := false
    for ind in inds do
      if builtins.contains ind then continue
      let (rel, ex) ← inductiveRelevance table ind
      if ex then existential := existential.insert ind
      if rel != (table.find? ind).getD #[] then
        table := table.insert ind rel
        changed := true
  return (table, existential)

/-- Whether `lcAny` occurs in a relevant position of an LCNF type, i.e. the
type describes data whose representation is statically unknown. -/
partial def hasRelevantAny (table : RelevanceTable) (e : Expr) : Bool :=
  match e with
  | .const ``lcAny _ => true
  | .forallE _ d b _ => hasRelevantAny table d || hasRelevantAny table b
  | .app .. =>
    let args := e.getAppArgs
    match e.getAppFn with
    -- An erased type applied to arguments still classifies erased values.
    | .const ``lcErased _ => false
    | .const name _ =>
      match table.find? name with
      | some rel => (args.zipIdx.any fun (a, i) => rel.getD i true && hasRelevantAny table a)
      | none => args.any (hasRelevantAny table)
    | f => hasRelevantAny table f || args.any (hasRelevantAny table)
  | _ => false

end LeanToReussir
