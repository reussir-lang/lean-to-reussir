import Lean

/-!
# Mono types that keep constant type families

Lean's `toMonoType` erases every type-former argument of an inductive to
`lcAny`: `Std.HashMap Nat Nat` is `DHashMap Nat (fun _ => Nat)`, whose
buckets are `AssocList Nat (fun _ => Nat)`, and mono makes that
`AssocList Nat lcAny`, so the map's values lose their type. `toMonoTypeKeep`
is `toMonoType` except that a *closed* type-former argument is kept when it
does not make the type dependent: a constant family `fun _ … _ => T` (kept
with `T` converted), or a type constructor such as `List` (also after eta
reduction: `fun n => Fin n` is `Fin`). A family whose body mentions its
variable (`fun b => cond b Nat String`) still becomes `lcAny`, as in Lean:
its values need not have a single representation. A value index does not
count: Lean's base code already writes `Fin (n + 1)` as `Fin lcAny`, so
`fun n => Fin (n + 1)` is a constant family and is kept.

Everywhere lean2rr computes mono types itself (Stage 2's `toMono`,
constructor fields, Stage 3) it uses this function, so the types agree.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- The type-former argument `arg` as kept in a mono type, if it is closed
and not dependent. -/
partial def keepFormer? (arg : Expr) (conv : Expr → CoreM Expr) : CoreM (Option Expr) := do
  let arg := arg.headBeta.eta
  if arg.hasFVar || arg.hasLooseBVars || arg.hasMVar then return none
  -- Strip the binders; a constant family's body does not mention them.
  let rec strip (e : Expr) (n : Nat) : Expr × Nat :=
    match e with
    | .lam _ _ b _ => strip b (n + 1)
    | _ => (e, n)
  let (body, n) := strip arg 0
  if n == 0 then return some arg
  if body.hasLooseBVars then return none
  let body ← conv body
  let mut out := body
  for _ in [:n] do out := .lam `_ erasedExpr out .default
  return some out

/-- `toMonoType` keeping closed, non-dependent type-former arguments. -/
partial def toMonoTypeKeep (type : Expr) : CoreM Expr := do
  let type := type.headBeta
  match type with
  | .const .. => visitApp type #[]
  | .app .. => type.withApp visitApp
  | .forallE n d b bi =>
    let monoB ← toMonoTypeKeep (b.instantiate1 anyExpr)
    match monoB with
    | .const ``lcErased _ => return erasedExpr
    | _ => return .forallE n (← toMonoTypeKeep d) monoB bi
  | .sort _ => return erasedExpr
  | .mdata d b => return .mdata d (← toMonoTypeKeep b)
  | _ => return anyExpr
where
  visitApp (f : Expr) (args : Array Expr) : CoreM Expr := do
    match f with
    | .const ``lcErased _ => return erasedExpr
    | .const ``lcAny _ => return anyExpr
    | .const ``Decidable _ => return mkConst ``Bool
    -- "Any object" (a one-field structure over `Nat`, which mono would
    -- unwrap): values of every type are cast to it, so its representation
    -- is the uniform one, in data structures as in library code.
    | .const ``NonScalar _ | .const ``PNonScalar _ => return anyExpr
    | .const .. => visitConst f args
    | _ => return anyExpr
  visitConst (f : Expr) (args : Array Expr) : CoreM Expr := do
    match f with
    | .const declName us =>
      if let some info ← hasTrivialStructure? declName then
        let ctorType ← getOtherDeclBaseType info.ctorName []
        toMonoTypeKeep (getParamTypes (← instantiateForall ctorType args[*...info.numParams]))[info.fieldIdx]!
      else
        let mut result := mkConst declName
        let mut type ← getOtherDeclBaseType declName us
        if type.isErased then return erasedExpr
        for arg in args do
          let .forallE _ d b _ := type.headBeta | return anyExpr
          let arg := arg.headBeta
          if d matches .const ``lcErased _ | .sort _ then
            result := mkApp result (← toMonoTypeKeep arg)
          else if isTypeFormerType d then
            -- The difference with Lean's `toMonoType`.
            result := mkApp result ((← keepFormer? arg toMonoTypeKeep).getD anyExpr)
          else
            result := mkApp result anyExpr
          type := b.instantiate1 arg
        return result
    | _ => return anyExpr

/-! ## Types with computed fields

A type `T` with computed fields (`Lean.Name`) has an implementation
inductive `T._impl`, whose constructors `T.c._impl` also store the computed
fields; `T.casesOn` is `implemented_by` a match on `T._impl`
(`Lean.Elab.ComputedFields`). Lean's `ToMono` (and lean2rr's `TypedToMono`)
decide by that `implemented_by`, not by the name: a program can declare a
type named `T._impl` of its own next to a `T` without computed fields
(test `RtNameImplCollide`). Every place that maps a type to its
implementation asks these functions, so they all agree with `TypedToMono`. -/

/-- The implementation inductive `n._impl` of `n`, if `n` is a type with
computed fields (`n.casesOn` has an `implemented_by`). -/
def computedImpl? (env : Environment) (n : Name) : Option InductiveVal :=
  if (getImplementedBy? env (mkCasesOnName n)).isSome then
    match env.find? (n ++ `_impl) with
    | some (.inductInfo iv) => some iv
    | _ => none
  else none

/-- The type with computed fields that `n` implements, if `n` is such an
implementation (`computedImpl?`). -/
def implOf? (env : Environment) (n : Name) : Option Name :=
  match n with
  | .str p "_impl" => if (computedImpl? env p).any (·.name == n) then some p else none
  | _ => none

/-- The inductive whose constructors build the values of type head `n`:
its implementation for a type with computed fields (`computedImpl?`), else
`n` itself if it is an inductive. -/
def reprInductive? (env : Environment) (n : Name) : Option InductiveVal :=
  match computedImpl? env n with
  | some iv => some iv
  | none =>
    match env.find? n with
    | some (.inductInfo iv) => some iv
    | _ => none

/-- Whether `m` and `n` name one inductive: the same name, or a type with
computed fields and its implementation (`computedImpl?`). -/
def sameInductive (env : Environment) (m n : Name) : Bool :=
  m == n || implOf? env m == some n || implOf? env n == some m

end LeanToReussir
