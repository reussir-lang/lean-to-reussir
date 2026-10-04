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

/-- `typedRef α`: the mono type lean2rr gives a reference (`ST.Ref σ α`,
which Lean's mono phase erases to `lcAny`) whose contents have the precise
mono type `α` (Stage 3 assigns it from `ST.Prim.mkRef` instances,
translation plan §4; Stage 4 represents it by a typed cell, §5.1). Not a
Lean constant: it only occurs in types lean2rr computes. -/
def typedRefName : Name := `_l2r.TypedRef

def mkTypedRef (α : Expr) : Expr := mkApp (mkConst typedRefName) α

/-- Does `t` mention `typedRef`? -/
def hasTypedRef (t : Expr) : Bool := (t.find? (·.isConstOf typedRefName)).isSome

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
    -- Already a mono type (see `typedRefName`).
    | .const n _ => if n == typedRefName then return mkAppN f args else visitConst f args
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

end LeanToReussir
