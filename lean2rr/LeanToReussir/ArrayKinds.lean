import Lean
import LeanToReussir.MonoTypesKeep

/-!
# Storage kinds of compact arrays

An `Array S` whose element type `S` is a scalar can be stored compactly, as
`RVec<k>` of its storage kind `k` (optimization `compact-arrays`;
`CompactArrays.lean` decides which kinds the program can store so, and the
lowering's `arrayStorage` uses the decision):

* `u8`: `UInt8`, `Bool`, and enumerations (inductives whose constructors
  have no relevant fields, lowered as a `[value]` enum without fields) with
  1 to 256 constructors, stored as their constructor index;
* `u16`: `UInt16`; `u32`: `UInt32` (and `Char`, whose mono type is
  `UInt32`); `u64`: `UInt64`, `USize`; `f32`: `Float32`; `f64`: `Float`.

`scalarKind?` decides from the mono type; the lowering's `arrayKindOf`
decides from the Reussir type, and the two agree (an enumeration here is
exactly a type `nominalType` gives the shape `enumLike`).
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- The storage kinds, in the order the docs list them. -/
def compactKinds : Array String := #["u8", "u16", "u32", "u64", "f32", "f64"]

/-- Types that are never enumerations here: the lowering gives them their
own representation (`lowerTypeApp`). -/
def notEnumTypes : List Name :=
  [``Unit, ``PUnit, ``lcVoid, ``lcErased, ``lcAny, ``Nat, ``Int, ``String, ``Thunk, ``Task,
   ``ByteArray, ``FloatArray, ``Array, ``IO.FS.Handle]

/-- The number of constructors of inductive `n` (its `_impl`, as
`lowerTypeApp`), if it is an enumeration: not a proposition, and every
field of every constructor erased (a type, a proof, the world), with the
parameters at `lcAny`, as `nominalType` computes the fields. -/
def enumCtorCount? (n : Name) : CoreM (Option Nat) := do
  if notEnumTypes.contains n then return none
  let env ← getEnv
  let ival ← match env.find? (n ++ `_impl), env.find? n with
    | some (.inductInfo iv), _ => pure iv
    | _, some (.inductInfo iv) => pure iv
    | _, _ => return none
  if ival.type.getForallBody.isProp then return none
  let params := Array.replicate ival.numParams anyExpr
  for ctorName in ival.ctors do
    let ctorTy ← getOtherDeclBaseType ctorName []
    let mut ty ← instantiateForall ctorTy params
    repeat
      match ty.headBeta with
      | .forallE _ d b _ =>
        let mono ← toMonoTypeKeep d
        unless mono.isErased || mono == mkConst ``lcVoid do return none
        ty := b.instantiate1 anyExpr
      | _ => break
  return some ival.ctors.length

/-- The storage kind of a compact array of mono element type `t`, if `t`
is a scalar (see the module comment). `cache` holds the answers for
inductives. -/
def scalarKind? (cache : IO.Ref (Std.HashMap Name (Option String))) (t : Expr) :
    CoreM (Option String) := do
  let .const n _ := t.consumeMData.headBeta.getAppFn | return none
  match n with
  | ``UInt8 | ``Bool => return some "u8"
  | ``UInt16 => return some "u16"
  | ``UInt32 => return some "u32"
  | ``UInt64 | ``USize => return some "u64"
  | ``Float32 => return some "f32"
  | ``Float => return some "f64"
  | _ =>
    if let some r := (← cache.get)[n]? then return r
    let r := match ← enumCtorCount? n with
      | some k => if 1 ≤ k && k ≤ 256 then some "u8" else none
      | none => none
    cache.modify (·.insert n r)
    return r

/-- Whether mono type `t` is a scalar with a storage kind, or mentions an
`Array S` of one (`Array (Array UInt8)`, `Option (Array UInt64)`): its
values can be or hold compact arrays. -/
partial def holdsCompactKind (cache : IO.Ref (Std.HashMap Name (Option String))) (t : Expr) :
    CoreM Bool := do
  if (← scalarKind? cache t).isSome then return true
  go t
where
  go (t : Expr) : CoreM Bool := do
    match t.consumeMData with
    | .forallE _ d b _ => return (← go d) || (← go b)
    | t@(.app ..) =>
      if t.isAppOfArity ``Array 1 then
        if (← scalarKind? cache t.appArg!).isSome then return true
      for a in t.getAppArgs do
        if ← go a then return true
      return false
    | _ => return false

end LeanToReussir
