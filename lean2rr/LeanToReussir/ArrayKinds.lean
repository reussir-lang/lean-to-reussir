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

/-! ## Pointer kinds (optimization `typed-arrays`, clean step B1)

An `Array X` whose element type `X` is a one-word counted type is stored
typed, `RVec<T>` of `X`'s own Reussir type `T`, when the whole-program check
allows it. The *pointer kind* of `X` names the Reussir type the lowering
gives `X`, so that two element types of one kind have one representation:

* `Nat`, `Int`: `Nat`, `Int` (none under `--int-backend rcgmp` without
  `--rcgmp-type-args`, `natInt` below: an `RVec<Nat>` would pass `Nat` at
  the type arguments of the runtime's array functions, where Reussir gives
  them a raw handle and releases it after the call; `isFfiTypeArgTy`);
  `String`: `LStr`;
* `I:<name>`: an inductive that the lowering makes a shared record or enum
  (`sharedInductive?`); rule 1 gives every instance (`List Nat`,
  `List String`) the one type of the inductive;
* `A(<k>)`: an `Array Y`, where `k` is `Y`'s kind (storage or pointer
  kind), or `box` when `Y` has none (`RVec<RVec<…>>`).

Function types, `ByteArray`, `FloatArray`, thunks, tasks, handles,
references and `lcAny` have no pointer kind (`noPtrKindTypes`). -/

/-- Types without a pointer kind of the inductive form: the lowering gives
them a representation of its own (`lowerTypeApp`: a scalar, the unit, a
box, a runtime cell or array), or the runtime's glue takes arrays of them
as arrays of boxes (`ByteArray`: the event loop's sends). `Nat`, `Int`,
`String` and `Array` have kinds of their own (`ptrKind?`). -/
def noPtrKindTypes : List Name :=
  [``Unit, ``PUnit, ``lcVoid, ``lcErased, ``lcAny, ``Thunk, ``Task, ``ByteArray, ``FloatArray,
   ``IO.FS.Handle, ``ST.Ref, ``Bool, ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize, ``Float,
   ``Float32, ``Nat, ``Int, ``String, ``Array]

/-- The name that stands for inductive type head `n` in its pointer kind, if
the lowering (`lowerTypeApp`, `nominalType`) makes the values of `n` a
shared record or enum (one pointer): an inductive (its `_impl` for a type
with computed fields; `n` and `n._impl` have one kind) that is not a
proposition, with a relevant field in some constructor (else it is an
enumeration, a `[value]` enum), and not one constructor with exactly one
relevant field (a `[value]` struct under `value-structs`; such a structure
is never typed, whether or not the pass is on). -/
def sharedInductive? (n : Name) : CoreM (Option Name) := do
  if noPtrKindTypes.contains n then return none
  let env ← getEnv
  let (key, ival) ← match env.find? (n ++ `_impl), env.find? n with
    | some (.inductInfo iv), _ => pure (n, iv)
    | _, some (.inductInfo iv) => pure ((match n with | .str p "_impl" => p | _ => n), iv)
    | _, _ => return none
  if ival.type.getForallBody.isProp then return none
  let params := Array.replicate ival.numParams anyExpr
  let mut fieldsPerCtor : Array Nat := #[]
  for ctorName in ival.ctors do
    let ctorTy ← getOtherDeclBaseType ctorName []
    let mut ty ← instantiateForall ctorTy params
    let mut k := 0
    repeat
      match ty.headBeta with
      | .forallE _ d b _ =>
        let mono ← toMonoTypeKeep d
        unless mono.isErased || mono == mkConst ``lcVoid do k := k + 1
        ty := b.instantiate1 anyExpr
      | _ => break
    fieldsPerCtor := fieldsPerCtor.push k
  if fieldsPerCtor.all (· == 0) then return none
  if fieldsPerCtor == #[1] then return none
  return some key

/-- The key of inductive `n`'s pointer kind in the cache that `scalarKind?`
uses for storage kinds (the one cache holds both). -/
def ptrKindCacheKey (n : Name) : Name := .str n "_l2r_ptrkind"

mutual
  /-- The kind of array element type `t`: its storage kind (`scalarKind?`)
  or, with `ptr` (`typed-arrays`), its pointer kind (`ptrKind?`; `Nat` and
  `Int` have one only with `natInt`). -/
  partial def elemKind? (cache : IO.Ref (Std.HashMap Name (Option String))) (t : Expr) (ptr : Bool)
      (natInt : Bool) : CoreM (Option String) := do
    if let some k ← scalarKind? cache t then return some k
    unless ptr do return none
    ptrKind? cache t natInt

  /-- The pointer kind of array element type `t` (see above); `Nat` and
  `Int` have one only with `natInt` (`LowerCtx.natIntTypeArgs`: not under
  `--int-backend rcgmp` without `--rcgmp-type-args`). -/
  partial def ptrKind? (cache : IO.Ref (Std.HashMap Name (Option String))) (t : Expr) (natInt : Bool) :
      CoreM (Option String) := do
    let t := t.consumeMData.headBeta
    if t.isForall then return none
    let .const n _ := t.getAppFn | return none
    match n with
    | ``Nat => return if natInt then some "Nat" else none
    | ``Int => return if natInt then some "Int" else none
    | ``String => return some "LStr"
    | ``Array =>
      unless t.getAppNumArgs == 1 do return none
      return some s!"A({(← elemKind? cache t.appArg! true natInt).getD "box"})"
    | _ =>
      let ck := ptrKindCacheKey n
      if let some r := (← cache.get)[ck]? then return r
      let r := (← sharedInductive? n).map fun k => s!"I:{k}"
      cache.modify (·.insert ck r)
      return r
end

/-- The binder names of the source and the result array of a split `map`
instance's own parameters (`buildSplit`), by which `revertPtrSplits`
finds them. A name with a numeric part after a plain string is no name of
user code (an identifier has none; a hygienic name has a `_@` part), so
a captured variable named `src` or `dst`, which Lean's specializer puts
first among the loop's parameters with its user name, cannot match. -/
def splitSrcName : Name := .num (.str .anonymous "_l2r_split_src") 0
def splitDstName : Name := .num (.str .anonymous "_l2r_split_dst") 0

/-- Whether kind `k` is a pointer kind (not one of the storage kinds). -/
def isPtrKind (k : String) : Bool := !compactKinds.contains k

/-- Whether mono type `t` is a scalar with a storage kind, or mentions an
`Array S` of one (`Array (Array UInt8)`, `Option (Array UInt64)`): its
values can be or hold compact arrays. With `ptr` (`typed-arrays`), also a
type with a pointer kind, or one that mentions an array whose element type
has one (`Array String`, `Option (Array Point)`; `natInt` as `ptrKind?`). -/
partial def holdsCompactKind (cache : IO.Ref (Std.HashMap Name (Option String))) (t : Expr)
    (ptr : Bool := false) (natInt : Bool := true) : CoreM Bool := do
  if (← elemKind? cache t ptr natInt).isSome then return true
  go t
where
  go (t : Expr) : CoreM Bool := do
    match t.consumeMData with
    | .forallE _ d b _ => return (← go d) || (← go b)
    | t@(.app ..) =>
      if t.isAppOfArity ``Array 1 then
        if (← elemKind? cache t.appArg! ptr natInt).isSome then return true
      for a in t.getAppArgs do
        if ← go a then return true
      return false
    | _ => return false

end LeanToReussir
