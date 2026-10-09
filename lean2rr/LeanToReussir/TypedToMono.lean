/-
Derived from Lean 4.33's `src/Lean/Compiler/LCNF/ToMono.lean` (unchanged in 4.34)
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean
import LeanToReussir.MonoTypesKeep

/-!
# Stage 2's `toMono`, keeping constant type families

Lean's `toMono` pass, unchanged except that types are converted with
`toMonoTypeKeep` (see `MonoTypesKeep.lean`) instead of `toMonoType`, so that
mono types keep closed, non-dependent type-former arguments (the value type
of a `HashMap`), and that a `cases` on `Array`, `ByteArray` or `FloatArray`
binds its field at the field's own type, not `lcAny`
(`casesArrayToMonoK`). Definitions carry a `K` suffix to stay apart from
Lean's.
-/

namespace Lean.Compiler.LCNF
open LeanToReussir

structure ToMonoKM.State where
  typeParams : FVarIdHashSet := {}

abbrev ToMonoKM := StateRefT ToMonoKM.State CompilerM

def Param.toMonoK (param : Param .pure) : ToMonoKM (Param .pure) := do
  if isTypeFormerType param.type then
    modify fun s => { s with typeParams := s.typeParams.insert param.fvarId }
  param.update (← toMonoTypeKeep param.type)

@[inline]
def argToMonoK (arg : Arg .pure) : ToMonoKM (Arg .pure) := do
  match arg with
  | .erased | .type .. => return .erased
  | .fvar fvarId =>
    if (← get).typeParams.contains fvarId then
      return .erased
    else
      return arg

def argsToMonoKWithFnType (args : Array (Arg .pure)) (type : Expr)
    : ToMonoKM (Array (Arg .pure)) := do
  let mut remainingType : Option Expr := some type
  let mut result := Array.emptyWithCapacity args.size
  for arg in args do
    let monoArg ← if let some (.forallE _ d b _ ) := remainingType then
      remainingType := some b
      if d.isErased then
        pure .erased
      else
        argToMonoK arg
    else
      remainingType := none
      argToMonoK arg
    result := result.push monoArg
  return result

def argsToMonoKRedArg (args : Array (Arg .pure)) (params : Array (Param .pure))
    (redArgs : Array (Arg .pure)) : ToMonoKM (Array (Arg .pure)) := do
  let mut result := #[]
  let mut argIdx := 0
  for redArg in redArgs do
    match redArg with
    | .fvar fvarId =>
      while params[argIdx]!.fvarId != fvarId do
        argIdx := argIdx + 1
      let arg ← argToMonoK args[argIdx]!
      argIdx := argIdx + 1
      result := result.push arg
    | .erased | .type _ => pure ()
  for arg in args[params.size...*] do
    let arg ← argToMonoK arg
    result := result.push arg
  return result

def ctorAppToMonoK (ctorInfo : ConstructorVal) (args : Array (Arg .pure))
    : ToMonoKM (LetValue .pure) := do
  let argsNewParams : Array (Arg .pure) := .replicate ctorInfo.numParams .erased
  let argsNewFields ← args[ctorInfo.numParams...*].toArray.mapM argToMonoK
  let argsNew := argsNewParams ++ argsNewFields
  return .const ctorInfo.name [] argsNew

partial def LetValue.toMonoK (e : LetValue .pure) : ToMonoKM (LetValue .pure) := do
  match e with
  | .erased | .lit .. => return e
  | .const declName _ args =>
    if declName == ``Decidable.isTrue then
      return .const ``Bool.true [] #[]
    else if declName == ``Decidable.isFalse then
      return .const ``Bool.false [] #[]
    else if declName == ``Decidable.decide then
      -- Decidable.decide is the identity function since Decidable
      -- and Bool have the same runtime representation.
      return args[1]!.toLetValue
    else if declName == ``Quot.mk then
      return args[2]!.toLetValue
    else if declName == ``Quot.lcInv then
      match args[2]! with
      | .fvar fvarId =>
        let mut extraArgs : Array (Arg .pure) := .emptyWithCapacity (args.size - 3)
        for i in 3...args.size do
          let arg ← argToMonoK args[i]!
          extraArgs := extraArgs.push arg
        return .fvar fvarId extraArgs
      | .erased | .type _ =>
        return .erased
    else if declName == ``Nat.zero then
      return .lit (.nat 0)
    else if declName == ``Nat.succ then
      -- This should have been handled in Code.toMonoK.
      unreachable!
    else if let some (.ctorInfo ctorInfo) := (← getEnv).find? declName then
      if let some info ← hasTrivialStructure? ctorInfo.induct then
        args[ctorInfo.numParams + info.fieldIdx]!.toLetValue.toMonoK
      else
        ctorAppToMonoK ctorInfo args
    else
      let env ← getEnv
      if let some monoDecl ← getMonoDecl? declName then
        if args.size >= monoDecl.params.size then
          if let .code (.let { fvarId := resultFVar, value := .const callName _ callArgs, .. }
                             (.return retFVar)) := monoDecl.value then
            let redArgDeclName := declName ++ `_redArg
            if callName == redArgDeclName && retFVar == resultFVar then
              let args ← argsToMonoKRedArg args monoDecl.params callArgs
              return .const redArgDeclName [] args
        let args ← argsToMonoKWithFnType args monoDecl.type
        return .const declName [] args
      else
        let args ← args.mapM argToMonoK
        return .const declName [] args
  | .fvar fvarId args =>
    if (← get).typeParams.contains fvarId then
      return .erased
    else
      return .fvar fvarId (← args.mapM argToMonoK)
  | .proj structName fieldIdx fvarId =>
    if (← get).typeParams.contains fvarId then
      return .erased
    else if let some info ← hasTrivialStructure? structName then
      if info.fieldIdx == fieldIdx then
        return .fvar fvarId #[]
      else
        return .erased
    else
      return e

def LetDecl.toMonoK (decl : LetDecl .pure) : ToMonoKM (LetDecl .pure) := do
  let type ← toMonoTypeKeep decl.type
  let value ← decl.value.toMonoK
  decl.update type value

def mkFieldParamsForComputedFieldsK (ctorType : Expr) (numParams : Nat) (numNewFields : Nat)
    (oldFields : Array (Param .pure)) : ToMonoKM (Array (Param .pure)) := do
  let mut type := ctorType
  for _ in *...numParams do
    match type with
    | .forallE _ _ body _ =>
      type := body
    | _ => unreachable!
  let mut newFields := Array.emptyWithCapacity (oldFields.size + numNewFields)
  for _ in *...numNewFields do
    match type with
    | .forallE name fieldType body _ =>
      let param ← mkParam name (← toMonoTypeKeep fieldType) false
      newFields := newFields.push param
      type := body
    | _ => unreachable!
  return newFields ++ oldFields

mutual

partial def FunDecl.toMonoK (decl : FunDecl .pure) : ToMonoKM (FunDecl .pure) := do
  let type ← toMonoTypeKeep decl.type
  let params ← decl.params.mapM (·.toMonoK)
  let value ← decl.value.toMonoK
  decl.update type params value

/-- Convert `cases` `Decidable` => `Bool` -/
partial def decToMonoK (c : Cases .pure) (_ : c.typeName == ``Decidable) : ToMonoKM (Code .pure) := do
  let resultType ← toMonoTypeKeep c.resultType
  let alts ← c.alts.mapM fun alt => do
    match alt with
    | .default k => return alt.updateCode (← k.toMonoK)
    | .alt ctorName ps k =>
      eraseParams ps
      let ctorName := if ctorName == ``Decidable.isTrue then ``Bool.true else ``Bool.false
      return .alt ctorName #[] (← k.toMonoK)
  return .cases ⟨``Bool, resultType, c.discr, alts⟩

/-- Eliminate `cases` for `Nat`. -/
partial def casesNatToMonoK (c: Cases .pure) (_ : c.typeName == ``Nat) : ToMonoKM (Code .pure) := do
  let resultType ← toMonoTypeKeep c.resultType
  let natType := mkConst ``Nat
  let zeroDecl ← mkLetDecl `zero natType (.lit (.nat 0))
  let isZeroDecl ← mkLetDecl `isZero (mkConst ``Bool) (.const ``Nat.decEq [] #[.fvar c.discr, .fvar zeroDecl.fvarId])
  let alts ← c.alts.mapM fun alt => do
    match alt with
    | .default k => return alt.updateCode (← k.toMonoK)
    | .alt ctorName ps k =>
      eraseParams ps
      if ctorName == ``Nat.succ then
        let p := ps[0]!
        let oneDecl ← mkLetDecl `one natType (.lit (.nat 1))
        let subOneDecl := { fvarId := p.fvarId, binderName := p.binderName, type := natType, value := .const ``Nat.sub [] #[.fvar c.discr, .fvar oneDecl.fvarId] }
        modifyLCtx fun lctx => lctx.addLetDecl subOneDecl
        return .alt ``Bool.false #[] (.let oneDecl (.let subOneDecl (← k.toMonoK)))
      else
        return .alt ``Bool.true #[] (← k.toMonoK)
  return .let zeroDecl (.let isZeroDecl (.cases ⟨``Bool, resultType, isZeroDecl.fvarId, alts⟩))

/-- Eliminate `cases` for `Int`. -/
partial def casesIntToMonoK (c: Cases .pure) (_ : c.typeName == ``Int) : ToMonoKM (Code .pure) := do
  let resultType ← toMonoTypeKeep c.resultType
  let natType := mkConst ``Nat
  let zeroNatDecl ← mkLetDecl `natZero natType (.lit (.nat 0))
  let zeroIntDecl ← mkLetDecl `intZero (mkConst ``Int) (.const ``Int.ofNat [] #[.fvar zeroNatDecl.fvarId])
  let isNegDecl ← mkLetDecl `isNeg (mkConst ``Bool) (.const ``Int.decLt [] #[.fvar c.discr, .fvar zeroIntDecl.fvarId])
  let alts ← c.alts.mapM fun alt => do
    match alt with
    | .default k => return alt.updateCode (← k.toMonoK)
    | .alt ctorName ps k =>
      eraseParams ps
      let p := ps[0]!
      if ctorName == ``Int.negSucc then
        let absDecl ← mkLetDecl `abs natType (.const ``Int.natAbs [] #[.fvar c.discr])
        let oneDecl ← mkLetDecl `one natType (.lit (.nat 1))
        let subOneDecl := { fvarId := p.fvarId, binderName := p.binderName, type := natType, value := .const ``Nat.sub [] #[.fvar absDecl.fvarId, .fvar oneDecl.fvarId] }
        modifyLCtx fun lctx => lctx.addLetDecl subOneDecl
        return .alt ``Bool.true #[] (.let absDecl (.let oneDecl (.let subOneDecl (← k.toMonoK))))
      else
        let absDecl := { fvarId := p.fvarId, binderName := p.binderName, type := natType, value := .const ``Int.natAbs [] #[.fvar c.discr] }
        modifyLCtx fun lctx => lctx.addLetDecl absDecl
        return .alt ``Bool.false #[] (.let absDecl (← k.toMonoK))
  return .let zeroNatDecl (.let zeroIntDecl (.let isNegDecl (.cases ⟨``Bool, resultType, isNegDecl.fvarId, alts⟩)))

/-- Eliminate `cases` for `UInt` types. -/
partial def casesUIntToMonoK (c : Cases .pure) (uintName : Name) (_ : c.typeName == uintName) :
    ToMonoKM (Code .pure) := do
  assert! c.alts.size == 1
  let .alt _ ps k := c.alts[0]! | unreachable!
  eraseParams ps
  let p := ps[0]!
  let decl := { fvarId := p.fvarId, binderName := p.binderName, type := anyExpr, value := .const (.str uintName "toBitVec") [] #[.fvar c.discr] }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  let k ← k.toMonoK
  return .let decl k

/-- Eliminate `cases` for `Array`. Unlike Lean's `toMono`, the list is bound
at the field's own type (`List α`, as every other `cases` field,
`Param.toMonoK`), not `lcAny`: Stage 3 then sends the call to the instance
of `Array.toList` at `α` (`externRetarget?`), so a compact array is not
passed as an array of boxes (hunt HARR2-01). -/
partial def casesArrayToMonoK (c : Cases .pure) (_ : c.typeName == ``Array) : ToMonoKM (Code .pure) := do
  assert! c.alts.size == 1
  let .alt _ ps k := c.alts[0]! | unreachable!
  eraseParams ps
  let p := ps[0]!
  let decl := { fvarId := p.fvarId, binderName := p.binderName, type := (← toMonoTypeKeep p.type), value := .const ``Array.toList [] #[.erased, .fvar c.discr] }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  let k ← k.toMonoK
  return .let decl k

/-- Eliminate `cases` for `ByteArray`. Unlike Lean's `toMono`, the data is
bound at the field's own type, `Array UInt8` (the result type of
`ByteArray.data`), not `lcAny` (hunt HARR2-01: a `map` over it could not be
typed, and the `u8` kind went off). -/
partial def casesByteArrayToMonoK (c : Cases .pure) (_ : c.typeName == ``ByteArray) :
    ToMonoKM (Code .pure) := do
  assert! c.alts.size == 1
  let .alt _ ps k := c.alts[0]! | unreachable!
  eraseParams ps
  let p := ps[0]!
  let decl := { fvarId := p.fvarId, binderName := p.binderName, type := (← toMonoTypeKeep p.type), value := .const ``ByteArray.data [] #[.fvar c.discr] }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  let k ← k.toMonoK
  return .let decl k

/-- Eliminate `cases` for `FloatArray`. Unlike Lean's `toMono`, the data
is bound at the field's own type, `Array Float` (the result type of
`FloatArray.data`), not `lcAny` (hunt HARR2-01). -/
partial def casesFloatArrayToMonoK (c : Cases .pure) (_ : c.typeName == ``FloatArray) :
    ToMonoKM (Code .pure) := do
  assert! c.alts.size == 1
  let .alt _ ps k := c.alts[0]! | unreachable!
  eraseParams ps
  let p := ps[0]!
  let decl := { fvarId := p.fvarId, binderName := p.binderName, type := (← toMonoTypeKeep p.type), value := .const ``FloatArray.data [] #[.fvar c.discr] }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  let k ← k.toMonoK
  return .let decl k

/-- Eliminate `cases` for `String`. -/
partial def casesStringToMonoK (c : Cases .pure) (_ : c.typeName == ``String) : ToMonoKM (Code .pure) := do
  assert! c.alts.size == 1
  let .alt _ ps k := c.alts[0]! | unreachable!
  eraseParams ps
  let p := ps[0]!
  let decl := { fvarId := p.fvarId, binderName := p.binderName, type := anyExpr, value := .const ``String.toByteArray [] #[.fvar c.discr] }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  let k ← k.toMonoK
  return .let decl k

/-- Eliminate `cases` for `Float`. -/
partial def casesFloatToMonoK (c : Cases .pure) (_ : c.typeName == ``Float) : ToMonoKM (Code .pure) := do
  assert! c.alts.size == 1
  let .alt _ ps k := c.alts[0]! | unreachable!
  eraseParams ps
  let p := ps[0]!
  let decl := { fvarId := p.fvarId, binderName := p.binderName, type := anyExpr, value := .const ``Float.toModel [] #[.fvar c.discr] }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  let k ← k.toMonoK
  return .let decl k

/-- Eliminate `cases` for `Float32`. -/
partial def casesFloat32ToMonoK (c : Cases .pure) (_ : c.typeName == ``Float32) : ToMonoKM (Code .pure) := do
  assert! c.alts.size == 1
  let .alt _ ps k := c.alts[0]! | unreachable!
  eraseParams ps
  let p := ps[0]!
  let decl := { fvarId := p.fvarId, binderName := p.binderName, type := anyExpr, value := .const ``Float32.toModel [] #[.fvar c.discr] }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  let k ← k.toMonoK
  return .let decl k

/-- Eliminate `cases` for `Thunk. -/
partial def casesThunkToMonoK (c : Cases .pure) (_ : c.typeName == ``Thunk) : ToMonoKM (Code .pure) := do
  assert! c.alts.size == 1
  let .alt _ ps k := c.alts[0]! | unreachable!
  eraseParams ps
  let p := ps[0]!
  let letValue := .const ``Thunk.get [] #[.erased, .fvar c.discr]
  let letDecl ← mkLetDecl (← mkFreshBinderName `_x) anyExpr letValue
  let paramType := .const `PUnit []
  let decl := ⟨
    p.fvarId,
    p.binderName,
    #[← mkAuxParam paramType],
    (← mkArrow paramType anyExpr),
    .let letDecl (.return letDecl.fvarId)
  ⟩
  modifyLCtx fun lctx => lctx.addFunDecl decl
  let k ← k.toMonoK
  return .fun decl k

/-- Eliminate `cases` for `Task. -/
partial def casesTaskToMonoK (c : Cases .pure) (_ : c.typeName == ``Task) : ToMonoKM (Code .pure) := do
  assert! c.alts.size == 1
  let .alt _ ps k := c.alts[0]! | unreachable!
  eraseParams ps
  let p := ps[0]!
  let decl := { fvarId := p.fvarId, binderName := p.binderName, type := anyExpr, value := .const ``Task.get [] #[.erased, .fvar c.discr] }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  let k ← k.toMonoK
  return .let decl k

/-- Eliminate `cases` for trivial structure. See `hasTrivialStructure?` -/
partial def trivialStructToMonoK (info : TrivialStructureInfo) (c : Cases .pure) : ToMonoKM (Code .pure) := do
  assert! c.alts.size == 1
  let .alt ctorName ps k := c.alts[0]! | unreachable!
  assert! ctorName == info.ctorName
  assert! info.fieldIdx < ps.size
  let p := ps[info.fieldIdx]!
  eraseParams ps
  /- We reuse `p`s `fvarId` to avoid substitution -/
  let decl := { fvarId := p.fvarId, binderName := p.binderName, type := (← toMonoTypeKeep p.type), value := .fvar c.discr #[] }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  let k ← k.toMonoK
  return .let decl k

partial def Code.toMonoK (code : Code .pure) : ToMonoKM (Code .pure) := do
  match code with
  | .let decl k =>
    match decl.value with
    | .const ``Nat.succ _ args =>
      let #[arg] := args | unreachable!
      let oneDecl ← mkAuxLetDecl (.lit (.nat 1))
      let decl ← decl.update decl.type (.const ``Nat.add [] #[arg, .fvar oneDecl.fvarId])
      return .let oneDecl (.let decl (← k.toMonoK))
    | _ =>
      return code.updateLet! (← decl.toMonoK) (← k.toMonoK)
  | .fun decl k | .jp decl k => return code.updateFun! (← decl.toMonoK) (← k.toMonoK)
  | .unreach type => return .unreach (← toMonoTypeKeep type)
  | .jmp fvarId args => return code.updateJmp! fvarId (← args.mapM argToMonoK)
  | .return .. => return code
  | .cases c =>
    if h : c.typeName == ``Decidable then
      decToMonoK c h
    else if h : c.typeName == ``Nat then
      casesNatToMonoK c h
    else if h : c.typeName == ``Int then
      casesIntToMonoK c h
    else if h : c.typeName == ``UInt8 then
      casesUIntToMonoK c ``UInt8 h
    else if h : c.typeName == ``UInt16 then
      casesUIntToMonoK c ``UInt16 h
    else if h : c.typeName == ``UInt32 then
      casesUIntToMonoK c ``UInt32 h
    else if h : c.typeName == ``UInt64 then
      casesUIntToMonoK c ``UInt64 h
    else if h : c.typeName == ``Array then
      casesArrayToMonoK c h
    else if h : c.typeName == ``ByteArray then
      casesByteArrayToMonoK c h
    else if h : c.typeName == ``FloatArray then
      casesFloatArrayToMonoK c h
    else if h : c.typeName == ``String then
      casesStringToMonoK c h
    else if h : c.typeName == ``Float then
      casesFloatToMonoK c h
    else if h : c.typeName == ``Float32 then
      casesFloat32ToMonoK c h
    else if h : c.typeName == ``Thunk then
      casesThunkToMonoK c h
    else if h : c.typeName == ``Task then
      casesTaskToMonoK c h
    else if let some info ← hasTrivialStructure? c.typeName then
      trivialStructToMonoK info c
    else
      let resultType ← toMonoTypeKeep c.resultType
      let env ← getEnv
      let some (.inductInfo inductInfo) := env.find? c.typeName | panic! "expected inductive type"
      let casesOnName := mkCasesOnName inductInfo.name
      if (getImplementedBy? env casesOnName).isSome then
        -- TODO: Enforce that this is only used for computed fields.
        let typeName := c.typeName ++ `_impl
        let alts ← c.alts.mapM fun alt => do
          match alt with
          | .default k => return alt.updateCode (← k.toMonoK)
          | .alt ctorName ps k =>
            let implCtorName := ctorName ++ `_impl
            let some (.ctorInfo ctorInfo) := env.find? implCtorName | panic! "expected constructor"
            let numNewFields := ctorInfo.numFields - ps.size
            let ps ← mkFieldParamsForComputedFieldsK ctorInfo.type ctorInfo.numParams numNewFields ps
            let k ← k.toMonoK
            return .alt implCtorName ps k
        return .cases ⟨typeName, resultType, c.discr, alts⟩
      else
        let alts ← c.alts.mapM fun alt =>
          match alt with
          | .default k => return alt.updateCode (← k.toMonoK)
          | .alt _ ps k => return alt.updateAlt! (← ps.mapM (·.toMonoK)) (← k.toMonoK)
        return code.updateCases! resultType c.discr alts

end

def Decl.toMonoK (decl : Decl .pure) : CompilerM (Decl .pure) := do
  go |>.run' {}
where
  go : ToMonoKM (Decl .pure) := do
    let type ← toMonoTypeKeep decl.type
    let params ← decl.params.mapM (·.toMonoK)
    let value ← decl.value.mapCodeM (·.toMonoK)
    let decl := { decl with type, params, value, levelParams := [] }
    decl.saveMono
    return decl

def toMonoK : Pass where
  name     := `toMonoK
  run      := (·.mapM (·.toMonoK))
  phase    := .base
  phaseOut := .mono
  shouldAlwaysRunCheck := true


end Lean.Compiler.LCNF
