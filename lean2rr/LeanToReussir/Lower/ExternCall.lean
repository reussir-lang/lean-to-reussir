import LeanToReussir.Lower.Identity

/-!
# Extern calls

The dispatch of an extern call: generated glue for externs over Lean-defined
types (`customExtern`), otherwise a call of the runtime function named
after the C symbol (`lowerExternCall`, translation plan §5.8).
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Externs whose results mention Lean-defined types get generated glue
(translation plan §5.8); returns `none` for ordinary externs. -/
def customExtern (orig : Name) (params : Array Expr) (ret : Expr) (args : Array RR.Expr) :
    LowerM (Option RR.Expr) := do
  if let some e ← ctorCallbackExtern (← externSymbol orig) ret args then return some e
  if let some e ← lazyExtern orig params ret args then return some e
  if let some e ← promiseExtern (← externSymbol orig) params ret args then return some e
  if let some e ← processExtern orig params ret args then return some e
  match orig with
  -- `IO.Process.exit : UInt8 → IO α` never returns; nor does `forceExit`,
  -- which skips flushing and exit handlers.
  | ``IO.Process.exit | ``IO.Process.forceExit =>
    let rt ← lowerType ret
    let e ← fresh "ex"
    let prim := if orig == ``IO.Process.exit then "l2r_process_exit" else "l2r_process_force_exit"
    return some (.block ⟨#[(e, some (.named "u64"), .call prim #[] #[args[0]!])],
      .call "l2r_unreachable" #[rt] #[]⟩)
  | _ => pure ()
  -- `ptrAddrUnsafe`: what native Lean answers (see `addrOf`).
  if (← externSymbol orig) == "lean_ptr_addr" then
    let some p := params[0]? | return none
    return some (← addrOf args[0]! (← lowerType p))
  -- `Lean.Name.beq`: structural equality (see `structEqFn`).
  if (← externSymbol orig) == "lean_name_eq" then
    let .named tn ← lowerType params[0]! | return none
    let some f ← structEqFn tn | return none
    return some (.call f #[] #[args[0]!, args[1]!])
  -- Slices (`ByteSlice.beq`, `String.Slice` hash and `<`): the runtime
  -- takes the fields — the bytes or string, start, end — of each slice.
  let sliceSym := (← externSymbol orig)
  if let some prim := sliceGlue? sliceSym then
    let st ← lowerType params[0]!
    let .named sn := st | return none
    let some info := (← get).typeInfos[sn]? | return none
    let some layout := info.ctors.find? info.ctorOrder[0]! | return none
    let some (some (pa, _)) := layout.fields[0]? | return none
    let some (some (ps, _)) := layout.fields[1]? | return none
    let some (some (pe, _)) := layout.fields[2]? | return none
    let parts (x : RR.Expr) : Array RR.Expr :=
      #[.field x pa, .call "lean_usize_of_nat" #[] #[.field x ps], .call "lean_usize_of_nat" #[] #[.field x pe]]
    if args.size == 1 then
      return some (← withVar "bs" st args[0]! fun a => pure (.call prim #[] (parts a)))
    return some (← withVar "bs" st args[0]! fun a => withVar "bs" st args[1]! fun b =>
      pure (.call prim #[] (parts a ++ parts b)))
  -- `ShareCommon.State.shareCommon s a`: hash-consing natively; its
  -- reference body `(a, s)` is observably the same (sharing is not).
  if orig == ``ShareCommon.State.shareCommon then
    let rt ← lowerType ret
    let tys ← ctorFieldTys rt ``Prod.mk
    let some at' := tys[0]? | return none
    let some stt := tys[1]? | return none
    let n := params.size
    let a ← coerce args[n - 1]! (← lowerType params[n - 1]!) at'
    let st ← coerce args[n - 2]! (← lowerType params[n - 2]!) stt
    return some (← ctorValue rt ``Prod.mk #[a, st])
  -- `String.ofList : List Char → String`
  if orig == ``String.ofList then
    let lt ← lowerType params[0]!
    let fn ← listFold s!"l2r_list_to_string_{lt.render.map fun c => if c.isAlphanum then c else '_'}" lt
      (.named "LStr") (.named "u32") fun acc x => .call "lean_string_push" #[] #[acc, x]
    return some (.call fn #[] #[args[0]!, ← strLit ""])
  -- `Array.mk : List α → Array α`
  -- `String.mk : List Char → String`: push the characters onto "".
  if (← externSymbol orig) == "lean_string_mk" then
    let lt ← lowerType params[0]!
    let fn ← listFold s!"l2r_string_of_list_{lt.render.map fun c => if c.isAlphanum then c else '_'}" lt
      (.named "LStr") (.named "u32") fun acc x => .call "lean_string_push" #[] #[acc, x]
    return some (.call fn #[] #[args[0]!, ← strLit ""])
  if orig == ``Array.mk then
    let lt ← lowerType params[0]!
    let arrTy ← lowerType ret
    let some repr ← arrayRepr? arrTy | throwError "lean2rr: bad array type {arrTy.render}"
    let fn ← listFold s!"l2r_list_to_array_{lt.render.map fun c => if c.isAlphanum then c else '_'}" lt arrTy
      repr.value fun acc x => repr.call "push" #[acc, repr.store x]
    return some (.call fn #[] #[args[0]!, repr.call "empty" #[]])
  -- `Array.toList : Array α → List α`: cons the elements from the last.
  if orig == ``Array.toList then
    let arrTy ← lowerType params[0]!
    let lt ← lowerType ret
    let some repr ← arrayRepr? arrTy | throwError "lean2rr: bad array type {arrTy.render}"
    let .named ltn := lt | throwError "lean2rr: bad list type"
    let some info := (← get).typeInfos[ltn]? | throwError "lean2rr: bad list type"
    let some nil := info.ctors.find? ``List.nil | throwError "lean2rr: bad list type"
    let some cons := info.ctors.find? ``List.cons | throwError "lean2rr: bad list type"
    let valTy? := (cons.fields[0]?.join).map (·.2)
    let name := s!"l2r_array_to_list_{ltn}_{repr.family}"
    unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
      let u64 := RR.Ty.named "u64"
      -- Elements without a representation (types, proofs) are not stored.
      let (xLet, fieldVals) ← match valTy? with
        | some valTy => do
          let x := repr.load (repr.call "get" #[.var "v", .var "j"])
          pure (#[("x", some valTy, ← coerce x repr.value valTy)], #[RR.Expr.var "x", .var "acc"])
        | none => pure (#[], #[RR.Expr.var "acc"])
      let body : RR.Block := ⟨#[("zero", some u64, .atom "0")], .ite (.atom "zero < i")
        ⟨#[("one", some u64, .atom "1"), ("j", some u64, .atom "i - one")] ++ xLet ++
         #[("c", some lt, .ctor ltn (some cons.variant) (cons.place fieldVals))],
          .call (name ++ "_go") #[] #[.var "v", .var "j", .var "c"]⟩
        (.ofExpr (.var "acc"))⟩
      let entry : RR.Block :=
        .ofExpr (.call (name ++ "_go") #[] #[.var "v", repr.call "size" #[.var "v"],
          .ctor ltn (some nil.variant) #[]])
      modify fun s => { s with fns := s.fns ++ #[
        .fn (name ++ "_go") #[("v", arrTy), ("i", u64), ("acc", lt)] lt body,
        .fn name #[("v", arrTy)] lt entry] }
    return some (.call name #[] #[args[0]!])
  let std? : Option (Nat × Bool) := match orig with
    | ``IO.getStdin => some (0, false)
    | ``IO.getStdout => some (1, false)
    | ``IO.getStderr => some (2, false)
    | ``IO.setStdin => some (0, true)
    | ``IO.setStdout => some (1, true)
    | ``IO.setStderr => some (2, true)
    | _ => none
  if let some (fd, set) := std? then
    -- `BaseIO FS.Stream`: the result is `ST.Out σ FS.Stream`.
    let resTy ← lowerType ret
    let .named rn := resTy | return none
    let some info := (← get).typeInfos[rn]? | return none
    let some layout := info.ctors.find? info.ctorOrder[0]! | return none
    let some (some (_, streamTy)) := layout.fields[0]? | return none
    let (getFn, setFn) ← stdStreamFns fd streamTy
    if set then
      let s ← coerce args[0]! (← lowerType params[0]!) streamTy
      return some (← wrapIOResult resTy (.call setFn #[] #[s]))
    return some (← wrapIOResult resTy (.call getFn #[] #[]))
  return none

/-- Emit a saturated extern call. Default: call the prelude function named
after the C symbol with the passed arguments.

For extern instances (polymorphic externs such as `Array.push {α}`), the
prelude function is generic; it receives the storage types of the type
arguments explicitly. A type argument whose values cannot cross Reussir's
FFI boundary (a value type, a closure) is stored boxed in a one-field shared
struct, so arguments of that type are wrapped and a result of that type is
unwrapped here. -/
def lowerExternCall (orig : Name) (typeArgs : Array Expr) (params : Array Expr) (ret : Expr)
    (args : Array RR.Expr) : LowerM RR.Expr := do
  -- Glue sees only relevant parameters: erased ones (type arguments,
  -- proofs) are dropped; the world is kept (IO glue applies actions to it).
  let relevant := (params.zip args).filter fun (p, _) =>
    let p := p.consumeMData
    !(p.isErased || p.isSort)
  if let some e ← customExtern orig (relevant.map (·.1)) ret (relevant.map (·.2)) then return e
  if orig.getPrefix == `ST.Prim || orig.getPrefix == `ST.Prim.Ref then
    if let some e ← refGlue orig typeArgs (relevant.map (·.1)) ret (relevant.map (·.2))
        (← relevant.mapM (lowerType ·.1)) then return e
  let sym ← externSymbol orig
  -- Which parameters the runtime receives: not erased ones, not the world,
  -- not proofs.
  -- A parameter declared at a type variable is passed even when that is
  -- instantiated with a proof-like type (`Array.push` at `PLift True`).
  let (uses0, _) ← typeVarUses orig
  let mask ← params.zipIdx.mapM fun (p, i) => do
    if (uses0[i]?.join).isSome then return true
    return externParamPassed p && !(← isPropTy p)
  let passedArgs := (mask.zip args).filterMap fun (m, a) => if m then some a else none
  -- A fallible IO extern (files): the runtime's last-error protocol.
  if isFallibleIOSym sym then
    let prim := fallibleIOPrim sym
    if let some primRet := (← read).preludeRets[prim]? then
      let argTys ← (mask.zip params).filterMapM fun (m, p) => if m then some <$> lowerType p else pure none
      return ← fallibleIOGlue prim primRet argTys passedArgs ret (follow := sym != "lean_io_symlink_metadata")
  -- A `BaseIO` extern that cannot fail: the runtime provides its payload
  -- as `l2r_<sym without lean_>`; the result is wrapped as an IO result.
  if sym.startsWith "lean_" then
    let prim := "l2r_" ++ (sym.drop 5).toString
    if (← read).preludeFns.contains prim then
      let resTy ← lowerType ret
      if let .named rn := resTy then
        if let some k := (← get).typeKeys[rn]? then
          if k.isAppOf ``EST.Out || k.isAppOf ``ST.Out then
            -- Arguments at the primitive's parameter types (a handle is
            -- `lcAny` in mono code, so it arrives boxed).
            let argTys ← (mask.zip params).filterMapM fun (m, p) => if m then some <$> lowerType p else pure none
            let want := (← read).preludeParams[prim]?.getD argTys
            let passed ← (passedArgs.zip (argTys.zip want)).mapM fun (a, (t, w)) => coerce a t w
            return ← wrapIOResult resTy (.call prim #[] passed)
  -- A generic prelude function in plain Reussir that does not store its
  -- values in runtime containers (`dbgTrace`, `dbgSleep`, `panic`, …) is
  -- instantiated at the value types themselves: its arguments and result
  -- are passed as they are, closures included. Only FFI functions and
  -- containers need array storage types.
  if let some n := (← read).valueGenericFns[sym]? then
    let tys ← if n == typeArgs.size then typeArgs.mapM fun t => do lowerType (← toMonoTypeKeep t)
      else pure #[]
    -- A function value becomes a Reussir closure for the prelude.
    let argTys ← (mask.zip params).filterMapM fun (m, p) => if m then some <$> lowerType p else pure none
    let cls := (← read).valueGenericCls.getD sym #[]
    let passed ← (passedArgs.zip argTys).zipIdx.mapM fun ((a, t), i) => match t with
      | .fn d c => if cls[i]?.getD false then coerce a t (.cls d c) else pure a
      | _ => pure a
    return .call sym tys passed
  -- Array externs at `Array Nat`/`Array Int` use the one-word arrays.
  if let some α := typeArgs[0]? then
    let fam? := match ← lowerType (← toMonoTypeKeep α) with
      | .named "Nat" => some "natarr"
      | .named "Int" => some "intarr"
      | _ => none
    if let some fam := fam? then
      if let some sym' := natArrSym? sym fam then
        return .call sym' #[] passedArgs
  -- Storage for each type argument: the storage type, and the conversions
  -- of a value to and from it (`ArrayRepr.store`/`load`). An extern over
  -- arrays of the type argument stores it as the arrays do (an enumeration
  -- as its index, `arrayStorage`); any other as `arrayElemTy`.
  let overArrays := (params.push ret).any fun p => (p.find? (·.isAppOf ``Array)).isSome
  let mut storage : Array ArrayRepr := #[]
  for t in typeArgs do
    -- Instance keys hold base-phase types.
    let rt ← lowerType (← toMonoTypeKeep t)
    let st ← if overArrays then arrayStorage rt else pure (← arrayElemTy rt).1
    let some r ← arrayRepr? (.app "RVec" #[st]) | throwError "lean2rr: no storage for {rt.render}"
    storage := storage.push r
  -- Values whose declared type is a type parameter `α` are passed and
  -- returned in `α`'s storage (e.g. `Array.push`'s element): wrapped if the
  -- storage is a wrapper, as an index for an enumeration.
  let (uses, retUse) ← typeVarUses orig
  let reprOf (use : Option Nat) : Option ArrayRepr := do storage[← use]?
  let mut passed := #[]
  for i in [:params.size] do
    if mask[i]! then
      let a := args[i]!
      match reprOf (uses[i]?.join) with
      | some r => passed := passed.push (r.store a)
      | none => passed := passed.push a
  let call := RR.Expr.call sym (storage.map (·.storage)) passed
  match reprOf retUse with
  | some r => return r.load call
  | none => return call

end LeanToReussir
