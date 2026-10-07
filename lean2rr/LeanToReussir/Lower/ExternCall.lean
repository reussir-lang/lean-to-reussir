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
  -- `ptrAddrUnsafe` (see `addrOf`).
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
    return some (← stringOfList s!"l2r_list_to_string_{lt.render.map fun c => if c.isAlphanum then c else '_'}" lt args[0]!)
  -- `Array.mk : List α → Array α`
  -- `String.mk : List Char → String`: push the characters onto a string
  -- made at their UTF-8 size (`stringOfList`).
  if (← externSymbol orig) == "lean_string_mk" then
    let lt ← lowerType params[0]!
    return some (← stringOfList s!"l2r_string_of_list_{lt.render.map fun c => if c.isAlphanum then c else '_'}" lt args[0]!)
  if orig == ``Array.mk then
    let lt ← lowerType params[0]!
    let arrTy ← lowerType ret
    let some ae := arrayElem? arrTy | throwError "lean2rr: bad array type {arrTy.render}"
    let fn ← listFold s!"l2r_list_to_array_{lt.render.map fun c => if c.isAlphanum then c else '_'}_{arrTy.enc}" lt arrTy
      ae fun acc x => arrayCall ae "push" #[acc, x]
    -- The array is made at the list's length once, as natively
    -- `List.toArrayImpl` reserves `Array.mkEmpty xs.length` (a capacity
    -- hint, LB-37; review HA-02: pushes onto the empty array grew it about
    -- log2 n times, up to twice the size).
    let len ← listLength lt
    let xs ← fresh "xs"
    return some (.block ⟨#[(xs, some lt, args[0]!)], .call fn #[] #[.var xs,
      arrayCall ae "with_capacity" #[.call len #[] #[.var xs, .atom "0"], .atom "8"]]⟩)
  -- `ByteArray.mk`/`data`, `FloatArray.mk`/`data`: between an array of
  -- `Box`es and the runtime's array of bytes or floats (natively a copy
  -- too): the prelude's texture (`tex`), which allocates the result at its
  -- exact size and converts the elements in one loop. Unboxing at `u8` or
  -- `f64` reads a pointer only in a program that casts (`programCasts`:
  -- the generated cast, `l2r_unbox_u8`): there the texture serves an array
  -- whose boxes it reads (`check`: all immediates, or immediates and the
  -- float and `UInt64` cells), and a generated loop, element by element
  -- (`arrayMapFn`), the others.
  let sym ← externSymbol orig
  if let some (dstElem, name, tex, check?) := (match sym with
      | "lean_byte_array_mk" => some (RR.Ty.named "u8", "l2r_byte_array_of_array", "l2r_bytes_of_boxes",
          some "l2r_boxes_all_imm")
      | "lean_byte_array_data" => some (RR.Ty.box, "l2r_byte_array_to_array", "l2r_boxes_of_bytes", none)
      | "lean_float_array_mk" => some (RR.Ty.named "f64", "l2r_float_array_of_array", "l2r_floats_of_boxes",
          some "l2r_boxes_all_float_words")
      | "lean_float_array_data" => some (RR.Ty.box, "l2r_float_array_to_array", "l2r_boxes_of_floats", none)
      | _ => none) then
    let srcTy ← lowerType params[0]!
    let some se := arrayElem? srcTy | throwError "lean2rr: bad array type {srcTy.render}"
    let loop : LowerM String := arrayMapFn name srcTy dstElem fun x => coerce x se dstElem
    -- The textures take and give arrays of boxes (rule 1).
    let retElem := arrayElem? (← lowerType ret)
    unless (if check?.isSome then se == RR.Ty.box else retElem == some RR.Ty.box) do
      return some (.call (← loop) #[] #[args[0]!])
    let some check := check? | return some (.call tex #[] #[args[0]!])
    unless (← read).programCasts do return some (.call tex #[] #[args[0]!])
    let fn ← loop
    let v ← fresh "ba"
    return some (.block ⟨#[(v, some srcTy, args[0]!)],
      .ite (.call check #[] #[.var v]) (.ofExpr (.call tex #[] #[.var v])) (.ofExpr (.call fn #[] #[.var v]))⟩)
  -- `Array.toList : Array α → List α`: cons the elements from the last.
  if orig == ``Array.toList then
    let arrTy ← lowerType params[0]!
    let lt ← lowerType ret
    let some ae := arrayElem? arrTy | throwError "lean2rr: bad array type {arrTy.render}"
    let .named ltn := lt | throwError "lean2rr: bad list type"
    let some info := (← get).typeInfos[ltn]? | throwError "lean2rr: bad list type"
    let some nil := info.ctors.find? ``List.nil | throwError "lean2rr: bad list type"
    let some cons := info.ctors.find? ``List.cons | throwError "lean2rr: bad list type"
    -- The head is a `Box` at every instantiation (`nominalType`).
    let some (_, valTy) := cons.fields[0]?.join | throwError "lean2rr: bad list type {ltn} (internal error)"
    let name := s!"l2r_array_to_list_{ltn}_{arrTy.enc}"
    unless (← hasFn name) do
      let u64 := RR.Ty.named "u64"
      let x := arrayCall ae "get" #[.var "v", .var "j"]
      let (xLet, fieldVals) := (#[("x", some valTy, ← coerce x ae valTy)], #[RR.Expr.var "x", .var "acc"])
      let body : RR.Block := ⟨#[("zero", some u64, .atom "0")], .ite (.atom "zero < i")
        ⟨#[("one", some u64, .atom "1"), ("j", some u64, .atom "i - one")] ++ xLet ++
         #[("c", some lt, .ctor ltn (some cons.variant) (cons.place fieldVals))],
          .call (name ++ "_go") #[] #[.var "v", .var "j", .var "c"]⟩
        (.ofExpr (.var "acc"))⟩
      let entry : RR.Block :=
        .ofExpr (.call (name ++ "_go") #[] #[.var "v", arrayCall ae "size" #[.var "v"],
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
    let streamTy ← lowerType (mkConst ``IO.FS.Stream)
    let (getFn, setFn) ← stdStreamFns fd streamTy
    if set then
      let s ← coerce args[0]! (← lowerType params[0]!) streamTy
      return some (← wrapIOResult resTy (.call setFn #[] #[s]) streamTy)
    return some (← wrapIOResult resTy (.call getFn #[] #[]) streamTy)
  return none

/-- The call of an extern of the program that lean2rr refuses
(`LowerCtx.externRefusals`): a function no prelude defines,
`l2r_refused_<declaration>`, so the program, generated only under
`L2R_ALLOW_MISSING_EXTERNS`, does not build. -/
def refusedExternCall (orig : Name) (args : Array RR.Expr) : RR.Expr :=
  .call ("l2r_refused_" ++ fnName orig) #[] args

/-- The read externs whose index `bindReadIndex` binds first: element
reads at a `Nat` index (`a[i]'h`, `a[i]!` of `Array`, `ByteArray` and
`FloatArray`) and the string reads at a `Nat` position.
`String.Pos.Raw.get?` (`lean_string_utf8_get_opt`) is not here: it goes
through lean2rr's glue (`Lower/Externs.lean`), not this call. -/
def readExternSyms : List String := [
  "lean_array_fget", "lean_array_fget_borrowed", "lean_array_get", "lean_array_get_borrowed",
  "lean_byte_array_fget", "lean_byte_array_get", "lean_float_array_fget", "lean_float_array_get",
  "lean_string_utf8_get", "lean_string_utf8_get_bang", "lean_string_utf8_get_fast",
  "lean_string_utf8_next", "lean_string_utf8_next_fast", "lean_string_utf8_prev",
  "lean_string_utf8_at_end", "lean_string_is_valid_pos", "lean_string_get_byte_fast"]

/-- The call `mk args` of the extern `sym`; for a read extern
(`readExternSyms`), each argument that is a variable passed to a parameter
of type `Nat` is bound by a `let` first: `let k = i; read(a, k)`. That is
the index. A parameter declared at a type variable (`get!`'s default, at
`Array Nat` a `Nat`) is not: its argument is passed in its storage (`Box`,
the boxed `Nat`, or the box itself where the boxing was folded away,
`boxUnboxed?`), not as a `Nat`; `atVar` marks those parameters.

Reussir increments a variable that is used again later at the place where it
is used, the arguments of a call from left to right. As a direct argument, an
index used after the read (`a[i]`, then `i + 1`) was incremented after the
container. The increment of a big index is a store that LLVM cannot tell from
a store to the container's count, so it came between the container's
increment and the read's decrement: LLVM reloaded the count and kept both
stores (lean-zip's LZ77 loop). Bound first, the index is incremented at the
`let`, and the container's increment is the last store before the read.
The arguments are those of the parameters (the extern's parameter types)
that `mask` passes. -/
def bindReadIndex (sym : String) (mask : Array Bool) (atVar : Array Bool) (params : Array Expr)
    (args : Array RR.Expr) (mk : Array RR.Expr → RR.Expr) : LowerM RR.Expr := do
  unless readExternSyms.contains sym do return mk args
  let isNat := (mask.zip params).zipIdx.filterMap fun ((m, p), i) =>
    if m then some (!(atVar[i]?.getD false) && p.consumeMData.isConstOf ``Nat) else none
  let mut lets := #[]
  let mut args' := #[]
  for (a, i) in args.zipIdx do
    match a, isNat[i]? with
    | .var _, some true =>
      let k ← fresh "ix"
      lets := lets.push (k, some (RR.Ty.named "Nat"), a)
      args' := args'.push (.var k)
    | _, _ => args' := args'.push a
  return if lets.isEmpty then mk args else .block ⟨lets, mk args'⟩

/-- The mono types of the parameters of extern `orig` in its declaration
(type arguments and proofs erased, a value of a type parameter `lcAny`);
empty if they cannot be computed. -/
def genericParamTypes (orig : Name) : LowerM (Array Expr) := do
  try
    let mut ty ← toMonoTypeKeep (← getOtherDeclBaseType orig [])
    let mut out := #[]
    repeat
      match ty.consumeMData.headBeta with
      | .forallE _ d b _ =>
        out := out.push d
        ty := b.instantiate1 anyExpr
      | _ => break
    return out
  catch _ => return #[]

/-- The argument Lean passes for a parameter of mono type `g` (in the
extern's declaration) that an instance erases: `box(0)`, and for a function
type a function that gives `box(0)` (natively the closure is `box(0)` too,
and `lean_apply_n` of a scalar gives the scalar: a body that the instance
erases never runs). `none` for a function type with an erased domain. -/
partial def erasedArg (g : Expr) : LowerM (Option RR.Expr) := do
  match g.consumeMData.headBeta with
  | .forallE _ d b _ =>
    if erasedDom d then return none
    let some body ← erasedArg (b.instantiate1 anyExpr) | return none
    return some (rawFnValue (← lowerType g) (← fresh "ea") (.ofExpr body))
  | g' => return some (← coerce .unitVal .unit (← lowerType g'))

/-- Emit a saturated extern call. Default: call the prelude function named
after the C symbol with the passed arguments.

For extern instances (polymorphic externs such as `Array.push {α}`), the
prelude function is generic; it receives the storage types of the type
arguments explicitly: `Box` for a type parameter whose values the extern
stores as array elements (its declared signature has `Array α`: an
`Array α` is an array of `Box`es), so arguments of that type are boxed and
a result of that type is unboxed here; for any other, the type itself, or,
for a type whose values cannot cross Reussir's FFI boundary (a value type,
a closure), a one-field shared struct (`cellStorage`). The decision is per
type parameter and from the declared signature: `dbgTraceIfShared` at
`α := Array Nat` passes the array itself (a box would be a new reference to
it, whose sharing the extern would report instead of the array's). -/
def lowerExternCall (orig : Name) (typeArgs : Array Expr) (params : Array Expr) (ret : Expr)
    (args : Array RR.Expr) : LowerM RR.Expr := do
  -- An extern of the program that lean2rr refuses: `calleeOf` reported it,
  -- and the program is rejected; no glue, and a call that resolves to
  -- nothing (under `L2R_ALLOW_MISSING_EXTERNS` the program is generated,
  -- and must not call the runtime's function of the symbol; review REB-11).
  if (← read).externRefusals.contains orig then
    return refusedExternCall orig args
  -- Glue sees only relevant parameters: erased ones (type arguments,
  -- proofs) are dropped; the world is kept (IO glue applies actions to it).
  -- The glue reads its arguments by position, so a parameter that this
  -- instance erases but the declaration does not (`Task.pure`'s `a : α`
  -- at `α := Type`, `Thunk.mk`'s `Unit → α` at `α := Prop`) stays, at the
  -- declaration's mono type, with the argument Lean passes (`erasedArg`;
  -- test `RtExternErasedValue`).
  let gen ← genericParamTypes orig
  let mut relevant : Array (Expr × RR.Expr) := #[]
  for h : i in [:params.size] do
    if !erasedDom params[i] then
      relevant := relevant.push (params[i], args[i]!)
    else if let some g := gen[i]? then
      unless erasedDom g do
        if let some a ← erasedArg g then relevant := relevant.push (g, a)
  if let some e ← customExtern orig (relevant.map (·.1)) ret (relevant.map (·.2)) then return e
  if orig.getPrefix == `ST.Prim || orig.getPrefix == `ST.Prim.Ref then
    if let some e ← refGlue orig (relevant.map (·.1)) ret (relevant.map (·.2)) then return e
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
        if let some k := (← get).typeHeads[rn]? then
          if k == ``EST.Out || k == ``ST.Out then
            -- Arguments at the primitive's parameter types (a handle is
            -- `lcAny` in mono code, so it arrives boxed).
            let argTys ← (mask.zip params).filterMapM fun (m, p) => if m then some <$> lowerType p else pure none
            let want := (← read).preludeParams[prim]?.getD argTys
            let passed ← (passedArgs.zip (argTys.zip want)).mapM fun (a, (t, w)) => coerce a t w
            -- The result too, from a non-generic primitive's result type (a
            -- runtime object such as a mutex or promise is `lcAny` in mono
            -- code).
            match (← read).preludeRets[prim]?, (← read).preludeParams.contains prim with
              | some r, true => return ← wrapIOResult resTy (.call prim #[] passed) r
              | r?, _ =>
                -- A generic primitive (`fn l2r_runtime_hold<T>(a : T) ->
                -- L2RUnit`, `fn l2r_runtime_mark_persistent<T>(a : T) -> T`):
                -- its result has the prelude's result type or, when that
                -- is one of its type parameters, the type of the argument
                -- declared at it. The result's field is a `Box` (rule 1),
                -- so `wrapIOResult` converts.
                let vt ← match (← read).preludeRetArg[prim]?, r? with
                  | some i, _ => pure (argTys[i]?.getD RR.Ty.box)
                  | none, some r => pure r
                  | none, none => ioPayloadFieldTy resTy
                return ← wrapIOResult resTy (.call prim #[] passed) vt
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
    let passed ← (passedArgs.zip argTys).zipIdx.mapM fun ((a, t), i) => match t.rt with
      | .fn d c => if cls[i]?.getD false then coerce a t (.cls d c) else pure a
      | _ => pure a
    return .call sym tys passed
  -- Storage for each type argument. A type parameter the extern stores
  -- as array elements (its declared signature has `Array α`) is stored as
  -- the arrays store it, in a `Box` (one array type, `RVec<Box>`); any
  -- other in its own type, or wrapped (`cellStorage`).
  let inArrays ← typeVarsInArrays orig
  let mut storage : Array RR.Ty := #[]
  for h : k in [:typeArgs.size] do
    -- Instance keys hold base-phase types.
    let rt ← lowerType (← toMonoTypeKeep typeArgs[k])
    storage := storage.push (← if inArrays[k]?.getD false then pure RR.Ty.box else pure (← cellStorage rt).1)
  -- Values whose declared type is a type parameter `α` are passed and
  -- returned in `α`'s storage (e.g. `Array.push`'s element): boxed, or
  -- wrapped if the storage is a wrapper.
  let (uses, retUse) ← typeVarUses orig
  let storageOf (use : Option Nat) : Option RR.Ty := do storage[← use]?
  let toStorage (a : RR.Expr) (t st : RR.Ty) : LowerM RR.Expr := do
    if st == t then return a
    if (← elemBoxOf? st).isSome then
      let .named bn := st | return a
      return .ctor bn none #[a]
    coerce a t st
  let mut passed := #[]
  for i in [:params.size] do
    if mask[i]! then
      let a := args[i]!
      match storageOf (uses[i]?.join) with
      | some st => passed := passed.push (← toStorage a (← lowerType params[i]!) st)
      | none => passed := passed.push a
  -- The prelude's function of that name (and through it the runtime):
  -- one that does not exist is reported, with the extern, by
  -- `lowerProgram` (translation plan §5.8).
  unless (← read).preludeFns.contains sym do
    unless (← get).missingExterns.any (·.1 == sym) do
      modify fun s => { s with missingExterns := s.missingExterns.push (sym, orig) }
  let atVar := params.mapIdx fun i _ => (uses[i]?.join).isSome
  let call ← bindReadIndex sym mask atVar params passed fun passed => RR.Expr.call sym storage passed
  match storageOf retUse with
  | some st =>
    let rt ← lowerType ret
    if st == rt then return call
    if (← elemBoxOf? st).isSome then return .field call 0
    coerce call st rt
  | none => return call

end LeanToReussir
