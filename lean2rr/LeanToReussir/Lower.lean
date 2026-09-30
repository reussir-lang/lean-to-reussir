import Lean
import LeanToReussir.LowerBase

/-!
# Stage 4: lowering mono LCNF to Reussir

Translation plan §5.2–§5.8. Code is lowered declaration by declaration:

* calls follow Lean's arities exactly (§5.2): a saturated call is a direct
  call, a partial application becomes a chain of single-parameter lambdas
  that calls the function only when its last argument arrives, and an
  over-application calls and then applies the result;
* closure values are curried and applied one argument at a time (§5.3);
* `cases` becomes `if`, `match` or field access (§5.5);
* join points are inlined (J1), turned into a structured `let` (J2), or
  outlined into a function called in tail position (J3) (§5.6);
* conversions to and from `Box` are inserted where a value's type differs
  from the type its use expects.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- How a jump to a join point is lowered. -/
inductive JumpAction where
  /-- J1: the join point has a single jump; its body is inlined there. -/
  | inline (params : Array (Param .pure)) (body : Code .pure)
  /-- J2: jumps produce the join point's arguments as the value of the
  enclosing structured `let`. -/
  | yield (tys : Array RR.Ty)
  /-- J3: jumps call the outlined function with the captured variables
  followed by the arguments. -/
  | call (fn : String) (captured : Array String)

structure CodeCtx where
  vars : Std.HashMap FVarId (String × RR.Ty) := {}
  jumps : Std.HashMap FVarId JumpAction := {}
  /-- Types of join-point parameters, for lowering jump arguments. -/
  jpParams : Std.HashMap FVarId (Array RR.Ty) := {}

/-! ## Conversions -/

/-- Head constant of the Lean type a generated nominal type represents. -/
def nominalHead (n : String) : LowerM (Option Name) := do
  match (← get).typeKeys[n]? with
  | some k => return k.getAppFn.constName?
  | none => return none

mutual
  /-- Convert `e` from representation `src` to `dst`. Besides `Box`
  conversions and closure wrappers, two instantiations of the same inductive
  are converted structurally: Lean's mono `cse` compares erased types, so it
  may merge e.g. `[] : List Shape` with `[] : List Nat`; such a merged value
  carries no data at the differing type parameter, so rebuilding it at the
  target type is always possible (an arm that would need an impossible
  element conversion is unreachable). -/
  partial def coerce (e : RR.Expr) (src dst : RR.Ty) : LowerM RR.Expr := do
    match ← tryCoerce e src dst with
    | some r => return r
    | none =>
      let keyOf (t : RR.Ty) : LowerM String := do
        match t with
        | .named n => return match (← get).typeKeys[n]? with | some k => s!"{n} = {k}" | none => n
        | _ => return t.render
      throwError "lean2rr: no representation conversion from {← keyOf src} to {← keyOf dst}"

  partial def tryCoerce (e : RR.Expr) (src dst : RR.Ty) : LowerM (Option RR.Expr) := do
    if src == dst then return some e
    if dst == RR.Ty.box then
      return some (.ctor boxName (some (← boxVariant src)) #[e])
    if src == RR.Ty.box then
      let v ← boxVariant dst
      let x ← fresh "ub"
      return some (.mtch e #[
        { ty := boxName, ctor := some v, binders := #[some x], body := .ofExpr (.var x) },
        { ty := boxName, ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[dst] #[]) }])
    match src, dst with
    | .fn a1 b1, .fn a2 b2 =>
      let x ← fresh "cv"
      let some arg ← tryCoerce (.var x) a2 a1 | return none
      let some res ← tryCoerce (.apply e arg) b1 b2 | return none
      return some (.lam x a2 (.ofExpr res))
    | .named sn, .named dn =>
      let some sh ← nominalHead sn | return none
      let some dh ← nominalHead dn | return none
      if sh != dh then return none
      return some (.call (← structConv sn dn) #[] #[e])
    | .app "RVec" #[se], .app "RVec" #[de] =>
      -- Arrays merged across types: rebuild element by element.
      let _ := (se, de)
      return none
    | _, _ => return none

  /-- The generated function converting instantiation `sn` to `dn` of the
  same inductive (cached). -/
  partial def structConv (sn dn : String) : LowerM String := do
    let fname := s!"l2r_conv_{sn}_{dn}"
    if (← get).fns.any (fun | .fn n .. => n == fname | _ => false) ||
       (← get).convsInProgress.contains fname then return fname
    modify fun s => { s with convsInProgress := s.convsInProgress.insert fname }
    let some si := (← get).typeInfos[sn]? | throwError "lean2rr: no type {sn}"
    let some di := (← get).typeInfos[dn]? | throwError "lean2rr: no type {dn}"
    let mut arms := #[]
    let mut structBody : Option RR.Block := none
    for ctor in si.ctorOrder do
      let some sl := si.ctors.find? ctor | continue
      let some dl := di.ctors.find? ctor | continue
      let srcFields := sl.fields.filterMap id
      let dstFields := dl.fields.filterMap id
      let names ← srcFields.mapM fun _ => fresh "cf"
      let mut vals := #[]
      let mut possible := true
      for h : i in [:dstFields.size] do
        let (_, dt) := dstFields[i]
        match srcFields[i]? with
        | some (_, st) =>
          match ← tryCoerce (.var names[i]!) st dt with
          | some v => vals := vals.push v
          | none => possible := false
        | none => possible := false
      let body : RR.Block := if possible then
          .ofExpr (match di.shape with
            | .struct => .ctor dn none vals
            | _ => .ctor dn (some dl.variant) vals)
        else .ofExpr (.call "l2r_unreachable" #[.named dn] #[])
      match si.shape with
      | .struct =>
        structBody := some ⟨(names.zip srcFields).mapIdx (fun i (n, (_, t)) => (n, some t, RR.Expr.field (.var "x") i)), body.result⟩
      | _ =>
        arms := arms.push { ty := sn, ctor := some sl.variant, binders := names.map some, body }
    let body := match structBody with
      | some b => b
      | none => .ofExpr (.mtch (.var "x") arms)
    modify fun s => { s with fns := s.fns.push (.fn fname #[("x", .named sn)] (.named dn) body) }
    return fname
end

/-! ## Declarations and signatures -/

/-- Parameter types and result type of a function type with `n` parameters. -/
def splitFnType (ty : Expr) (n : Nat) : Array Expr × Expr := Id.run do
  let mut ty := ty
  let mut ps := #[]
  for _ in [:n] do
    match ty.consumeMData with
    | .forallE _ d b _ => ps := ps.push d; ty := b.instantiate1 anyExpr
    | _ => break
  return (ps, ty)

/-- What a constant application targets. -/
inductive Callee where
  /-- A declaration with code in the translated program. -/
  | code (fn : String) (params : Array RR.Ty) (ret : RR.Ty)
  /-- An extern: Lean name (original, for the extern table), key type
  arguments (for polymorphic externs), mono parameter types, result type. -/
  | extern (orig : Name) (typeArgs : Array Expr) (params : Array Expr) (ret : Expr)
  /-- A constructor. -/
  | ctor (info : ConstructorVal)

def calleeOf (f : Name) : LowerM Callee := do
  if let some (.ctorInfo c) := (← getEnv).find? f then return .ctor c
  if let some d := (← read).decls.find? f then
    let (ps, r) := splitFnType d.type d.params.size
    match d.value with
    | .code _ => return .code (fnName f) (← ps.mapM lowerType) (← lowerType r)
    | .extern _ =>
      let key := (← read).keys.find? f
      return .extern (key.map (·.decl) |>.getD f) (key.map (·.typeArgs) |>.getD #[]) ps r
  -- A monomorphic extern kept under its own name: take Lean's persisted mono signature.
  if let some d ← getMonoDecl? f then
    let (ps, r) := splitFnType d.type d.params.size
    return .extern f #[] ps r
  throwError "lean2rr: unknown callee {f} (internal error)"

/-- Argument lowering with conversion to the expected type. -/
def lowerArg (ctx : CodeCtx) (a : Arg .pure) (expected : RR.Ty) : LowerM RR.Expr := do
  match a with
  | .fvar x =>
    match ctx.vars[x]? with
    | some (n, t) => coerce (.var n) t expected
    | none => throwError "lean2rr: unbound variable {x.name} (internal error)"
  | _ => coerce .unitVal .unit expected

/-- A curried chain of lambdas over `tys` whose innermost body is
`mk vars`. Used for partial applications: the body runs only when the last
argument arrives. -/
def lambdaChain (tys : Array RR.Ty) (mk : Array RR.Expr → LowerM RR.Expr) : LowerM RR.Expr := do
  let names ← tys.mapM fun _ => fresh "pa"
  let mut body ← mk (names.map .var)
  for (n, t) in (names.zip tys).reverse do
    body := .lam n t (.ofExpr body)
  return body

/-- Apply a closure to further arguments, one at a time. -/
def applyChain (f : RR.Expr) (fty : RR.Ty) (ctx : CodeCtx) (args : Array (Arg .pure)) :
    LowerM (RR.Expr × RR.Ty) := do
  let mut e := f
  let mut t := fty
  for a in args do
    match t with
    | .fn d c =>
      e := .apply e (← lowerArg ctx a d)
      t := c
    | _ =>
      -- Applying a boxed value: unbox to the closure type implied by the argument.
      throwError "lean2rr: application of a non-function value of type {t.render}"
  return (e, t)

/-! ## Externs -/

/-- The C symbol Lean uses for an extern (the prelude implements functions
under the same names). -/
def externSymbol (orig : Name) : LowerM String := do
  match getExternNameFor (← getEnv) `c orig with
  | some s => return s
  | none => return "l2r_extern_" ++ fnName orig

/-- Whether a parameter of an extern is passed to the C function: erased
parameters and the IO world are not (`paramsWithoutErased`/`paramsWithoutVoid`). -/
def externParamPassed (t : Expr) : Bool :=
  let t := t.consumeMData
  !(t.isErased || t == mkConst ``lcVoid || t.isSort)

/-- Wrap a value as the successful result of an IO action: `EST.Out.ok v`
for `EST.Out`-typed results, `ST.Out` (a one-field struct once the world
field is dropped) for `BaseIO` results. -/
def wrapIOResult (resTy : RR.Ty) (v : RR.Expr) : LowerM RR.Expr := do
  let .named tn := resTy | throwError "lean2rr: IO result of type {resTy.render}"
  let some info := (← get).typeInfos[tn]? | throwError "lean2rr: IO result of type {tn}"
  match info.shape with
  | .struct => return .ctor tn none #[v]
  | _ =>
    let some ok := info.ctors.find? ``EST.Out.ok | throwError "lean2rr: IO result type {tn} has no ok"
    return .ctor tn (some ok.variant) #[v]

/-- The payload type of an IO result type (`EST.Out.ok`'s or `ST.Out`'s value). -/
def ioPayloadTy (resTy : RR.Ty) : LowerM RR.Ty := do
  let .named tn := resTy | return RR.Ty.unit
  let some info := (← get).typeInfos[tn]? | return RR.Ty.unit
  let layout := match info.shape with
    | .struct => info.ctors.find? info.ctorOrder[0]!
    | _ => info.ctors.find? ``EST.Out.ok
  match layout.bind (·.fields[0]?) with
  | some (some (_, t)) => return t
  | _ => return RR.Ty.unit

/-- A standard stream (`IO.getStdout` & co.) as a Lean `IO.FS.Stream` value:
each field is a curried closure calling the runtime primitive
`l2r_stream_<field>` on file descriptor `fd`. Erased and world parameters
are not passed to the primitive. -/
def streamValue (fd : Nat) (streamTy : RR.Ty) : LowerM RR.Expr := do
  let .named sn := streamTy | throwError "lean2rr: bad stream type"
  let some info := (← get).typeInfos[sn]? | throwError "lean2rr: bad stream type"
  let some layout := info.ctors.find? info.ctorOrder[0]! | throwError "lean2rr: bad stream type"
  let fieldNames := getStructureFields (← getEnv) ``IO.FS.Stream
  let mut vals := #[]
  for h : i in [:fieldNames.size] do
    let some (some (_, fty)) := layout.fields[i]? | continue
    -- Split the curried closure type into parameters and the IO result.
    let mut ps := #[]
    let mut t := fty
    repeat
      match t with
      | .fn d c => ps := ps.push d; t := c
      | _ => break
    let prim := s!"l2r_stream_{fieldNames[i]}"
    let names ← ps.mapM fun _ => fresh "s"
    let passed := (names.zip ps).filterMap fun (n, pt) => if pt == .unit then none else some (RR.Expr.var n)
    let call := RR.Expr.call prim #[] (#[.atom (toString fd)] ++ passed)
    -- Primitives with no result return `u64` (Reussir's `unit` is not a value).
    let payload ← ioPayloadTy t
    let v ← if payload == RR.Ty.unit then do
        let r ← fresh "r"
        pure (RR.Expr.block ⟨#[(r, some (.named "u64"), call)], .unitVal⟩)
      else pure call
    let mut body ← wrapIOResult t v
    for (n, pt) in (names.zip ps).reverse do
      body := .lam n pt (.ofExpr body)
    vals := vals.push body
  return .ctor sn none vals

/-- A generated function folding a Lean `List` into an accumulator:
`go(l, acc)` = `acc` extended with every element via `step(acc, x)`. Cached
by name. -/
def listFold (name : String) (listTy accTy elemTy : RR.Ty) (step : RR.Expr → RR.Expr → RR.Expr) :
    LowerM String := do
  if (← get).fns.any fun | .fn n .. => n == name | _ => false then return name
  let .named lt := listTy | throwError "lean2rr: bad list type"
  let some info := (← get).typeInfos[lt]? | throwError "lean2rr: bad list type"
  let some nil := info.ctors.find? ``List.nil | throwError "lean2rr: bad list type"
  let some cons := info.ctors.find? ``List.cons | throwError "lean2rr: bad list type"
  let body : RR.Block := .ofExpr (.mtch (.var "l") #[
    { ty := lt, ctor := some nil.variant, binders := #[], body := .ofExpr (.var "acc") },
    { ty := lt, ctor := some cons.variant, binders := #[some "x", some "t"],
      body := .ofExpr (.call name #[] #[.var "t", step (.var "acc") (.var "x")]) }])
  let _ := elemTy
  modify fun s => { s with fns := s.fns.push (.fn name #[("l", listTy), ("acc", accTy)] accTy body) }
  return name

/-- Externs whose results mention Lean-defined types get generated glue
(translation plan §5.8); returns `none` for ordinary externs. -/
def customExtern (orig : Name) (params : Array Expr) (ret : Expr) (args : Array RR.Expr) :
    LowerM (Option RR.Expr) := do
  -- Tasks run eagerly and thunks are called on demand: the glue follows the
  -- reference bodies of these externs in Lean's source (translation plan §6).
  -- `Task α` and `Thunk α` are Lean's one-field structures.
  let structOf (t : Expr) : LowerM String := do
    match ← lowerType t with
    | .named n => return n
    | rt => throwError "lean2rr: expected a structure type, got {rt.render}"
  match orig with
  | ``Task.get => return some (.field args[0]! 0)
  | ``Task.spawn => return some (.ctor (← structOf ret) none #[.apply args[0]! .unitVal])
  | ``Task.map => return some (.ctor (← structOf ret) none #[.apply args[0]! (.field args[1]! 0)])
  | ``Task.bind => return some (.apply args[1]! (.field args[0]! 0))
  | ``Thunk.pure =>
    let x ← fresh "tu"
    return some (.ctor (← structOf ret) none #[.lam x RR.Ty.unit (.ofExpr args[0]!)])
  | ``Thunk.get => return some (.apply (.field args[0]! 0) .unitVal)
  -- BaseIO task combinators, run eagerly: `asTask act := Task.pure <$> act`,
  -- `mapTask f t := Task.pure <$> f t.get`, `bindTask t f := f t.get`,
  -- `wait t := pure t.get`. Results are `ST.Out` structs.
  | ``IO.asTask =>
    let resTy ← lowerType ret
    let taskTy ← ioPayloadTy resTy
    let .named taskN := taskTy | return none
    let r ← fresh "at"
    let rTy ← match ← lowerType params[0]! with | .fn _ c => pure c | t => pure t
    return some (.block ⟨#[(r, some rTy, .apply args[0]! args[2]!)],
      ← wrapIOResult resTy (.ctor taskN none #[.field (.var r) 0])⟩)
  | ``IO.mapTask =>
    let resTy ← lowerType ret
    let taskTy ← ioPayloadTy resTy
    let .named taskN := taskTy | return none
    let r ← fresh "mt"
    let fTy ← lowerType params[0]!
    let rTy := match fTy with | .fn _ (.fn _ c) => c | t => t
    return some (.block ⟨#[(r, some rTy, .apply (.apply args[0]! (.field args[1]! 0)) args[4]!)],
      ← wrapIOResult resTy (.ctor taskN none #[.field (.var r) 0])⟩)
  | ``IO.bindTask => return some (.apply (.apply args[1]! (.field args[0]! 0)) args[4]!)
  | ``IO.wait => return some (← wrapIOResult (← lowerType ret) (.field args[0]! 0))
  -- `IO.Process.exit : UInt8 → IO α` never returns.
  | ``IO.Process.exit =>
    let rt ← lowerType ret
    let e ← fresh "ex"
    return some (.block ⟨#[(e, some (.named "u64"), .call "l2r_process_exit" #[] #[args[0]!])],
      .call "l2r_unreachable" #[rt] #[]⟩)
  | _ => pure ()
  -- `String.ofList : List Char → String`
  if orig == ``String.ofList then
    let lt ← lowerType params[0]!
    let fn ← listFold s!"l2r_list_to_string_{lt.render.map fun c => if c.isAlphanum then c else '_'}" lt
      (.named "LStr") (.named "u32") fun acc x => .call "lean_string_push" #[] #[acc, x]
    return some (.call fn #[] #[args[0]!, .call "lean_mk_string" #[] #[.atom "\"\""]])
  -- `Array.mk : List α → Array α`
  if orig == ``Array.mk then
    let lt ← lowerType params[0]!
    let arrTy ← lowerType ret
    let .app _ #[elemTy] := arrTy | throwError "lean2rr: bad array type {arrTy.render}"
    -- The list holds unboxed elements; wrap them if the array stores boxes.
    let .named ltn := lt | throwError "lean2rr: bad list type"
    let some info := (← get).typeInfos[ltn]? | throwError "lean2rr: bad list type"
    let some cons := info.ctors.find? ``List.cons | throwError "lean2rr: bad list type"
    let some (some (_, valTy)) := cons.fields[0]? | throwError "lean2rr: bad list type"
    let (_, boxed) ← arrayElemTy valTy
    let wrap (x : RR.Expr) : RR.Expr := match elemTy with
      | .named en => if boxed then .ctor en none #[x] else x
      | _ => x
    let fn ← listFold s!"l2r_list_to_array_{lt.render.map fun c => if c.isAlphanum then c else '_'}" lt arrTy
      elemTy fun acc x => .call "l2r_array_push" #[] #[acc, wrap x]
    return some (.call fn #[] #[args[0]!, .call "l2r_array_empty" #[elemTy] #[]])
  let fd? : Option Nat := match orig with
    | ``IO.getStdin => some 0
    | ``IO.getStdout => some 1
    | ``IO.getStderr => some 2
    | _ => none
  if let some fd := fd? then
    -- BaseIO FS.Stream: the result is `ST.Out σ FS.Stream`.
    let resTy ← lowerType ret
    let .named rn := resTy | return none
    let some info := (← get).typeInfos[rn]? | return none
    let some layout := info.ctors.find? info.ctorOrder[0]! | return none
    let some (some (_, streamTy)) := layout.fields[0]? | return none
    return some (← wrapIOResult resTy (← streamValue fd streamTy))
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
  if let some e ← customExtern orig params ret args then return e
  let sym ← externSymbol orig
  -- Storage for each type argument: (Lean type, storage type, boxed?).
  let mut storage := #[]
  for t in typeArgs do
    let rt ← lowerType t
    let (st, boxed) ← arrayElemTy rt
    storage := storage.push (t.consumeMData, st, boxed)
  let boxOf (t : Expr) : Option RR.Ty :=
    storage.findSome? fun (lt, st, boxed) => if boxed && lt == t.consumeMData then some st else none
  let mut passed := #[]
  for (p, a) in params.zip args do
    if externParamPassed p then
      match boxOf p with
      | some (.named bn) => passed := passed.push (.ctor bn none #[a])
      | _ => passed := passed.push a
  let call := RR.Expr.call sym (storage.map (·.2.1)) passed
  match boxOf ret with
  | some _ => return .field call 0
  | none => return call

/-! ## Values -/

def natLiteral (n : Nat) : RR.Expr :=
  if n < 2 ^ 63 then .ctor "Nat" (some "Small") #[.atom (toString n)]
  else .call "lean_cstr_to_nat" #[] #[.atom (n.repr.quote)]

/-- Lower a constant application with Lean's arity rules. -/
def lowerConstApp (ctx : CodeCtx) (f : Name) (args : Array (Arg .pure)) (resTy : Expr) :
    LowerM RR.Expr := do
  match ← calleeOf f with
  | .code fn params ret =>
    let n := params.size
    if args.size == n then
      let as ← (args.zip params).mapM fun (a, t) => lowerArg ctx a t
      return .call fn #[] as
    else if args.size < n then
      let supplied ← (args.zip params).mapM fun (a, t) => lowerArg ctx a t
      lambdaChain params[args.size:].toArray fun rest => return .call fn #[] (supplied ++ rest)
    else
      let as ← (args[:n].toArray.zip params).mapM fun (a, t) => lowerArg ctx a t
      return (← applyChain (.call fn #[] as) ret ctx args[n:].toArray).1
  | .extern orig typeArgs params ret =>
    let n := params.size
    let ptys ← params.mapM lowerType
    let retTy ← lowerType ret
    if args.size == n then
      let as ← (args.zip ptys).mapM fun (a, t) => lowerArg ctx a t
      lowerExternCall orig typeArgs params ret as
    else if args.size < n then
      let supplied ← (args.zip ptys).mapM fun (a, t) => lowerArg ctx a t
      lambdaChain ptys[args.size:].toArray fun rest => lowerExternCall orig typeArgs params ret (supplied ++ rest)
    else
      let as ← (args[:n].toArray.zip ptys).mapM fun (a, t) => lowerArg ctx a t
      let call ← lowerExternCall orig typeArgs params ret as
      return (← applyChain call retTy ctx args[n:].toArray).1
  | .ctor c =>
    let arity := c.numParams + c.numFields
    let rt ← lowerType (← if args.size ≥ arity then pure resTy else pure resTy)
    -- The instance is determined by the result type of a saturated
    -- application; for a partial application, by the codomain.
    let (_, fullTy) := splitFnType resTy (arity - min arity args.size)
    let fullRt ← if args.size ≥ arity then pure rt else lowerType fullTy
    let build (vals : Array RR.Expr) : LowerM RR.Expr := do
      match fullRt with
      | .named "bool" => return .atom (if c.name == ``Bool.true then "true" else "false")
      | .named "L2RUnit" => return .unitVal
      | .named tn =>
        match (← get).typeInfos[tn]? with
        | some info =>
          let some layout := info.ctors.find? c.name
            | throwError "lean2rr: constructor {c.name} not in type {tn}"
          let mut fieldVals := #[]
          for h : i in [:layout.fields.size] do
            if let some _ := layout.fields[i] then
              fieldVals := fieldVals.push vals[layout.numParams + i]!
          match info.shape with
          | .struct => return .ctor tn none fieldVals
          | _ => return .ctor tn (some layout.variant) fieldVals
        | none => throwError "lean2rr: constructor {c.name} of non-nominal type {tn}"
      | t => throwError "lean2rr: constructor {c.name} at type {t.render}"
    -- Expected Reussir types of the constructor's arguments.
    let argTys ← do
      match fullRt with
      | .named tn =>
        match (← get).typeInfos[tn]? with
        | some info =>
          let some layout := info.ctors.find? c.name | pure (Array.replicate arity RR.Ty.unit)
          pure <| (Array.replicate layout.numParams RR.Ty.unit) ++ layout.fields.map fun
            | some (_, t) => t
            | none => RR.Ty.unit
        | none => pure (Array.replicate arity RR.Ty.unit)
      | _ => pure (Array.replicate arity RR.Ty.unit)
    let vals ← (args.zip argTys).mapM fun (a, t) => lowerArg ctx a t
    if args.size ≥ arity then build vals
    else lambdaChain argTys[args.size:].toArray fun rest => build (vals ++ rest)

def lowerLetValue (ctx : CodeCtx) (v : LetValue .pure) (ty : Expr) (rty : RR.Ty) : LowerM RR.Expr := do
  match v with
  | .lit (.nat n) => coerce (natLiteral n) (.named "Nat") rty
  | .lit (.str s) => coerce (.call "lean_mk_string" #[] #[.atom s.quote]) (.named "LStr") rty
  | .lit (.uint8 n) | .lit (.uint16 n) => return .atom (toString n)
  | .lit (.uint32 n) => return .atom (toString n)
  | .lit (.uint64 n) | .lit (.usize n) => return .atom (toString n)
  | .erased => coerce .unitVal .unit rty
  | .proj _ i x _ =>
    match ctx.vars[x]? with
    | some (n, .named tn) =>
      match (← get).typeInfos[tn]? with
      | some info =>
        let some layout := info.ctors.find? info.ctorOrder[0]! | throwError "lean2rr: bad projection"
        match layout.fields[i]? with
        | some (some (j, ft)) => coerce (.field (.var n) j) ft rty
        | _ => coerce .unitVal .unit rty
      | none => throwError "lean2rr: projection from non-structure {tn}"
    | _ => throwError "lean2rr: projection from unknown variable"
  | .const f _ args _ => lowerConstApp ctx f args ty
  | .fvar g args =>
    match ctx.vars[g]? with
    | some (n, t) =>
      let (e, t') ← applyChain (.var n) t ctx args
      coerce e t' rty
    | none => throwError "lean2rr: unbound function variable (internal error)"
  | _ => throwError "lean2rr: impure let value (internal error)"

/-! ## Join-point strategy -/

/-- Number of jumps to each join point. -/
partial def countJumps : Code .pure → Std.HashMap FVarId Nat → Std.HashMap FVarId Nat
  | .jmp j _, m => m.insert j (m.getD j 0 + 1)
  | .let _ k, m => countJumps k m
  | .fun d k _, m | .jp d k, m => countJumps k (countJumps d.value m)
  | .cases c, m => c.alts.foldl (fun m alt => countJumps alt.getCode m) m
  | _, m => m

/-- Does every path through `c` end in a jump to one of `targets` (or in
`unreach`)? Nested join points in `outlined` are functions, so jumping to
them does not count. -/
partial def endsInJumps (c : Code .pure) (targets : FVarIdSet) (outlined : FVarIdSet) : Bool :=
  match c with
  | .let _ k => endsInJumps k targets outlined
  | .fun _ k _ => endsInJumps k targets outlined
  | .jmp j _ => targets.contains j
  | .unreach _ => true
  | .return _ => false
  | .cases cs => cs.alts.all fun alt => endsInJumps alt.getCode targets outlined
  | .jp d k =>
    if !outlined.contains d.fvarId && endsInJumps d.value targets outlined then
      endsInJumps k (targets.insert d.fvarId) outlined
    else endsInJumps k targets outlined
  | _ => false

/-- Join points jumped to from inside the body of join point `inside`. -/
partial def jumpsIn : Code .pure → FVarIdSet → FVarIdSet
  | .jmp j _, s => s.insert j
  | .let _ k, s => jumpsIn k s
  | .fun d k _, s | .jp d k, s => jumpsIn k (jumpsIn d.value s)
  | .cases c, s => c.alts.foldl (fun s alt => jumpsIn alt.getCode s) s
  | _, s => s

/-- Choose a strategy for every join point of a declaration body: the set
of outlined (J3) join points; others are J1 (single jump) or J2. -/
partial def chooseOutlined (body : Code .pure) : FVarIdSet := Id.run do
  let counts := countJumps body {}
  -- All join points with their scope.
  let mut jps : Array (FunDecl .pure × Code .pure) := #[]
  let rec gather (c : Code .pure) (acc : Array (FunDecl .pure × Code .pure)) : Array (FunDecl .pure × Code .pure) :=
    match c with
    | .let _ k => gather k acc
    | .fun d k _ => gather k (gather d.value acc)
    | .jp d k => gather k (gather d.value (acc.push (d, k)))
    | .cases cs => cs.alts.foldl (fun acc alt => gather alt.getCode acc) acc
    | _ => acc
  jps := gather body #[]
  let mut outlined : FVarIdSet := {}
  let mut changed := true
  while changed do
    changed := false
    for (d, k) in jps do
      if outlined.contains d.fvarId then continue
      let single := counts.getD d.fvarId 0 ≤ 1
      -- A J2 join point cannot be the target of a jump from inside an outlined body.
      let jumpedFromOutlined := jps.any fun (d', _) =>
        outlined.contains d'.fvarId && (jumpsIn d'.value {}).contains d.fvarId
      let ok := single || (endsInJumps k (({} : FVarIdSet).insert d.fvarId) outlined && !jumpedFromOutlined)
      if !ok then
        outlined := outlined.insert d.fvarId
        changed := true
  return outlined

/-! ## Code -/

/-- Free variable names of an RR expression/block (for outlined join points). -/
partial def rrFreeVars (e : RR.Expr) (bound : Std.HashSet String) (acc : Std.HashSet String) : Std.HashSet String :=
  match e with
  | .var n => if bound.contains n || n.startsWith "L2RUnit" then acc else acc.insert n
  | .atom _ => acc
  | .call _ _ args => args.foldl (fun acc a => rrFreeVars a bound acc) acc
  | .apply f a => rrFreeVars a bound (rrFreeVars f bound acc)
  | .ctor _ _ args => args.foldl (fun acc a => rrFreeVars a bound acc) acc
  | .field e _ => rrFreeVars e bound acc
  | .lam x _ b => blockFreeVars b (bound.insert x) acc
  | .ite c t f => blockFreeVars f bound (blockFreeVars t bound (rrFreeVars c bound acc))
  | .mtch s arms => arms.foldl (fun acc arm =>
      let bound := arm.binders.foldl (fun b x => match x with | some x => b.insert x | none => b) bound
      blockFreeVars arm.body bound acc) (rrFreeVars s bound acc)
  | .block b => blockFreeVars b bound acc
where
  blockFreeVars (b : RR.Block) (bound : Std.HashSet String) (acc : Std.HashSet String) : Std.HashSet String :=
    let (bound, acc) := b.lets.foldl (fun (bound, acc) (x, _, e) => (bound.insert x, rrFreeVars e bound acc)) (bound, acc)
    rrFreeVars b.result bound acc

mutual
  /-- Lower a code block whose value has Reussir type `retTy`. -/
  partial def lowerCode (ctx : CodeCtx) (outlined : FVarIdSet) (retTy : RR.Ty) (c : Code .pure) :
      LowerM RR.Block := do
    match c with
    | .let d k =>
      let t ← lowerType d.type
      let e ← lowerLetValue ctx d.value d.type t
      let x ← fresh "x"
      let b ← lowerCode { ctx with vars := ctx.vars.insert d.fvarId (x, t) } outlined retTy k
      return { b with lets := #[(x, some t, e)] ++ b.lets }
    | .return x =>
      match ctx.vars[x]? with
      | some (n, t) => return .ofExpr (← coerce (.var n) t retTy)
      | none => throwError "lean2rr: return of unbound variable (internal error)"
    | .unreach _ => return .ofExpr (.call "l2r_unreachable" #[retTy] #[])
    | .cases cs => return .ofExpr (← lowerCases ctx outlined retTy cs)
    | .jmp j args =>
      match ctx.jumps[j]? with
      | some (.inline params body) =>
        -- J1: bind the parameters to the arguments, then the body.
        let mut ctx' := ctx
        let mut lets := #[]
        for (p, a) in params.zip args do
          let t ← lowerType p.type
          let x ← fresh "j"
          lets := lets.push (x, some t, ← lowerArg ctx a t)
          ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, t) }
        let b ← lowerCode ctx' outlined retTy body
        return { b with lets := lets ++ b.lets }
      | some (.yield tys) =>
        let vals ← (args.zip tys).mapM fun (a, t) => lowerArg ctx a t
        match vals.size with
        | 0 => return .ofExpr .unitVal
        | 1 => return .ofExpr vals[0]!
        | _ => return .ofExpr (.ctor (← tupleType tys) none vals)
      | some (.call fn captured) =>
        let tys := ctx.jpParams.getD j #[]
        let vals ← (args.zip tys).mapM fun (a, t) => lowerArg ctx a t
        return .ofExpr (.call fn #[] (captured.map .var ++ vals))
      | none => throwError "lean2rr: jump to unknown join point (internal error)"
    | .jp d k =>
      let ptys ← d.params.mapM (lowerType ·.type)
      let ctx := { ctx with jpParams := ctx.jpParams.insert d.fvarId ptys }
      if outlined.contains d.fvarId then
        -- J3: outline the body into a function over its free variables.
        let pnames ← d.params.mapM fun _ => fresh "p"
        let vars := (d.params.zip (pnames.zip ptys)).foldl (fun m (p, nt) => m.insert p.fvarId nt) ctx.vars
        let bodyCtx := { ctx with vars }
        let body ← lowerCode bodyCtx outlined retTy d.value
        let bound := pnames.foldl (·.insert ·) ({} : Std.HashSet String)
        let free := (rrFreeVars.blockFreeVars body bound {}).toArray.qsort (· < ·)
        let varTys : Std.HashMap String RR.Ty := ctx.vars.fold (fun m _ (n, t) => m.insert n t) {}
        let captured := free.filter varTys.contains
        let fn ← fresh "jp_"
        let fparams := captured.map (fun n => (n, varTys.getD n .unit)) ++ pnames.zip ptys
        modify fun s => { s with fns := s.fns.push (.fn fn fparams retTy body) }
        lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.call fn captured) } outlined retTy k
      else if (countJumps k {}).getD d.fvarId 0 ≤ 1 then
        lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.inline d.params d.value) } outlined retTy k
      else
        -- J2: the scope computes the join point's arguments.
        let resTy ← match ptys.size with
          | 0 => pure RR.Ty.unit
          | 1 => pure ptys[0]!
          | _ => pure (RR.Ty.named (← tupleType ptys))
        let scope ← lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.yield ptys) } outlined resTy k
        let r ← fresh "jv"
        let mut lets : Array (String × Option RR.Ty × RR.Expr) := #[(r, some resTy, .block scope)]
        let mut ctx' := ctx
        for h : i in [:d.params.size] do
          let p := d.params[i]
          let x ← fresh "y"
          let e := if ptys.size == 1 then RR.Expr.var r else .field (.var r) i
          lets := lets.push (x, some ptys[i]!, e)
          ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, ptys[i]!) }
        let b ← lowerCode ctx' outlined retTy d.value
        return { b with lets := lets ++ b.lets }
    | .fun d k _ =>
      -- Lambda lifting normally removes local functions; lower defensively.
      let ptys ← d.params.mapM (lowerType ·.type)
      let pnames ← d.params.mapM fun _ => fresh "lp"
      let (_, rt) := splitFnType d.type d.params.size
      let rt ← lowerType rt
      let vars := (d.params.zip (pnames.zip ptys)).foldl (fun m (p, nt) => m.insert p.fvarId nt) ctx.vars
      let bodyCtx := { ctx with vars }
      let body ← lowerCode bodyCtx outlined rt d.value
      let mut lam := RR.Expr.block body
      for (n, t) in (pnames.zip ptys).reverse do lam := .lam n t (.ofExpr lam)
      let fty := (ptys.foldr (fun a b => RR.Ty.fn a b) rt)
      let x ← fresh "f"
      let b ← lowerCode { ctx with vars := ctx.vars.insert d.fvarId (x, fty) } outlined retTy k
      return { b with lets := #[(x, some fty, lam)] ++ b.lets }
    | _ => throwError "lean2rr: impure code (internal error)"

  partial def lowerCases (ctx : CodeCtx) (outlined : FVarIdSet) (retTy : RR.Ty) (cs : Cases .pure) :
      LowerM RR.Expr := do
    let some (scrut, sty) := ctx.vars[cs.discr]? | throwError "lean2rr: cases on unbound variable"
    let altFor (ctor : Name) : Option (Alt .pure) := cs.alts.find? fun
      | .alt c _ _ _ => c == ctor
      | _ => false
    let dflt : Option (Code .pure) := cs.alts.findSome? fun
      | .default k => some k
      | _ => none
    match sty with
    | .named "bool" =>
      let branch (ctor : Name) : LowerM RR.Block := do
        match altFor ctor with
        | some alt => lowerCode ctx outlined retTy alt.getCode
        | none =>
          match dflt with
          | some k => lowerCode ctx outlined retTy k
          | none => return .ofExpr (.call "l2r_unreachable" #[retTy] #[])
      return .ite (.var scrut) (← branch ``Bool.true) (← branch ``Bool.false)
    | .named tn =>
      let some info := (← get).typeInfos[tn]?
        | throwError "lean2rr: cases on non-nominal type {tn} ({cs.typeName})"
      match info.shape with
      | .struct =>
        let some alt := cs.alts[0]? | throwError "lean2rr: empty cases"
        match alt with
        | .alt ctor ps k _ =>
          let some layout := info.ctors.find? ctor | throwError "lean2rr: bad constructor"
          let mut ctx' := ctx
          let mut lets := #[]
          for h : i in [:ps.size] do
            let p := ps[i]
            match layout.fields[i]? with
            | some (some (j, ft)) =>
              let x ← fresh "f"
              lets := lets.push (x, some ft, RR.Expr.field (.var scrut) j)
              ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, ft) }
            | _ => ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId ("L2RUnit::u{}", .unit) }
          let b ← lowerCode ctx' outlined retTy k
          return .block { b with lets := lets ++ b.lets }
        | .default k => return .block (← lowerCode ctx outlined retTy k)
        | _ => throwError "lean2rr: impure alternative"
      | _ =>
        let mut arms := #[]
        for ctor in info.ctorOrder do
          let some layout := info.ctors.find? ctor | continue
          match altFor ctor with
          | some (.alt _ ps k _) =>
            let mut ctx' := ctx
            let mut binders := Array.replicate (layout.fields.filter (·.isSome)).size (none : Option String)
            for h : i in [:ps.size] do
              let p := ps[i]
              match layout.fields[i]? with
              | some (some (j, ft)) =>
                let x ← fresh "f"
                binders := binders.set! j (some x)
                ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, ft) }
              | _ => ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId ("L2RUnit::u{}", .unit) }
            arms := arms.push { ty := tn, ctor := some layout.variant, binders, body := ← lowerCode ctx' outlined retTy k }
          | _ => pure ()
        if arms.size < info.ctorOrder.size then
          let body ← match dflt with
            | some k => lowerCode ctx outlined retTy k
            | none => pure (.ofExpr (.call "l2r_unreachable" #[retTy] #[]))
          arms := arms.push { ty := tn, ctor := none, binders := #[], body }
        return .mtch (.var scrut) arms
    | t => throwError "lean2rr: cases on value of type {t.render} ({cs.typeName})"
end

/-- Lower a declaration with code to a Reussir function. -/
def lowerDecl (d : Decl .pure) : LowerM Unit := do
  let .code body := d.value | return
  let (ps, r) := splitFnType d.type d.params.size
  let _ := ps
  let ptys ← d.params.mapM (lowerType ·.type)
  let ret ← lowerType r
  let pnames ← d.params.mapM fun _ => fresh "a"
  let ctx : CodeCtx := { vars := (d.params.zip (pnames.zip ptys)).foldl (fun m (p, nt) => m.insert p.fvarId nt) {} }
  let block ← try lowerCode ctx (chooseOutlined body) ret body
    catch e => throwError "{e.toMessageData}\n  while lowering {d.name}"
  modify fun s => { s with fns := s.fns.push (.fn (fnName d.name) (pnames.zip ptys) ret block) }

end LeanToReussir
