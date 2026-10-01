import LeanToReussir.Lower.ExternCall

/-! # Values -/

namespace LeanToReussir
open Lean Compiler LCNF

/-- A `Nat` literal: `Small` below 2^64, otherwise parsed by the runtime
from its decimal digits in the string literal table (a flat call: a nested
arithmetic expression per limb overflowed rrc's stack for literals of
thousands of digits, and cost quadratic time). -/
def natLiteral (n : Nat) : LowerM RR.Expr := do
  if n < 2 ^ 64 then return .ctor "Nat" (some "Small") #[.atom (toString n)]
  return .call "l2r_nat_norm" #[] #[.call "l2r_big_of_decimal_lstr" #[] #[← strLit (toString n)]]

/-- Constructor `c` applied to all its arguments `vals` (parameters, then
fields), building a value of `fullRt`. -/
def ctorBuild (c : Name) (fullRt : RR.Ty) (vals : Array RR.Expr) : LowerM RR.Expr := do
  match fullRt with
  | .named "bool" => return .atom (if c == ``Bool.true then "true" else "false")
  | .named "L2RUnit" => return .unitVal
  | .named tn =>
    match (← get).typeInfos[tn]? with
    | some info =>
      let some layout := info.ctors.find? c
        | throwError "lean2rr: constructor {c} not in type {tn}"
      let mut fieldVals := #[]
      for h : i in [:layout.fields.size] do
        if let some (_, t) := layout.fields[i] then
          -- Hidden fields (`IO.Process.Child`'s) have no Lean argument.
          fieldVals := fieldVals.push (← match vals[layout.numParams + i]? with
            | some v => pure v
            | none => zeroValue t)
      let placedVals := layout.place fieldVals
      match info.shape with
      | .struct => return .ctor tn none placedVals
      | _ => return .ctor tn (some layout.variant) placedVals
    | none => throwError "lean2rr: constructor {c} of non-nominal type {tn}"
  | t => throwError "lean2rr: constructor {c} at type {t.render}"

/-- Lean definitions replaced by prelude functions with the same results
(runtime requests 12, 27): `Nat.repr` divides by 10 digit by digit, and
`Nat.reprFast` reads a table of strings through a once-cell. -/
def preludeReplacement? (f : Name) : LowerM (Option (String × RR.Ty)) := do
  let orig := ((← read).keys.find? f).map (·.decl) |>.getD f
  match orig with
  | ``Nat.repr | ``Nat.reprFast => return some ("l2r_nat_repr", .named "Nat")
  | ``Int.repr => return some ("l2r_int_repr", .named "Int")
  | _ => return none

/-- A saturated call of an `ST.Ref` operation: the reference arguments are
passed at their own representation (a typed reference, or a `Box`; see
`refGlue`), not converted to the extern's parameter type (`lcAny`, which
would box a typed reference). -/
def refCall? (ctx : CodeCtx) (orig : Name) (typeArgs : Array Expr) (params : Array Expr) (ret : Expr)
    (args : Array (Arg .pure)) : LowerM (Option RR.Expr) := do
  unless orig.getPrefix == `ST.Prim.Ref do return none
  let mut ps := #[]
  let mut as := #[]
  let mut ts := #[]
  for (a, p) in args.zip params do
    let p' := p.consumeMData
    if p'.isErased || p'.isSort then continue
    let pt ← lowerType p
    -- The references: the first relevant parameter (both, for `ptrEq`).
    let handle := ps.size == 0 || (orig == ``ST.Prim.Ref.ptrEq && ps.size == 1)
    match a, handle with
    | .fvar x, true =>
      let some (vn, vt) := ctx.vars[x]? | throwError "lean2rr: unbound variable {x.name} (internal error)"
      as := as.push (RR.Expr.var vn)
      ts := ts.push vt
    | _, _ =>
      as := as.push (← lowerArg ctx a pt)
      ts := ts.push pt
    ps := ps.push p
  refGlue orig typeArgs ps ret as ts

/-- Lower a constant application with Lean's arity rules. -/
def lowerConstApp (ctx : CodeCtx) (f : Name) (args : Array (Arg .pure)) (resTy : Expr) :
    LowerM RR.Expr := do
  if args.size == 1 then
    if let some (prim, argTy) ← preludeReplacement? f then
      return ← coerce (.call prim #[] #[← lowerArg ctx args[0]! argTy]) (.named "LStr") (← lowerType resTy)
  match ← calleeOf f with
  | .initConst slot ty =>
    let t ← lowerType ty
    let (st, boxed) ← arrayElemTy t
    let v := RR.Expr.call "l2r_once_get" #[st] #[.atom (toString slot)]
    let v := if boxed then .field v 0 else v
    let (e, t) ← applyChain v t ctx args
    coerce e t (← lowerType resTy)
  | .code fn params ret =>
    let n := params.size
    if args.size == n then
      let as ← (args.zip params).mapM fun (a, t) => lowerArg ctx a t
      coerce (.call fn #[] as) ret (← lowerType resTy)
    else if args.size < n then
      let supplied ← (args.zip params).mapM fun (a, t) => lowerArg ctx a t
      partialApp { id := "d" ++ fn, params, ret, call := .code fn } supplied (← lowerType resTy)
    else
      let as ← (args[:n].toArray.zip params).mapM fun (a, t) => lowerArg ctx a t
      let (e, t) ← applyChain (.call fn #[] as) ret ctx args[n:].toArray
      coerce e t (← lowerType resTy)
  | .extern orig typeArgs params ret =>
    let n := params.size
    let ptys ← params.mapM lowerType
    let retTy ← lowerType ret
    if args.size == n then
      -- `ptrAddrUnsafe x`: the identity of `x` in its own representation
      -- (converted to the parameter's, it would be another object).
      if (← externSymbol orig) == "lean_ptr_addr" then
        if let some (.fvar x) := args.back? then
          if let some (vn, vt) := ctx.vars[x]? then
            return ← coerce (← addrOf (.var vn) vt) (.named "u64") (← lowerType resTy)
      if let some e ← refCall? ctx orig typeArgs params ret args then
        return ← coerce e retTy (← lowerType resTy)
      let as ← (args.zip ptys).mapM fun (a, t) => lowerArg ctx a t
      coerce (← lowerExternCall orig typeArgs params ret as) retTy (← lowerType resTy)
    else if args.size < n then
      let supplied ← (args.zip ptys).mapM fun (a, t) => lowerArg ctx a t
      partialApp { id := "e" ++ fnName f, params := ptys, ret := retTy, call := .extern orig typeArgs params ret }
        supplied (← lowerType resTy)
    else
      let as ← (args[:n].toArray.zip ptys).mapM fun (a, t) => lowerArg ctx a t
      let call ← lowerExternCall orig typeArgs params ret as
      let (e, t) ← applyChain call retTy ctx args[n:].toArray
      coerce e t (← lowerType resTy)
  | .ctor c =>
    let arity := c.numParams + c.numFields
    let rt ← lowerType (← if args.size ≥ arity then pure resTy else pure resTy)
    -- The instance is determined by the result type of a saturated
    -- application; for a partial application, by the codomain.
    let (_, fullTy) := splitFnType resTy (arity - min arity args.size)
    let fullRt ← if args.size ≥ arity then pure rt else lowerType fullTy
    -- Expected Reussir types of the constructor's arguments.
    let argTys ← do
      match fullRt with
      | .named tn =>
        match (← get).typeInfos[tn]? with
        | some info =>
          let some layout := info.ctors.find? c.name | pure (Array.replicate arity RR.Ty.unit)
          let tys := (Array.replicate layout.numParams RR.Ty.unit) ++ layout.fields.map fun
            | some ((_ : Nat), t) => t
            | none => RR.Ty.unit
          pure (tys.extract 0 arity)
        | none => pure (Array.replicate arity RR.Ty.unit)
      | _ => pure (Array.replicate arity RR.Ty.unit)
    let vals ← (args.zip argTys).mapM fun (a, t) => lowerArg ctx a t
    if args.size ≥ arity then ctorBuild c.name fullRt vals
    else partialApp { id := "k" ++ fullRt.enc ++ "_" ++ fnName c.name, params := argTys, ret := fullRt,
                      call := .ctor c.name fullRt } vals (← lowerType resTy)

/-- How a `cases` (or projection) of inductive `typeName` treats a
discriminant of Reussir type `sty`. Mono erases `unsafeCast`, so the
discriminant can be a value of another type that Lean represents alike
(translation plan §5.5): an inductive with the same constructor shapes, a
`Nat` or `UInt8` used as an enumeration. -/
inductive CastCases where
  /-- A value of `typeName` (the usual case). -/
  | same
  /-- A value of isomorphic inductive `sn` (§5.1), matched as `dn`, an
  instance of `typeName`: constructors correspond by position, relevant
  fields by position (`viewLayout`), and are bound at their own types. -/
  | view (sn dn : String)
  /-- Converted to `typeName`'s instance `dst` first (enumerations by index;
  where no conversion exists, `coerce` warns and the cast panics). -/
  | convert (dst : RR.Ty)
  /-- `typeName` has no representation (its values carry nothing). -/
  | unit

def castCases (sty : RR.Ty) (typeName : Name) : LowerM CastCases := do
  let sameHead (h : Name) := h == typeName || h == typeName ++ `_impl || typeName == h ++ `_impl
  let tn := match sty with | .named n => n | _ => ""
  let infos := (← get).typeInfos
  let nominal := infos.contains tn
  if nominal then
    let some h ← nominalHead tn | return .same
    if sameHead h then return .same
  else if tn == "bool" && typeName == ``Bool then return .same
  -- The instance of `typeName` to match against: at the discriminant's
  -- type arguments when the parameter counts agree (`Option Nat` cast to
  -- `MyOpt Nat`), otherwise the uniform one.
  let uniform ← uniformType typeName
  if uniform == .unit then return .unit
  if uniform == sty || uniform == RR.Ty.box then return .same
  if nominal then
    let mut cands : Array RR.Ty := #[]
    if let some k := (← get).typeKeys[tn]? then
      if let some (.inductInfo ival) := (← getEnv).find? typeName then
        if ival.numParams == k.getAppNumArgs && ival.numParams > 0 then
          cands := cands.push (← lowerTypeApp typeName k.getAppArgs)
    cands := cands.push uniform
    for dt in cands do
      if let .named dn := dt then
        if (← get).typeInfos.contains dn && (← isomorphic tn dn) then return .view tn dn
  return .convert uniform

/-- The layout of constructor `dc` (layout `dl`, of the instance a cast
value is matched as) over the record of the corresponding constructor `sc`
(layout `sl`) of the value's own type: each field of `dl` is the field of
`sl` it reads natively (`castFieldMap`), at its record position and type (as
`structConv` converts). A field reading nothing here is a placeholder. -/
def viewLayout (sc dc : Name) (sl dl : CtorLayout) : LowerM CtorLayout := do
  let fm := (← castFieldMap sc dc sl dl).getD #[]
  let fields := (List.range dl.fields.size).toArray.map fun j =>
    match fm[j]?.join.join with
    | some k => sl.fields[k]?.join
    | none => none
  return { variant := sl.variant, numParams := dl.numParams, fields }

def lowerLetValue (ctx : CodeCtx) (v : LetValue .pure) (ty : Expr) (rty : RR.Ty) : LowerM RR.Expr := do
  match v with
  | .lit (.nat n) => coerce (← natLiteral n) (.named "Nat") rty
  | .lit (.str s) => coerce (← strLit s) (.named "LStr") rty
  | .lit (.uint8 n) | .lit (.uint16 n) => return .atom (toString n)
  | .lit (.uint32 n) => return .atom (toString n)
  | .lit (.uint64 n) | .lit (.usize n) => return .atom (toString n)
  | .erased => zeroValue rty
  | .proj sn i x _ =>
    match ctx.vars[x]? with
    | some (n, st) =>
      -- A projection of a cast value: as a `cases` (see `castCases`).
      let (e, tn, layout?) ← match ← castCases st sn with
        | .view src dst =>
          let si := (← get).typeInfos[src]?
          let di := (← get).typeInfos[dst]?
          let sc := si.bind (·.ctorOrder[0]?)
          let dc := di.bind (·.ctorOrder[0]?)
          let sl := si.bind fun i => i.ctorOrder[0]?.bind i.ctors.find?
          let dl := di.bind fun i => i.ctorOrder[0]?.bind i.ctors.find?
          let layout ← match sc, dc, sl, dl with
            | some sc, some dc, some sl, some dl => some <$> viewLayout sc dc sl dl
            | _, _, _, _ => pure none
          pure (RR.Expr.var n, src, layout)
        | .convert dty =>
          let .named dn := dty | return ← zeroValue rty
          let di := (← get).typeInfos[dn]?
          pure (← coerce (.var n) st dty, dn, di.bind fun i => i.ctorOrder[0]?.bind i.ctors.find?)
        | .unit => return ← zeroValue rty
        | .same =>
          let .named tn := st | throwError "lean2rr: projection from {st.render}"
          let some info := (← get).typeInfos[tn]? | throwError "lean2rr: projection from non-structure {tn}"
          pure (RR.Expr.var n, tn, info.ctorOrder[0]?.bind info.ctors.find?)
      let some layout := layout? | throwError "lean2rr: bad projection"
      match layout.fields[i]? with
      | some (some (j, ft)) =>
        match e with
        | .var _ => coerce (.field e j) ft rty
        | _ => withVar "pv" (.named tn) e fun v => coerce (.field v j) ft rty
      | _ => zeroValue rty
    | _ => throwError "lean2rr: projection from unknown variable"
  | .const f _ args _ => lowerConstApp ctx f args ty
  | .fvar g args =>
    match ctx.vars[g]? with
    | some (n, t) =>
      let (e, t') ← applyChain (.var n) t ctx args
      coerce e t' rty
    | none => throwError "lean2rr: unbound function variable (internal error)"
  | _ => throwError "lean2rr: impure let value (internal error)"

end LeanToReussir
