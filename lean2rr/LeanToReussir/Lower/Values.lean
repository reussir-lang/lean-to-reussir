import LeanToReussir.Lower.Borrow

/-! # Values -/

namespace LeanToReussir
open Lean Compiler LCNF

/-- A `Nat` literal: a small value below 2^63 (`l2r_nat_small k`, the word
`2k + 1`), otherwise a big number parsed by the runtime from its decimal
digits in the string literal table (a flat call: a nested arithmetic
expression per limb overflowed rrc's stack for literals of thousands of
digits, and cost quadratic time). -/
def natLiteral (n : Nat) : LowerM RR.Expr := do
  if n < 2 ^ 63 then return .call "l2r_nat_small" #[] #[.atom (toString n)]
  return .call "l2r_nat_of_decimal_lstr" #[] #[← strLit (toString n)]

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

/-- The prelude function replacing a call of `f` (an instance of a Lean
definition the configuration replaces, see `LowerCtx.preludeReplacements`),
and its parameter type. -/
def preludeReplacement? (f : Name) : LowerM (Option (String × RR.Ty)) := do
  let orig := ((← read).keys.find? f).map (·.decl) |>.getD f
  return (← read).preludeReplacements.find? orig

/-- The mono function type of constructor `c` at the instance `fullTy`
(its parameters, erased in mono code, then its fields at their types there,
as `nominalType` computes them), for the type of a partial application. -/
def ctorFnType (c : ConstructorVal) (fullTy : Expr) : LowerM Expr := do
  -- The same field types as rule 4's flow analysis (`ErasedDomains`).
  return mkFnType (Array.replicate c.numParams erasedExpr ++ (← layoutFieldTypes c.name fullTy)) fullTy

/-- The arguments `args[:k]` that a callee taking the Lean parameters
`keep` (rule 4a, `keepMask`; empty: all) receives, at its parameter types
`params`. -/
def lowerTaken (ctx : CodeCtx) (args : Array (Arg .pure)) (params : Array RR.Ty) (keep : Array Bool)
    (k : Nat) : LowerM (Array RR.Expr) := do
  let mut out := #[]
  for i in [:min k (min args.size params.size)] do
    if keep[i]?.getD true then out := out.push (← lowerArg ctx args[i]! params[i]!)
  return out

/-- Lower a constant application with Lean's arity rules, as a value of
Reussir type `rty` (the binder's: `lowerType resTy`, or `Box` for a value
that only goes into boxes, `CodeCtx.boxedOnly`). -/
def lowerConstApp (ctx : CodeCtx) (f : Name) (args : Array (Arg .pure)) (resTy : Expr) (rty : RR.Ty) :
    LowerM RR.Expr := do
  if args.size == 1 then
    if let some (prim, argTy) ← preludeReplacement? f then
      return ← coerce (.call prim #[] #[← lowerArg ctx args[0]! argTy]) (.named "LStr") rty
  match ← calleeOf f with
  | .initConst slot ty =>
    let t ← lowerType ty
    let (st, boxed) ← cellStorage t
    let v := RR.Expr.call "l2r_once_get" #[st] #[.atom (toString slot)]
    let v := if boxed then .field v 0 else v
    let (e, t) ← applyChain v t ctx args
    coerce e t rty
  | .code fn params ret keep =>
    let n := params.size
    -- Arguments Lean lends to the callee: released after the call
    -- (Lower/Borrow).
    let keeps ← borrowKeeps ctx f args n
    -- Rule 4a: the arguments of the parameters the function takes.
    if args.size == n then
      let as ← lowerTaken ctx args params keep n
      coerce (← releaseAfter (.call fn #[] as) ret keeps) ret rty
    else if args.size < n then
      let supplied ← lowerTaken ctx args params keep args.size
      let target ← boxedTarget f fn params keep ret
      let ty ← match (← read).decls.find? f with
        | some d => some <$> lowerType d.type
        | none => pure none
      partialApp { id := "d" ++ target, params, ret, call := .code target, keep, ty } args.size supplied
        rty
    else
      let as ← lowerTaken ctx args params keep n
      let (e, t) ← applyChain (← releaseAfter (.call fn #[] as) ret keeps) ret ctx args[n:].toArray
      coerce e t rty
  | .extern orig typeArgs params ret =>
    let n := params.size
    let ptys ← params.mapM lowerType
    let retTy ← lowerType ret
    if args.size == n then
      -- A refused extern of the program: no shortcut either (review REB-11).
      if (← read).externRefusals.contains orig then
        let as ← (args.zip ptys).mapM fun (a, t) => lowerArg ctx a t
        return ← coerce (refusedExternCall orig as) retTy rty
      -- `ptrAddrUnsafe x`: the address of `x` in its own representation
      -- (converted to the parameter's, it would be a temporary cell, whose
      -- address the next temporary can get: `ptrEq` would then say `true`
      -- for different values). Equal answers mean the same cell or equal
      -- values only for two values alive at the same time (plan §9).
      if (← externSymbol orig) == "lean_ptr_addr" then
        if let some (.fvar x) := args.back? then
          if let some (vn, vt) := ctx.vars[x]? then
            return ← coerce (← addrOf (.var vn) vt) (.named "u64") rty
      let as ← (args.zip ptys).mapM fun (a, t) => lowerArg ctx a t
      coerce (← lowerExternCall orig typeArgs params ret as) retTy rty
    else if args.size < n then
      -- Rule 4a for the target: the call gets placeholders for the erased
      -- parameters it does not take (`targetCall`).
      let keep := keepMask params
      let supplied ← lowerTaken ctx args ptys keep args.size
      partialApp { id := "e" ++ fnName f, params := ptys, ret := retTy, call := .extern orig typeArgs params ret,
                   keep, ty := some (← lowerType (mkFnType params ret)) }
        args.size supplied rty
    else
      let as ← (args[:n].toArray.zip ptys).mapM fun (a, t) => lowerArg ctx a t
      let call ← lowerExternCall orig typeArgs params ret as
      let (e, t) ← applyChain call retTy ctx args[n:].toArray
      coerce e t rty
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
    if args.size ≥ arity then
      let vals ← (args.zip argTys).mapM fun (a, t) => lowerArg ctx a t
      coerce (← ctorBuild c.name fullRt vals) fullRt rty
    else
      -- Rule 4a for the target: erased parameters and fields are not
      -- captured (`targetCall` gives them placeholders).
      let fty ← ctorFnType c fullTy
      let (lps, _) := splitFnType fty arity
      let keep := if lps.size == arity then keepMask lps else #[]
      let ty ← if lps.size == arity then some <$> lowerType fty else pure none
      let vals ← lowerTaken ctx args argTys keep args.size
      partialApp { id := "k" ++ fullRt.enc ++ "_" ++ fnName c.name, params := argTys, ret := fullRt,
                   call := .ctor c.name fullRt, keep, ty } args.size vals rty

/-- How a `cases` (or projection) of inductive `typeName` treats a
discriminant of Reussir type `sty`. Mono erases `unsafeCast`, so the
discriminant can be a value of another type that Lean represents alike
(translation plan §5.5): an inductive with the same constructor shapes, a
`Nat` or `UInt8` used as an enumeration. -/
inductive CastCases where
  /-- A value of `typeName` (the usual case). -/
  | same
  /-- A value of isomorphic inductive `sn` (§5.1), matched as `dn`, the
  type of `typeName`: constructors correspond by position, relevant fields
  by position (`viewLayout`), and are read at their own types. -/
  | view (sn dn : String)
  /-- Converted to `typeName`'s type `dst` first (enumerations by index;
  where no conversion exists, `coerce` warns and the cast panics). -/
  | convert (dst : RR.Ty)
  /-- `typeName` has no representation (its values carry nothing). -/
  | unit

def castCases (sty : RR.Ty) (typeName : Name) : LowerM CastCases := do
  let sameHead (h : Name) := h == typeName || h == typeName ++ `_impl || typeName == h ++ `_impl
  let tn := match sty with | .named n => n | _ => ""
  let infos ← getPart (·.typeInfos)
  let nominal := infos.contains tn
  if nominal then
    let some h ← nominalHead tn | return .same
    if sameHead h then return .same
  else if tn == "bool" && typeName == ``Bool then return .same
  -- The type of `typeName` to match against (one type per inductive).
  let uniform ← uniformType typeName
  if uniform == .unit then return .unit
  if uniform == sty || uniform == RR.Ty.box then return .same
  if nominal then
    if let .named dn := uniform then
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
  -- A fixed-width literal is its own word (`rty` is its type, or `Box` for
  -- a value that only goes into boxes).
  let litAt (e : RR.Expr) (lt : String) : LowerM RR.Expr :=
    if rty == RR.Ty.box then coerce e (.named lt) rty else pure e
  match v with
  | .lit (.nat n) => coerce (← natLiteral n) (.named "Nat") rty
  | .lit (.str s) => coerce (← strLit s) (.named "LStr") rty
  | .lit (.uint8 n) => litAt (.atom (toString n)) "u8"
  | .lit (.uint16 n) => litAt (.atom (toString n)) "u16"
  | .lit (.uint32 n) => litAt (.atom (toString n)) "u32"
  | .lit (.uint64 n) | .lit (.usize n) => litAt (.atom (toString n)) "u64"
  | .erased => zeroValue rty
  | .proj sn i x _ =>
    match ctx.vars[x]? with
    | some (n, st) =>
      -- A projection of a cast value: as a `cases` (see `castCases`).
      let (e, tn, layout?) ← match ← castCases st sn with
        | .view src dst =>
          let si ← getPart (·.typeInfos[src]?)
          let di ← getPart (·.typeInfos[dst]?)
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
          let di ← getPart (·.typeInfos[dn]?)
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
  | .const f _ args _ => lowerConstApp ctx f args ty rty
  | .fvar g args =>
    match ctx.vars[g]? with
    | some (n, t) =>
      let (e, t') ← applyChain (.var n) t ctx args
      coerce e t' rty
    | none => throwError "lean2rr: unbound function variable (internal error)"
  | _ => throwError "lean2rr: impure let value (internal error)"

end LeanToReussir
