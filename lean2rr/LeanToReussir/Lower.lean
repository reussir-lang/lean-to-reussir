import Lean
import LeanToReussir.MonoTypesKeep
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
  /-- J4: jumps re-enter the declaration's state machine at the join point's
  variant (see `StateMachine`). -/
  | enter (variant : String) (captured : Array String)

/-- A self-recursive declaration with outlined join points is lowered as one
function over a `[value]` enum of entry points (J4, translation plan §5.6):
the declaration's own entry and one variant per outlined join point. Jumps to
those join points and self tail calls become self tail calls of that
function, which LLVM turns into a loop; separate functions would make the
loop mutually recursive. -/
structure StateMachine where
  /-- The dispatching function: the declaration's parameters, then the
  entry point. -/
  fn : String
  /-- The entry-point enum: nullary `e` for the declaration itself (no
  allocation), one variant per outlined join point. -/
  mode : String
  /-- The declaration, whose tail calls re-enter at `entry`. -/
  self : Name
  arity : Nat
  /-- Names of the declaration's parameters, passed through unchanged when
  entering a join point. -/
  params : Array String
  entry : String := "e"

structure CodeCtx where
  vars : Std.HashMap FVarId (String × RR.Ty) := {}
  jumps : Std.HashMap FVarId JumpAction := {}
  /-- Types of join-point parameters, for lowering jump arguments. -/
  jpParams : Std.HashMap FVarId (Array RR.Ty) := {}
  sm : Option StateMachine := none

/-! ## Conversions -/

/-- Head constant of the Lean type a generated nominal type represents. -/
def nominalHead (n : String) : LowerM (Option Name) := do
  match (← get).typeKeys[n]? with
  | some k => return k.getAppFn.constName?
  | none => return none

/-- A placeholder of Reussir type `t`. Lean passes `box(0)` for values that
are never inspected: erased arguments (`◾`) at relevant types, and the
`unsafeCast ()` its library stores into array slots so that the element
being updated stays unshared (`Array.modifyMUnsafe`, `Array.mapMUnsafe`).
lean2rr materializes `box(0)` at the expected type as that type's zero:
`0`, `false`, the first constructor whose fields have zeros, a closure
returning a zero, an empty array (for `Nat`, `Bool` and enumerations this is
exactly what `box(0)` denotes in Lean). Only a type without a finite value
gets `l2r_unreachable`. Each placeholder is a generated function
`l2r_zero_N`. -/
partial def zeroValue (t : RR.Ty) : LowerM RR.Expr := do
  if t == .unit then return .unitVal
  if let some f := (← get).zeroFns[t]? then return .call f #[] #[]
  let f ← fresh "l2r_zero_"
  modify fun s => { s with zeroFns := s.zeroFns.insert t f, zeroBusy := s.zeroBusy.insert t }
  let lit (text : String) : RR.Block := ⟨#[("z", some t, .atom text)], .var "z"⟩
  let unreachable : RR.Block := .ofExpr (.call "l2r_unreachable" #[t] #[])
  let body : RR.Block ← match t with
    | .named n =>
      if n ∈ ["u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64"] then pure (lit "0")
      else if n ∈ ["f32", "f64"] then pure (lit "0.0")
      else if n == "bool" then pure (.ofExpr (.atom "false"))
      else if n == "Nat" then
        pure ⟨#[("z", some (.named "u64"), .atom "0")], .ctor "Nat" (some "Small") #[.var "z"]⟩
      else if n == "Int" then
        pure ⟨#[("z", some (.named "i64"), .atom "0")], .ctor "Int" (some "Small") #[.var "z"]⟩
      else if n == "LStr" then pure (.ofExpr (← strLit ""))
      else if n == "LNatArr" then pure (.ofExpr (.call "l2r_natarr_empty" #[] #[]))
      else if n == "LIntArr" then pure (.ofExpr (.call "l2r_intarr_empty" #[] #[]))
      else if n == boxName then
        pure (.ofExpr (.ctor boxName (some (← boxVariant .unit)) #[.unitVal]))
      else if let some info := (← get).typeInfos[n]? then
        -- The first constructor none of whose fields is a type whose
        -- placeholder is being built (so the value is finite).
        let busy := (← get).zeroBusy
        let ok (tys : Array RR.Ty) := tys.all fun ft => !busy.contains ft
        let fieldsOf (layout : CtorLayout) := layout.posTys
        let cands := info.ctorOrder.filterMap info.ctors.find?
        match cands.find? (fieldsOf · |>.isEmpty) <|> cands.find? (ok ∘ fieldsOf) with
        | some layout =>
          let vals ← (fieldsOf layout).mapM zeroValue
          pure <| .ofExpr <| match info.shape with
            | .struct => .ctor n none vals
            | _ => .ctor n (some layout.variant) vals
        | none => pure unreachable
      else
        -- Generated positional structs (`Tuple…`, `ElemBox…`).
        match (← get).tupleTypes.toList.find? (·.2 == n) with
        | some (k, _) =>
          let fields := if k.size == 2 && k[1]! == .named "__elem_box" then #[k[0]!] else k
          if fields.any (← get).zeroBusy.contains then pure unreachable
          else pure (.ofExpr (.ctor n none (← fields.mapM zeroValue)))
        | none => pure unreachable
    | .app "RVec" #[e] => pure (.ofExpr (.call "l2r_array_empty" #[e] #[]))
    | .fn a b =>
      -- A closure is a value whatever its result; its result is built only
      -- if it is ever applied.
      let x ← fresh "zx"
      pure (.ofExpr (.lam x a (.ofExpr (← zeroValue b))))
    | _ => pure unreachable
  modify fun s => { s with
    zeroBusy := s.zeroBusy.erase t
    fns := s.fns.push (.fn f #[] t body) }
  return .call f #[] #[]

/-- The index of a value of an enumeration type (a generated `[value]`
enum without fields), as `u8`: a generated `match`. -/
def enumIndexFn (tn : String) : LowerM String := do
  let name := s!"l2r_enum_index_{tn}"
  unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
    let some info := (← get).typeInfos[tn]? | throwError "lean2rr: no enumeration {tn}"
    let arms := info.ctorOrder.zipIdx.filterMap fun (c, i) => (info.ctors.find? c).map fun l =>
      { ty := tn, ctor := some l.variant, binders := #[], body := ⟨#[("i", some (.named "u8"), .atom (toString i))], .var "i"⟩ : RR.Arm }
    modify fun s => { s with fns := s.fns.push (.fn name #[("x", .named tn)] (.named "u8") (.ofExpr (.mtch (.var "x") arms))) }
  return name

/-- The value of enumeration type `tn` with index `i : u64` (a generated
chain of comparisons). -/
def enumOfIndexFn (tn : String) : LowerM String := do
  let name := s!"l2r_enum_of_index_{tn}"
  unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
    let some info := (← get).typeInfos[tn]? | throwError "lean2rr: no enumeration {tn}"
    let ls := info.ctorOrder.filterMap info.ctors.find?
    let some last := ls.back? | throwError "lean2rr: empty enumeration {tn}"
    let mut e : RR.Expr := .ctor tn (some last.variant) #[]
    for j in [:ls.size - 1] do
      let i := ls.size - 2 - j
      let some l := ls[i]? | continue
      e := .block ⟨#[("k", some (.named "u64"), .atom (toString i))],
        .ite (.atom "x == k") (.ofExpr (.ctor tn (some l.variant) #[])) (.ofExpr e)⟩
    modify fun s => { s with fns := s.fns.push (.fn name #[("x", .named "u64")] (.named tn) (.ofExpr e)) }
  return name

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
      -- No conversion: only reachable through an `unsafeCast` between
      -- types whose values Lean represents alike but lean2rr does not.
      -- The program is still translated; the cast panics if executed.
      IO.eprintln s!"lean2rr: warning: no representation conversion from {← keyOf src} to {← keyOf dst}; the conversion panics at run time"
      return .call "l2r_internal_panic_at" #[dst] #[.atom "0"]

  partial def tryCoerce (e : RR.Expr) (src dst : RR.Ty) : LowerM (Option RR.Expr) := do
    if src == dst then return some e
    -- Closures are boxed in canonical form `Box -> Box`, so that any
    -- consumer can apply them whatever their precise type was.
    let canon := RR.Ty.fn RR.Ty.box RR.Ty.box
    if dst == RR.Ty.box then
      match src with
      | .fn .. =>
        if src == canon then return some (.ctor boxName (some (← boxVariant canon)) #[e])
        let some c ← tryCoerce e src canon | return none
        return some (.ctor boxName (some (← boxVariant canon)) #[c])
      | _ => return some (.ctor boxName (some (← boxVariant src)) #[e])
    if src == RR.Ty.box then
      match dst with
      | .fn .. =>
        let v ← boxVariant canon
        let x ← fresh "ub"
        let unboxed := RR.Expr.mtch e #[
          { ty := boxName, ctor := some v, binders := #[some x], body := .ofExpr (.var x) },
          { ty := boxName, ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[canon] #[]) }]
        if dst == canon then return some unboxed
        return ← tryCoerce unboxed canon dst
      | .named tn =>
        if (← get).typeInfos.contains tn then
          -- Any instantiation of the same inductive may have been boxed.
          return some (.call (← unboxFn tn) #[] #[e])
        let v ← boxVariant dst
        let x ← fresh "ub"
        return some (.mtch e #[
          { ty := boxName, ctor := some v, binders := #[some x], body := .ofExpr (.var x) },
          { ty := boxName, ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[dst] #[]) }])
      | _ =>
        let v ← boxVariant dst
        let x ← fresh "ub"
        return some (.mtch e #[
          { ty := boxName, ctor := some v, binders := #[some x], body := .ofExpr (.var x) },
          { ty := boxName, ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[dst] #[]) }])
    match src, dst with
    -- A unit-like value used at another type is an `unsafeCast ()`
    -- placeholder (see `zeroValue`).
    | .named "L2RUnit", _ => return some (← zeroValue dst)
    | .fn a1 b1, .fn a2 b2 =>
      -- Wrapper `|x| conv(e(conv(x)))`; `e` is bound first unless it is a
      -- variable, because Reussir only calls variables and call results.
      let (pre, callee) ← match e with
        | .var _ => pure (#[], e)
        | _ => do
          let v ← fresh "cf"
          pure (#[(v, some src, e)], RR.Expr.var v)
      let x ← fresh "cv"
      let some arg ← tryCoerce (.var x) a2 a1 | return none
      let some res ← tryCoerce (.apply callee arg) b1 b2 | return none
      let lam := RR.Expr.lam x a2 (.ofExpr res)
      return some (if pre.isEmpty then lam else .block ⟨pre, lam⟩)
    -- `Nat` and enumerations by index (Lean represents both as scalars;
    -- only reachable through `unsafeCast`).
    | .named sn, .named dn =>
      if sn == "Nat" then
        let some di := (← get).typeInfos[dn]? | return none
        unless di.shape == .enumLike do return none
        return some (.call (← enumOfIndexFn dn) #[] #[.call "lean_usize_of_nat" #[] #[e]])
      if dn == "Nat" then
        let some si := (← get).typeInfos[sn]? | return none
        unless si.shape == .enumLike do return none
        let idx := RR.Expr.call (← enumIndexFn sn) #[] #[e]
        return some (.ctor "Nat" (some "Small") #[.atom s!"({idx.render 0} as u64)"])
      let some sh ← nominalHead sn | return none
      let some dh ← nominalHead dn | return none
      if sh != dh && !(← isomorphic sn dn) then return none
      return some (.call (← structConv sn dn) #[] #[e])
    | _, _ =>
      -- Arrays whose element types differ (an array reinterpreted by
      -- Lean's uniform-representation code, e.g. `Array α` as
      -- `Array NonScalar`): rebuilt element by element.
      let some sr ← arrayRepr? src | return none
      let some dr ← arrayRepr? dst | return none
      match ← vecConv src dst sr dr with
      | some f => return some (.call f #[] #[e])
      | none => return none

  /-- The generated function converting an array with element storage `se`
  to one with element storage `de` (cached); `none` if the elements are not
  convertible. -/
  partial def vecConv (src dst : RR.Ty) (sr dr : ArrayRepr) : LowerM (Option String) := do
    if let some f := (← get).vecConvs[(src, dst)]? then return some f
    let f ← fresh "l2r_vconv_"
    modify fun s => { s with vecConvs := s.vecConvs.insert (src, dst) f }
    let x := sr.load (sr.call "get" #[.var "src", .var "i"])
    let some y ← tryCoerce x sr.value dr.value | return none
    let go := f ++ "_go"
    let u64 := RR.Ty.named "u64"
    let loop : RR.Block := .ofExpr <| .ite (.atom "i < n")
      ⟨#[("one", some u64, .atom "1"), ("y", some dr.storage, dr.store y)],
        .call go #[] #[.var "src", .atom "i + one", .var "n", dr.call "push" #[.var "acc", .var "y"]]⟩
      (.ofExpr (.var "acc"))
    let entry : RR.Block :=
      ⟨#[("n", some u64, sr.call "size" #[.var "src"]), ("zero", some u64, .atom "0")],
        .call go #[] #[.var "src", .var "zero", .var "n", dr.call "empty" #[]]⟩
    modify fun s => { s with fns := s.fns ++ #[
      .fn go #[("src", src), ("i", u64), ("n", u64), ("acc", dst)] dst loop,
      .fn f #[("src", src)] dst entry] }
    return some f

  /-- Two generated types with the same number of constructors and, at each
  position, the same number of relevant fields. -/
  partial def isomorphic (sn dn : String) : LowerM Bool := do
    let some si := (← get).typeInfos[sn]? | return false
    let some di := (← get).typeInfos[dn]? | return false
    if si.ctorOrder.size != di.ctorOrder.size then return false
    return (si.ctorOrder.zip di.ctorOrder).all fun (a, b) =>
      match si.ctors.find? a, di.ctors.find? b with
      | some la, some lb => (la.fields.filterMap id).size == (lb.fields.filterMap id).size
      | _, _ => false

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
    -- Constructors correspond by name (instantiations of one inductive) or
    -- by position (isomorphic inductives, through `unsafeCast`).
    let sameHead := (← nominalHead sn) == (← nominalHead dn)
    for h : ci in [:si.ctorOrder.size] do
      let ctor := si.ctorOrder[ci]
      let some sl := si.ctors.find? ctor | continue
      let dctor := if sameHead then ctor else di.ctorOrder[ci]?.getD ctor
      let some dl := di.ctors.find? dctor | continue
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
      -- Fields are bound from and placed at their record positions.
      let placedVals := dl.place vals
      let body : RR.Block := if possible then
          .ofExpr (match di.shape with
            | .struct => .ctor dn none placedVals
            | _ => .ctor dn (some dl.variant) placedVals)
        else .ofExpr (.call "l2r_unreachable" #[.named dn] #[])
      match si.shape with
      | .struct =>
        structBody := some ⟨(names.zip srcFields).map (fun (n, (p, t)) => (n, some t, RR.Expr.field (.var "x") p)), body.result⟩
      | _ =>
        let mut binders : Array (Option String) := Array.replicate srcFields.size none
        for (n, (p, _)) in names.zip srcFields do binders := binders.set! p (some n)
        arms := arms.push { ty := sn, ctor := some sl.variant, binders, body }
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
  /-- A constant defined by `initialize`: read from its once-cell. -/
  | initConst (slot : Nat) (type : Expr)

def calleeOf (f : Name) : LowerM Callee := do
  if let some slot := (← get).initSlots.find? f then
    return .initConst slot (← toMonoTypeKeep (← getOtherDeclBaseType f []))
  if let some (.ctorInfo c) := (← getEnv).find? f then
    -- Constructors of builtin types implemented by the runtime
    -- (`Int.ofNat` is `lean_nat_to_int`, …) are calls, as in Lean's IR.
    unless isExtern (← getEnv) f do return .ctor c
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
  if let some (.ctorInfo c) := (← getEnv).find? f then
    let ty ← toMonoTypeKeep (← getOtherDeclBaseType f [])
    let (ps, r) := splitFnType ty (c.numParams + c.numFields)
    return .extern f #[] ps r
  throwError "lean2rr: unknown callee {f} (internal error)"

/-- Argument lowering with conversion to the expected type. -/
def lowerArg (ctx : CodeCtx) (a : Arg .pure) (expected : RR.Ty) : LowerM RR.Expr := do
  match a with
  | .fvar x =>
    match ctx.vars[x]? with
    | some (n, t) => coerce (.var n) t expected
    | none => throwError "lean2rr: unbound variable {x.name} (internal error)"
  -- `◾` (type arguments, proofs, or `box(0)` at a relevant type)
  | _ => zeroValue expected

/-- A curried chain of lambdas over `tys` whose innermost body is
`mk vars`. Used for partial applications: the body runs only when the last
argument arrives. -/
def lambdaChain (tys : Array RR.Ty) (mk : Array RR.Expr → LowerM RR.Expr) : LowerM RR.Expr := do
  let names ← tys.mapM fun _ => fresh "pa"
  let mut body ← mk (names.map .var)
  for (n, t) in (names.zip tys).reverse do
    body := .lam n t (.ofExpr body)
  return body

/-- The domains of the first `k` arrows of `t` and the rest. -/
def peelFn (t : RR.Ty) (k : Nat) : Array RR.Ty × RR.Ty := Id.run do
  let mut ds := #[]
  let mut t := t
  for _ in [:k] do
    match t with
    | .fn d c => ds := ds.push d; t := c
    | _ => break
  return (ds, t)

/-- A partial application: a curried chain of lambdas over the missing
parameters, at the types the partial application has (the let's type),
converting to and from the callee's own parameter and result types. -/
def partialApp (missing : Array RR.Ty) (ret want : RR.Ty) (mk : Array RR.Expr → RR.Expr) :
    LowerM RR.Expr := do
  let (ds, c) := peelFn want missing.size
  if ds.size != missing.size then return ← lambdaChain missing fun rest => return mk rest
  lambdaChain ds fun rest => do
    let rest' ← (rest.zip (ds.zip missing)).mapM fun (v, (d, p)) => coerce v d p
    coerce (mk rest') ret c

/-- Apply a closure to further arguments, one at a time. A function value of
statically unknown type (`Box`) is stored in canonical form `Box -> Box`
(see `tryCoerce`): it is unboxed to that, applied to a boxed argument, and
yields a `Box`. -/
def applyChain (f : RR.Expr) (fty : RR.Ty) (ctx : CodeCtx) (args : Array (Arg .pure)) :
    LowerM (RR.Expr × RR.Ty) := do
  let mut e := f
  let mut t := fty
  for a in args do
    if t == RR.Ty.box then
      let canon := RR.Ty.fn RR.Ty.box RR.Ty.box
      e := ← coerce e RR.Ty.box canon
      t := canon
    match t with
    | .fn d c =>
      let arg ← lowerArg ctx a d
      -- Reussir only calls variables and call results: bind other
      -- function expressions (e.g. a `match` producing a closure) first.
      match e with
      | .var _ | .call .. | .apply .. => e := .apply e arg
      | _ =>
        let v ← fresh "fn"
        e := .block ⟨#[(v, some t, e)], .apply (.var v) arg⟩
      t := c
    | _ => throwError "lean2rr: application of a non-function value of type {t.render}"
  return (e, t)

/-! ## Externs -/

/-- For each parameter of `c`'s declared type, the type parameter (index
among the type-former parameters) that its value has in the mono phase, if
any; and the same for the result type. A parameter declared at `α` has
type `α`, and so has one declared at a trivial structure over `α` (such as
`[Inhabited α]`, which mono represents by its `default` field). -/
def typeVarUses (c : Name) : CoreM (Array (Option Nat) × Option Nat) := do
  let some ci := (← getEnv).find? c | return (#[], none)
  let mut ty := ci.type
  let mut tyParams : Array FVarId := #[]
  let mut uses := #[]
  repeat
    match ty with
    | .forallE _ d b _ =>
      uses := uses.push (← varOf tyParams d 8)
      let x ← mkFreshFVarId
      if isTypeFormerType d then tyParams := tyParams.push x
      ty := b.instantiate1 (.fvar x)
    | _ => break
  return (uses, ← varOf tyParams ty 8)
where
  varOf (tyParams : Array FVarId) (d : Expr) (fuel : Nat) : CoreM (Option Nat) := do
    let d := d.cleanupAnnotations
    if let .fvar x := d then return tyParams.idxOf? x
    let .const s _ := d.getAppFn | return none
    let some info ← hasTrivialStructure? s | return none
    let fuel' + 1 := fuel | return none
    let some (.ctorInfo ctor) := (← getEnv).find? info.ctorName | return none
    let mut fty ← instantiateForall ctor.type d.getAppArgs[:ctor.numParams]
    for _ in [:info.fieldIdx] do
      let .forallE _ _ b _ := fty | return none
      fty := b.instantiate1 (.fvar (← mkFreshFVarId))
    let .forallE _ fd _ _ := fty | return none
    varOf tyParams fd fuel'

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

/-- Is `t` a proposition (an application of a `Prop`-valued inductive)?
Its values are proofs, which externs do not receive. -/
def isPropTy (t : Expr) : CoreM Bool := do
  let .const n _ := t.consumeMData.getAppFn | return false
  match (← getEnv).find? n with
  | some (.inductInfo iv) => return iv.type.getForallBody.isProp
  | _ => return false

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

/-- A value of generated type `ty` built with constructor `ctor` from its
relevant fields. -/
def ctorValue (ty : RR.Ty) (ctor : Name) (fields : Array RR.Expr) : LowerM RR.Expr := do
  let .named tn := ty | throwError "lean2rr: constructor {ctor} at type {ty.render}"
  if tn == "bool" then return .atom (if ctor == ``Bool.true then "true" else "false")
  let some info := (← get).typeInfos[tn]? | throwError "lean2rr: constructor {ctor} of non-nominal type {tn}"
  let some layout := info.ctors.find? ctor | throwError "lean2rr: constructor {ctor} not in type {tn}"
  let fields := layout.place fields
  return match info.shape with
    | .struct => .ctor tn none fields
    | _ => .ctor tn (some layout.variant) fields

/-- The types of the relevant fields of constructor `ctor` of generated type `ty`. -/
def ctorFieldTys (ty : RR.Ty) (ctor : Name) : LowerM (Array RR.Ty) := do
  let .named tn := ty | return #[]
  let some info := (← get).typeInfos[tn]? | return #[]
  let some layout := info.ctors.find? ctor | return #[]
  return layout.fields.filterMap (·.map (·.2))

/-- `IO.FS.Metadata` from the runtime's `[atime s, ns, mtime s, ns, size,
file type, links]`. -/
def metadataOf (mt : RR.Ty) (v : RR.Expr) : LowerM RR.Expr := do
  let fs ← ctorFieldTys mt ``IO.FS.Metadata.mk
  let some stTy := fs[0]? | throwError "lean2rr: bad IO.FS.Metadata type"
  let some (RR.Ty.named ftn) := fs[3]? | throwError "lean2rr: bad IO.FS.Metadata type"
  let get (i : Nat) : RR.Expr := .call "l2r_array_get" #[.named "u64"] #[.var "m", .atom (toString i)]
  let time (i : Nat) : LowerM RR.Expr := ctorValue stTy ``IO.FS.SystemTime.mk
    #[.call "lean_int64_to_int_sint" #[] #[get i], .atom s!"({(get (i + 1)).render 0} as u32)"]
  let md ← ctorValue mt ``IO.FS.Metadata.mk
    #[← time 0, ← time 2, get 4, .call (← enumOfIndexFn ftn) #[] #[get 5], get 6]
  return .block ⟨#[("m", some (.app "RVec" #[.named "u64"]), v)], md⟩

/-- `Array IO.FS.DirEntry` from a directory and the runtime's entry names. -/
def dirEntriesOf (arrTy : RR.Ty) (root names : RR.Expr) : LowerM RR.Expr := do
  let some repr ← arrayRepr? arrTy | throwError "lean2rr: bad directory entry array {arrTy.render}"
  let .named en := repr.value | throwError "lean2rr: bad directory entry type"
  let name := s!"l2r_dir_entries_{en}"
  unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
    let u64 := RR.Ty.named "u64"
    let entry ← ctorValue repr.value ``IO.FS.DirEntry.mk
      #[.var "root", .call "l2r_array_get" #[.named "LStr"] #[.var "names", .var "i"]]
    let body : RR.Block := .ofExpr <| .ite (.atom "i < n")
      ⟨#[("one", some u64, .atom "1"), ("e", some repr.storage, repr.store entry)],
        .call (name ++ "_go") #[] #[.var "root", .var "names", .atom "i + one", .var "n",
          repr.call "push" #[.var "acc", .var "e"]]⟩
      (.ofExpr (.var "acc"))
    let strs := RR.Ty.app "RVec" #[.named "LStr"]
    let entry' : RR.Block := ⟨#[("n", some u64, .call "l2r_array_size" #[.named "LStr"] #[.var "names"]),
        ("zero", some u64, .atom "0")],
      .call (name ++ "_go") #[] #[.var "root", .var "names", .var "zero", .var "n", repr.call "empty" #[]]⟩
    modify fun s => { s with fns := s.fns ++ #[
      .fn (name ++ "_go") #[("root", .named "LStr"), ("names", strs), ("i", u64), ("n", u64), ("acc", arrTy)] arrTy body,
      .fn name #[("root", .named "LStr"), ("names", strs)] arrTy entry'] }
  return .call name #[] #[root, names]

/-- The runtime primitive implementing fallible IO extern `sym`. -/
def fallibleIOPrim (sym : String) : String :=
  if sym == "lean_io_prim_handle_mk" then "l2r_fs_open"
  else if sym.startsWith "lean_io_prim_handle_" then "l2r_fs_" ++ (sym.drop 20).toString
  else if sym == "lean_io_realpath" then "l2r_fs_real_path"
  else if sym == "lean_io_symlink_metadata" then "l2r_fs_metadata"
  else "l2r_fs_" ++ (sym.drop 8).toString

/-- Glue for a fallible IO extern: call the runtime primitive, then
`l2r_io_finish` turns its outcome into `EST.Out.ok payload` or into
`EST.Out.error e`, where `e` is built by Lean's own `IO.Error` builder for
the error kind the runtime reports (as Lean's `decode_io_error`). -/
def fallibleIOGlue (prim : String) (primRet : RR.Ty) (argTys : Array RR.Ty) (args : Array RR.Expr)
    (ret : Expr) (follow : Bool := true) : LowerM RR.Expr := do
  let resTy ← lowerType ret
  let .named rn := resTy | throwError "lean2rr: IO result of type {resTy.render}"
  let some info := (← get).typeInfos[rn]? | throwError "lean2rr: IO result of type {rn}"
  let some errL := info.ctors.find? ``EST.Out.error | throwError "lean2rr: IO result {rn} cannot fail"
  let payload ← ioPayloadTy resTy
  -- Arguments: enumerations (`IO.FS.Mode`) are passed as their index.
  let mut lets : Array (String × Option RR.Ty × RR.Expr) := #[]
  let mut vals := #[]
  for (a, t) in args.zip argTys do
    let x ← fresh "fa"
    let e ← match t with
      | .named tn =>
        -- A handle is `lcAny` in mono code, so it arrives boxed.
        if tn == boxName then coerce a t (.named "LHandle") else
        match (← get).typeInfos[tn]? with
        | some ti => if ti.shape == .enumLike then pure (RR.Expr.call (← enumIndexFn tn) #[] #[a]) else pure a
        | none => pure a
      | _ => pure a
    lets := lets.push (x, none, e)
    vals := vals.push (RR.Expr.var x)
  let v ← fresh "fv"
  -- `metadata` and `symlinkMetadata` differ in following symbolic links.
  if prim == "l2r_fs_metadata" then vals := vals.push (.atom (toString follow))
  lets := lets.push (v, some primRet, .call prim #[] vals)
  -- Success: the payload.
  let x ← fresh "fx"
  let okVal ← if payload == RR.Ty.unit then pure RR.Expr.unitVal
    else if prim == "l2r_fs_metadata" then metadataOf payload (.var x)
    else if prim == "l2r_fs_read_dir" then dirEntriesOf payload vals[0]! (.var x)
    else coerce (.var x) primRet payload
  let okFn := RR.Expr.lam x primRet (.ofExpr (← wrapIOResult resTy okVal))
  -- Failure: the builder of the reported kind.
  let (k, errno, fname, details) := ("ek", "ee", "ef", "ed")
  let errTy ← match errL.fields[0]? with
    | some (some (_, t)) => pure t
    | _ => throwError "lean2rr: IO result {rn} has no error field"
  let mut mk : RR.Expr := .call "l2r_unreachable" #[errTy] #[]
  for i in [:(← read).ioErrorBuilders.size] do
    let j := (← read).ioErrorBuilders.size - 1 - i
    let some inst := (← read).ioErrorBuilders[j]! | continue
    let callee ← calleeOf inst
    let .code fn ps _ := callee | continue
    let call := if ps.size == 3 then RR.Expr.call fn #[] #[.var fname, .var errno, .var details]
      else RR.Expr.call fn #[] #[.var errno, .var details]
    let kj ← fresh "kj"
    mk := .block ⟨#[(kj, some (.named "u32"), .atom (toString j))],
      .ite (.atom s!"{k} == {kj}") (.ofExpr call) (.ofExpr mk)⟩
  let errVal := RR.Expr.ctor rn (some errL.variant) #[mk]
  let errFn := RR.Expr.lam k (.named "u32") <| .ofExpr <| .lam errno (.named "u32") <| .ofExpr <|
    .lam fname (.named "LStr") <| .ofExpr <| .lam details (.named "LStr") (.ofExpr errVal)
  return .block ⟨lets, .call "l2r_io_finish" #[primRet, resTy] #[.var v, okFn, errFn]⟩

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
    { ty := lt, ctor := some cons.variant,
      binders := (cons.place #[.var "x", .var "t"]).map fun | .var v => some v | _ => none,
      body := .ofExpr (.call name #[] #[.var "t", step (.var "acc") (.var "x")]) }])
  let _ := elemTy
  modify fun s => { s with fns := s.fns.push (.fn name #[("l", listTy), ("acc", accTy)] accTy body) }
  return name

/-- Glue for `ST.Ref` operations on the runtime cell `LRef<S>` (S is the
storage type of the element type `α`, taken from the extern instance key).
A reference itself has mono type `lcAny` (Lean unwraps `ST.Ref` to an opaque
pointer), so it is passed around boxed. -/
def refGlue (orig : Name) (typeArgs : Array Expr) (params : Array Expr) (ret : Expr)
    (args : Array RR.Expr) : LowerM (Option RR.Expr) := do
  let some α := typeArgs[1]? | return none
  let α ← toMonoTypeKeep α
  let (st, boxed) ← arrayElemTy (← lowerType α)
  let refTy := RR.Ty.app "LRef" #[st]
  let wrap (e : RR.Expr) : RR.Expr := match st with
    | .named bn => if boxed then .ctor bn none #[e] else e
    | _ => e
  let unwrap (e : RR.Expr) : RR.Expr := if boxed then .field e 0 else e
  let resTy ← lowerType ret
  let payload ← ioPayloadTy resTy
  let asRef (i : Nat) : LowerM RR.Expr := do
    coerce args[i]! (← lowerType params[i]!) refTy
  match orig with
  | ``ST.Prim.mkRef =>
    let r ← coerce (.call "l2r_ref_new" #[st] #[wrap args[0]!]) refTy payload
    return some (← wrapIOResult resTy r)
  | ``ST.Prim.Ref.get =>
    let v ← coerce (unwrap (.call "l2r_ref_get" #[st] #[← asRef 0])) (← lowerType α) payload
    return some (← wrapIOResult resTy v)
  -- `take` moves the value out (Lean's `modify` is take-then-set, so the
  -- value stays unshared and is updated in place).
  | ``ST.Prim.Ref.take =>
    let v ← coerce (unwrap (.call "l2r_ref_take" #[st] #[← asRef 0])) (← lowerType α) payload
    return some (← wrapIOResult resTy v)
  | ``ST.Prim.Ref.set =>
    let r ← fresh "rs"
    return some (.block ⟨#[(r, some (.named "u64"), .call "l2r_ref_set" #[st] #[← asRef 0, wrap args[1]!])],
      ← wrapIOResult resTy .unitVal⟩)
  | ``ST.Prim.Ref.swap =>
    let v ← coerce (unwrap (.call "l2r_ref_swap" #[st] #[← asRef 0, wrap args[1]!])) (← lowerType α) payload
    return some (← wrapIOResult resTy v)
  | ``ST.Prim.Ref.ptrEq =>
    return some (← wrapIOResult resTy (.call "l2r_ref_ptr_eq" #[st] #[← asRef 0, ← asRef 1]))
  | _ => return none

/-- Externs over Lean-defined types: the runtime's generic helpers receive
the generated constructors as arguments. -/
def ctorCallbackExtern (sym : String) (ret : Expr) (args : Array RR.Expr) : LowerM (Option RR.Expr) := do
  let rt ← lowerType ret
  let lam (x : String) (t : RR.Ty) (body : RR.Expr) : RR.Expr := .lam x t (.ofExpr body)
  match sym with
  | "lean_string_compare" =>
    let v (c : Name) := ctorValue rt c #[]
    return some (.call "l2r_string_compare_with" #[rt] (args ++ #[← v ``Ordering.lt, ← v ``Ordering.eq, ← v ``Ordering.gt]))
  | "lean_string_data" =>
    let some hd := (← ctorFieldTys rt ``List.cons)[0]? | return none
    let cons ← ctorValue rt ``List.cons #[← coerce (.var "c") (.named "u32") hd, .var "t"]
    return some (.call "l2r_string_to_list" #[rt]
      (args ++ #[← ctorValue rt ``List.nil #[], lam "c" (.named "u32") (lam "t" rt cons)]))
  | "lean_string_utf8_get_opt" =>
    let some v := (← ctorFieldTys rt ``Option.some)[0]? | return none
    let some' ← ctorValue rt ``Option.some #[← coerce (.var "c") (.named "u32") v]
    return some (.call "l2r_string_utf8_get_opt_with" #[rt]
      (args ++ #[← ctorValue rt ``Option.none #[], lam "c" (.named "u32") some']))
  | "lean_float_frexp" | "lean_float32_frexp" =>
    let fty := RR.Ty.named (if sym == "lean_float_frexp" then "f64" else "f32")
    let tys ← ctorFieldTys rt ``Prod.mk
    let some mt := tys[0]? | return none
    let some et := tys[1]? | return none
    let pair ← ctorValue rt ``Prod.mk #[← coerce (.var "m") fty mt, ← coerce (.var "e") (.named "Int") et]
    let helper := if sym == "lean_float_frexp" then "l2r_float_frexp_with" else "l2r_float32_frexp_with"
    return some (.call helper #[rt] (args ++ #[lam "m" fty (lam "e" (.named "Int") pair)]))
  | _ => return none

/-- Externs whose results mention Lean-defined types get generated glue
(translation plan §5.8); returns `none` for ordinary externs. -/
def customExtern (orig : Name) (params : Array Expr) (ret : Expr) (args : Array RR.Expr) :
    LowerM (Option RR.Expr) := do
  if let some e ← ctorCallbackExtern (← externSymbol orig) ret args then return some e
  -- Tasks run eagerly and thunks are called on demand: the glue follows the
  -- reference bodies of these externs in Lean's source (translation plan §6).
  -- `Task α` and `Thunk α` are Lean's one-field structures.
  let structOf (t : Expr) : LowerM String := do
    match ← lowerType t with
    | .named n => return n
    | rt => throwError "lean2rr: expected a structure type, got {rt.render}"
  match orig with
  -- Generic Reussir functions in the prelude (not FFI): instantiated at
  -- the value type itself, not at its array storage type.
  | ``dbgTrace => return some (.call "lean_dbg_trace" #[← lowerType ret] args)
  | ``dbgTraceIfShared => return some (.call "lean_dbg_trace_if_shared" #[← lowerType ret] args)
  | ``Task.get => return some (.field args[0]! 0)
  | ``Task.spawn => return some (.ctor (← structOf ret) none #[.apply args[0]! .unitVal])
  | ``Task.map => return some (.ctor (← structOf ret) none #[.apply args[0]! (.field args[1]! 0)])
  | ``Task.bind => return some (.apply args[1]! (.field args[0]! 0))
  | ``Thunk.pure =>
    let x ← fresh "tu"
    return some (.ctor (← structOf ret) none #[.lam x RR.Ty.unit (.ofExpr args[0]!)])
  | ``Thunk.get => return some (.apply (.field args[0]! 0) .unitVal)
  -- Constructors that carry an extern attribute.
  | ``Thunk.mk | ``Task.pure => return some (.ctor (← structOf ret) none #[args[0]!])
  -- BaseIO task combinators, run eagerly: `asTask act := Task.pure <$> act`,
  -- `mapTask f t := Task.pure <$> f t.get`, `bindTask t f := f t.get`,
  -- `wait t := pure t.get`. Results are `ST.Out` structs.
  | ``BaseIO.asTask =>
    let resTy ← lowerType ret
    let taskTy ← ioPayloadTy resTy
    let .named taskN := taskTy | return none
    let r ← fresh "at"
    let rTy ← match ← lowerType params[0]! with | .fn _ c => pure c | t => pure t
    return some (.block ⟨#[(r, some rTy, .apply args[0]! args[2]!)],
      ← wrapIOResult resTy (.ctor taskN none #[.field (.var r) 0])⟩)
  | ``BaseIO.mapTask =>
    let resTy ← lowerType ret
    let taskTy ← ioPayloadTy resTy
    let .named taskN := taskTy | return none
    let r ← fresh "mt"
    let fTy ← lowerType params[0]!
    let rTy := match fTy with | .fn _ (.fn _ c) => c | t => t
    return some (.block ⟨#[(r, some rTy, .apply (.apply args[0]! (.field args[1]! 0)) args[4]!)],
      ← wrapIOResult resTy (.ctor taskN none #[.field (.var r) 0])⟩)
  | ``BaseIO.bindTask => return some (.apply (.apply args[1]! (.field args[0]! 0)) args[4]!)
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
    return some (.call fn #[] #[args[0]!, ← strLit ""])
  -- `Array.mk : List α → Array α`
  if orig == ``Array.mk then
    let lt ← lowerType params[0]!
    let arrTy ← lowerType ret
    let some repr ← arrayRepr? arrTy | throwError "lean2rr: bad array type {arrTy.render}"
    let fn ← listFold s!"l2r_list_to_array_{lt.render.map fun c => if c.isAlphanum then c else '_'}" lt arrTy
      repr.storage fun acc x => repr.call "push" #[acc, repr.store x]
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
    let some (some (_, valTy)) := cons.fields[0]? | throwError "lean2rr: bad list type"
    let name := s!"l2r_array_to_list_{ltn}_{repr.family}"
    unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
      let x := repr.load (repr.call "get" #[.var "v", .var "j"])
      let x ← coerce x repr.value valTy
      let u64 := RR.Ty.named "u64"
      let body : RR.Block := ⟨#[("zero", some u64, .atom "0")], .ite (.atom "zero < i")
        ⟨#[("one", some u64, .atom "1"), ("j", some u64, .atom "i - one"), ("x", some valTy, x),
           ("c", some lt, .ctor ltn (some cons.variant) (cons.place #[.var "x", .var "acc"]))],
          .call (name ++ "_go") #[] #[.var "v", .var "j", .var "c"]⟩
        (.ofExpr (.var "acc"))⟩
      let entry : RR.Block :=
        .ofExpr (.call (name ++ "_go") #[] #[.var "v", repr.call "size" #[.var "v"],
          .ctor ltn (some nil.variant) #[]])
      modify fun s => { s with fns := s.fns ++ #[
        .fn (name ++ "_go") #[("v", arrTy), ("i", u64), ("acc", lt)] lt body,
        .fn name #[("v", arrTy)] lt entry] }
    return some (.call name #[] #[args[0]!])
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
  -- Glue sees only relevant parameters: erased ones (type arguments,
  -- proofs) are dropped; the world is kept (IO glue applies actions to it).
  let relevant := (params.zip args).filter fun (p, _) =>
    let p := p.consumeMData
    !(p.isErased || p.isSort)
  if let some e ← customExtern orig (relevant.map (·.1)) ret (relevant.map (·.2)) then return e
  if orig.getPrefix == `ST.Prim || orig.getPrefix == `ST.Prim.Ref then
    if let some e ← refGlue orig typeArgs (relevant.map (·.1)) ret (relevant.map (·.2)) then return e
  let sym ← externSymbol orig
  -- Which parameters the runtime receives: not erased ones, not the world,
  -- not proofs.
  let mask ← params.mapM fun p => return externParamPassed p && !(← isPropTy p)
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
            return ← wrapIOResult resTy (.call prim #[] passedArgs)
  -- Array externs at `Array Nat`/`Array Int` use the one-word arrays.
  if let some α := typeArgs[0]? then
    let fam? := match ← lowerType (← toMonoTypeKeep α) with
      | .named "Nat" => some "natarr"
      | .named "Int" => some "intarr"
      | _ => none
    if let some fam := fam? then
      if let some sym' := natArrSym? sym fam then
        return .call sym' #[] passedArgs
  -- Storage for each type argument: (storage type, boxed?).
  let mut storage := #[]
  for t in typeArgs do
    -- Instance keys hold base-phase types.
    let rt ← lowerType (← toMonoTypeKeep t)
    storage := storage.push (← arrayElemTy rt)
  -- Values whose declared type is a type parameter `α` are passed and
  -- returned in `α`'s storage (e.g. `Array.push`'s element): wrapped if the
  -- storage is a wrapper.
  let (uses, retUse) ← typeVarUses orig
  let boxOf (use : Option Nat) : Option String := do
    let (st, boxed) ← storage[← use]?
    if boxed then if let .named bn := st then return bn
    none
  let mut passed := #[]
  for i in [:params.size] do
    if mask[i]! then
      let a := args[i]!
      match boxOf (uses[i]?.join) with
      | some bn => passed := passed.push (.ctor bn none #[a])
      | none => passed := passed.push a
  let call := RR.Expr.call sym (storage.map (·.1)) passed
  match boxOf retUse with
  | some _ => return .field call 0
  | none => return call

/-! ## Values -/

/-- A `Nat` literal: `Small` below 2^64, otherwise built from base-2^32
digits with runtime arithmetic (no string argument, see `strLit`). -/
def natLiteral (n : Nat) : RR.Expr :=
  if n < 2 ^ 64 then small n
  else
    let rec limbs (n : Nat) (acc : List Nat) (fuel : Nat) : List Nat :=
      match fuel with
      | 0 => acc
      | fuel + 1 => if n == 0 then acc else limbs (n / 2 ^ 32) ((n % 2 ^ 32) :: acc) fuel
    match limbs n [] (n.log2 / 32 + 2) with
    | [] => small 0
    | l :: ls => ls.foldl (init := small l) fun acc d =>
        .call "lean_nat_add" #[] #[.call "lean_nat_mul" #[] #[acc, small (2 ^ 32)], small d]
where
  small (k : Nat) : RR.Expr := .ctor "Nat" (some "Small") #[.atom (toString k)]

/-- Lower a constant application with Lean's arity rules. -/
def lowerConstApp (ctx : CodeCtx) (f : Name) (args : Array (Arg .pure)) (resTy : Expr) :
    LowerM RR.Expr := do
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
      partialApp params[args.size:].toArray ret (← lowerType resTy) fun rest => .call fn #[] (supplied ++ rest)
    else
      let as ← (args[:n].toArray.zip params).mapM fun (a, t) => lowerArg ctx a t
      let (e, t) ← applyChain (.call fn #[] as) ret ctx args[n:].toArray
      coerce e t (← lowerType resTy)
  | .extern orig typeArgs params ret =>
    let n := params.size
    let ptys ← params.mapM lowerType
    let retTy ← lowerType ret
    if args.size == n then
      let as ← (args.zip ptys).mapM fun (a, t) => lowerArg ctx a t
      lowerExternCall orig typeArgs params ret as
    else if args.size < n then
      let supplied ← (args.zip ptys).mapM fun (a, t) => lowerArg ctx a t
      let k := n - args.size
      let want ← lowerType resTy
      let (ds, c) := peelFn want k
      if ds.size == k then
        lambdaChain ds fun rest => do
          let rest' ← (rest.zip (ds.zip ptys[args.size:].toArray)).mapM fun (v, (d, p)) => coerce v d p
          coerce (← lowerExternCall orig typeArgs params ret (supplied ++ rest')) retTy c
      else
        lambdaChain ptys[args.size:].toArray fun rest => lowerExternCall orig typeArgs params ret (supplied ++ rest)
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
          let placedVals := layout.place fieldVals
          match info.shape with
          | .struct => return .ctor tn none placedVals
          | _ => return .ctor tn (some layout.variant) placedVals
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
  | .lit (.str s) => coerce (← strLit s) (.named "LStr") rty
  | .lit (.uint8 n) | .lit (.uint16 n) => return .atom (toString n)
  | .lit (.uint32 n) => return .atom (toString n)
  | .lit (.uint64 n) | .lit (.usize n) => return .atom (toString n)
  | .erased => zeroValue rty
  | .proj _ i x _ =>
    match ctx.vars[x]? with
    | some (n, .named tn) =>
      match (← get).typeInfos[tn]? with
      | some info =>
        let some layout := info.ctors.find? info.ctorOrder[0]! | throwError "lean2rr: bad projection"
        match layout.fields[i]? with
        | some (some (j, ft)) => coerce (.field (.var n) j) ft rty
        | _ => zeroValue rty
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

/-- Does `c` jump to `j`? -/
partial def hasJumpTo (j : FVarId) : Code .pure → Bool
  | .jmp j' _ => j == j'
  | .let _ k => hasJumpTo j k
  | .fun d k _ | .jp d k => hasJumpTo j d.value || hasJumpTo j k
  | .cases c => c.alts.any (hasJumpTo j ·.getCode)
  | _ => false

/-- Place join point `d` (whose scope is `k`) as deep as possible: into the
single branch, join-point body or continuation containing all its jumps.
Free variables of `d` stay in scope (binders are unique), and code does not
grow. Sunk into the subtree its jumps come from, a join point is more often
structured (J2) instead of outlined: an outlined join point that calls the
enclosing function back makes a loop mutually recursive, which LLVM does not
turn into a loop. -/
partial def sinkInto (d : FunDecl .pure) (k : Code .pure) : Code .pure :=
  let j := d.fvarId
  match k with
  | .let x k' => .let x (sinkInto d k')
  | .fun f k' _ => if hasJumpTo j f.value then .jp d k else .fun f (sinkInto d k')
  | .jp d2 k2 =>
    match hasJumpTo j d2.value, hasJumpTo j k2 with
    | true, true => .jp d k
    | true, false => .jp (FunDecl.mk d2.fvarId d2.binderName d2.params d2.type (sinkInto d d2.value)) k2
    | false, true => .jp d2 (sinkInto d k2)
    | false, false => k
  | .cases c =>
    if (c.alts.filter (hasJumpTo j ·.getCode)).size == 1 then
      .cases ⟨c.typeName, c.resultType, c.discr, c.alts.map fun alt =>
        if hasJumpTo j alt.getCode then
          match alt with
          | .alt ctor ps code _ => .alt ctor ps (sinkInto d code)
          | .default code => .default (sinkInto d code)
          | other => other
        else alt⟩
    else .jp d k
  | _ => .jp d k

/-- Sink every join point of `c` (innermost first). -/
partial def sinkJoinPoints : Code .pure → Code .pure
  | .let x k => .let x (sinkJoinPoints k)
  | .fun d k _ =>
    .fun (FunDecl.mk d.fvarId d.binderName d.params d.type (sinkJoinPoints d.value)) (sinkJoinPoints k)
  | .jp d k =>
    sinkInto (FunDecl.mk d.fvarId d.binderName d.params d.type (sinkJoinPoints d.value)) (sinkJoinPoints k)
  | .cases c =>
    .cases ⟨c.typeName, c.resultType, c.discr, c.alts.map fun
      | .alt ctor ps code _ => .alt ctor ps (sinkJoinPoints code)
      | .default code => .default (sinkJoinPoints code)
      | other => other⟩
  | c => c

/-- Does `c` contain a tail call `let x := f args; return x` of `f` with
`arity` arguments (outside nested join-point bodies, which are checked on
their own when outlined)? -/
partial def hasSelfTailCall (f : Name) (arity : Nat) : Code .pure → Bool
  | .let d k =>
    match d.value, k with
    | .const g _ args _, .return x => (g == f && args.size == arity && x == d.fvarId) || hasSelfTailCall f arity k
    | _, _ => hasSelfTailCall f arity k
  | .fun _ k _ => hasSelfTailCall f arity k
  | .jp d k => hasSelfTailCall f arity d.value || hasSelfTailCall f arity k
  | .cases c => c.alts.any (hasSelfTailCall f arity ·.getCode)
  | _ => false

/-- The bodies of the outlined join points of `c`. -/
partial def outlinedBodies (c : Code .pure) (outlined : FVarIdSet) : Array (Code .pure) :=
  go c #[]
where
  go (c : Code .pure) (acc : Array (Code .pure)) : Array (Code .pure) :=
    match c with
    | .let _ k => go k acc
    | .fun d k _ => go k (go d.value acc)
    | .jp d k => go k (go d.value (if outlined.contains d.fvarId then acc.push d.value else acc))
    | .cases cs => cs.alts.foldl (fun acc alt => go alt.getCode acc) acc
    | _ => acc

/-- Size of a code block (bindings, alternatives and exits), counted up to
`cap`. -/
partial def codeSize (c : Code .pure) (cap : Nat) : Nat :=
  go c 0
where
  go (c : Code .pure) (acc : Nat) : Nat :=
    if acc ≥ cap then acc else
    match c with
    | .let _ k => go k (acc + 1)
    | .fun d k _ | .jp d k => go k (go d.value (acc + 1))
    | .cases cs => cs.alts.foldl (fun acc alt => go alt.getCode (acc + 1)) (acc + 1)
    | _ => acc + 1

/-- Small join points (nested join points included, since sinking nests
them) are duplicated at their jumps (like J1) rather than
outlined: outlining one on a loop's path makes the loop a state machine
(J4) or mutually recursive (J3), and keeps the reuse of cells matched
before the jump from reaching constructions after it. -/
def isSmallJp (d : FunDecl .pure) : Bool := codeSize d.value 41 ≤ 40

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
      let ok := single || isSmallJp d ||
        (endsInJumps k (({} : FVarIdSet).insert d.fvarId) outlined && !jumpedFromOutlined)
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
      -- J4: a self tail call re-enters the state machine.
      if let some sm := ctx.sm then
        if let .const f _ args _ := d.value then
          if f == sm.self && args.size == sm.arity && t == retTy then
            if let .return x := k then
              if x == d.fvarId then
                let some selfDecl := (← read).decls.find? f | throwError "lean2rr: no declaration {f}"
                let (ps, _) := splitFnType selfDecl.type sm.arity
                let vals ← (args.zip ps).mapM fun (a, p) => do lowerArg ctx a (← lowerType p)
                return .ofExpr (.call sm.fn #[] (vals.push (.ctor sm.mode (some sm.entry) #[])))
      let e ← try lowerLetValue ctx d.value d.type t
        catch ex => throwError "{ex.toMessageData}\n  in let {d.binderName} : {d.type}"
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
      | some (.enter variant captured) =>
        let some sm := ctx.sm | throwError "lean2rr: state-machine jump outside a state machine"
        let tys := ctx.jpParams.getD j #[]
        let vals ← (args.zip tys).mapM fun (a, t) => lowerArg ctx a t
        return .ofExpr (.call sm.fn #[] (sm.params.map .var |>.push (.ctor sm.mode (some variant) (captured.map .var ++ vals))))
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
        let fparams := captured.map (fun n => (n, varTys.getD n .unit)) ++ pnames.zip ptys
        if let some sm := ctx.sm then
          -- J4: a variant of the state machine.
          let variant ← fresh "j"
          modify fun s => { s with smArms := s.smArms.push (variant, fparams, body) }
          return ← lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.enter variant captured) } outlined retTy k
        let fn ← fresh "jp_"
        modify fun s => { s with fns := s.fns.push (.fn fn fparams retTy body) }
        lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.call fn captured) } outlined retTy k
      else if (countJumps k {}).getD d.fvarId 0 ≤ 1 ||
          (isSmallJp d && !endsInJumps k (({} : FVarIdSet).insert d.fvarId) outlined) then
        -- J1, or a small join point that is not J2: its body at each jump.
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
    let some (scrut0, sty0) := ctx.vars[cs.discr]? | throwError "lean2rr: cases on unbound variable"
    -- A `cases` on a value of statically unknown type: convert it to the
    -- inductive's uniform instance first.
    if sty0 == RR.Ty.box then
      let uty ← uniformType cs.typeName
      let u ← fresh "uv"
      let conv ← coerce (.var scrut0) RR.Ty.box uty
      let ctx' := { ctx with vars := ctx.vars.insert cs.discr (u, uty) }
      return .block ⟨#[(u, some uty, conv)], ← lowerCases ctx' outlined retTy cs⟩
    let (scrut, sty) := (scrut0, sty0)
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

/-- The accessor of a constant (a declaration without parameters): its value
is computed once, by `<name>_init`, and kept in a runtime once-cell for the
rest of the run, like native Lean's CAFs and closed terms (translation plan
§5.12). The cell stores a boundary type; other values are boxed. -/
def cafAccessor (name : String) (ret : RR.Ty) : LowerM RR.Item := do
  let slot := (← get).cafSlots
  modify fun s => { s with cafSlots := slot + 1 }
  let (st, boxed) ← arrayElemTy ret
  let wrap (e : RR.Expr) : RR.Expr := match st with
    | .named bn => if boxed then .ctor bn none #[e] else e
    | _ => e
  let unwrap (e : RR.Expr) : RR.Expr := if boxed then .field e 0 else e
  let k := RR.Expr.atom (toString slot)
  let body : RR.Block := .ofExpr (.ite (.call "l2r_once_has" #[] #[k])
    (.ofExpr (unwrap (.call "l2r_once_get" #[st] #[k])))
    (.ofExpr (unwrap (.call "l2r_once_set" #[st] #[k, wrap (.call (name ++ "_init") #[] #[])]))))
  return .fn name #[] ret body

/-- Generate the bodies of all `Box → nominal` converters: each matches every
`Box` variant holding an instantiation of the target's inductive and
converts it structurally. Generating a conversion may add `Box` variants
(for fields), so this iterates until the variant set is stable. -/
partial def finishUnboxFns : LowerM Unit := do
  let mut done : Std.HashMap String Nat := {}
  repeat
    let targets := (← get).unboxTargets
    let nvars := (← get).boxVariants.size
    let pending := targets.filter fun t => done.getD t 0 != nvars + 1
    if pending.isEmpty then break
    for t in pending do
      let some th ← nominalHead t | continue
      let mut arms := #[]
      for (vt, vname) in (← get).boxVariants do
        let .named vn := vt | continue
        let some vh ← nominalHead vn | continue
        if vh != th then continue
        let x ← fresh "bx"
        let body ← if vn == t then pure (RR.Expr.var x) else coerce (.var x) vt (.named t)
        arms := arms.push { ty := boxName, ctor := some vname, binders := #[some x], body := .ofExpr body : RR.Arm }
      arms := arms.push { ty := boxName, ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[.named t] #[]) }
      let fname := s!"l2r_unbox_{t}"
      let item := RR.Item.fn fname #[("b", RR.Ty.box)] (.named t) (.ofExpr (.mtch (.var "b") arms))
      modify fun s => { s with fns := (s.fns.filter fun | .fn n .. => n != fname | _ => true).push item }
      -- Record the variant count this body was generated against; a later
      -- growth of the variant set makes it pending again.
      done := done.insert t (nvars + 1)

/-- Lower a declaration with code to a Reussir function. -/
def lowerDecl (d : Decl .pure) : LowerM Unit := do
  let .code body := d.value | return
  let body := sinkJoinPoints body
  let (ps, r) := splitFnType d.type d.params.size
  let _ := ps
  let ptys ← d.params.mapM (lowerType ·.type)
  let ret ← lowerType r
  let pnames ← d.params.mapM fun _ => fresh "a"
  let outlined := chooseOutlined body
  -- J4 when an outlined join point tail-calls the declaration: a loop
  -- passes through it. (Other calls need no state machine; going through
  -- its entry wrapper would only cost an allocation per call.)
  let callsBack := outlinedBodies body outlined |>.any (hasSelfTailCall d.name d.params.size)
  let sm? : Option StateMachine ← do
    if !callsBack || d.params.isEmpty || (← IO.getEnv "L2R_NO_J4").isSome then pure none
    else
      let base := fnName d.name
      pure (some { fn := base ++ "_sm", mode := base ++ "_mode", self := d.name, arity := d.params.size, params := pnames })
  modify fun s => { s with smArms := #[] }
  let ctx : CodeCtx := { vars := (d.params.zip (pnames.zip ptys)).foldl (fun m (p, nt) => m.insert p.fvarId nt) {}, sm := sm? }
  let block ← try lowerCode ctx outlined ret body
    catch e => throwError "{e.toMessageData}\n  while lowering {d.name}"
  if let some sm := sm? then
    let arms := (← get).smArms
    -- A shared enum: Reussir miscompiles `[value]` enums whose arms have
    -- different layouts (translation plan §9); Reussir reuses the cell of
    -- the matched value.
    let mode := RR.Item.enum sm.mode false
      (#[(sm.entry, #[])] ++ arms.map fun (v, fps, _) => (v, fps.map (·.2)))
    let mkArm (v : String) (names : Array String) (b : RR.Block) : RR.Arm :=
      { ty := sm.mode, ctor := some v, binders := names.map some, body := b }
    let matchArms := #[mkArm sm.entry #[] block] ++ arms.map fun (v, fps, b) => mkArm v (fps.map (·.1)) b
    let m ← fresh "m"
    modify fun s => { s with
      typeItems := s.typeItems.push mode
      fns := s.fns
        |>.push (.fn sm.fn ((pnames.zip ptys).push (m, .named sm.mode)) ret (.ofExpr (.mtch (.var m) matchArms)))
        |>.push (.fn (fnName d.name) (pnames.zip ptys) ret
            (.ofExpr (.call sm.fn #[] ((pnames.map .var).push (.ctor sm.mode (some sm.entry) #[])))))
      smArms := #[] }
    return
  if d.params.isEmpty then
    let acc ← cafAccessor (fnName d.name) ret
    modify fun s => { s with fns := s.fns.push (.fn (fnName d.name ++ "_init") #[] ret block) |>.push acc }
  else
    modify fun s => { s with fns := s.fns.push (.fn (fnName d.name) (pnames.zip ptys) ret block) }

end LeanToReussir
