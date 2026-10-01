import LeanToReussir.Lower.Code

/-!
# Generated at the end

Functions whose bodies depend on everything the program lowered: the
`Box` → nominal/array/function converters (`finishUnboxFns`), the
application and conversion functions of function values
(`finishFnValues`), and the enums of function types (`fnTypeItems`).
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Release `Box` value `b` out of line (`l2r_ptr_addr_rec` releases the
reference it receives), as a `let` binding (of a fixed name: the only
binding of the `unreachable` arm it is used in). rrc expands every release of an
enum in line into a match over its variants, one release per variant, and
`Box` has a variant per boxed type: an unboxing function, inlined wherever
it is called, would otherwise hold one such expansion in its `unreachable`
arm. -/
def boxSink (b : RR.Expr) : String × Option RR.Ty × RR.Expr :=
  ("l2rbs", some (.named "u64"), .call "l2r_ptr_addr_rec" #[RR.Ty.box] #[b])

/-- Can Reussir types `a` and `b` represent the same Lean type? `Box` stands
for any type; arrays compare their elements, instantiations of an inductive
their head. -/
partial def reprCompatible (a b : RR.Ty) : LowerM Bool := do
  if a == b || a == RR.Ty.box || b == RR.Ty.box then return true
  match a, b with
  | .fn a1 b1, .fn a2 b2 => return (← reprCompatible a1 a2) && (← reprCompatible b1 b2)
  | .app "LCell" _, .app "LCell" _ =>
    -- Thunks (or tasks) with compatible values.
    match ← lazyOf? a, ← lazyOf? b with
    | some (_, k1, va), some (_, k2, vb) => return k1 == k2 && (← reprCompatible va vb)
    | _, _ => return false
  | _, _ =>
    if let (some ra, some rb) := (← arrayRepr? a, ← arrayRepr? b) then
      return ← reprCompatible ra.value rb.value
    match a, b with
    | .named an, .named bn =>
      match ← nominalHead an, ← nominalHead bn with
      | some ha, some hb => return ha == hb
      | _, _ => return false
    | _, _ => return false

/-- Whether a `Box` holding a value of type `vt` may be read at type `t`
through `unsafeCast` (`boxCastable`, Lower/Conv). -/
def boxCastCompatible (vt t : RR.Ty) : LowerM Bool := boxCastable vt t

/-- Generate the bodies of all `Box → nominal` and `Box → array` converters.
A converter matches every `Box` variant that can hold a value of the
target's Lean type and converts it: for a nominal type, any instantiation of
its inductive (structurally); for an array type, any array representation
with compatible elements (element by element; e.g. an `Array Nat` built by
uniform-representation code is boxed as `RVec<Box>`, but its consumer wants
`LNatArr`). Other variants are unreachable. A boxed unit
is Lean's `box(0)` placeholder and becomes the target's zero. Generating a
conversion may add `Box` variants (for fields), so this iterates until the
variant set is stable. -/
partial def finishUnboxFns : LowerM Unit := do
  let mut done : Std.HashMap String Nat := {}
  repeat
    -- Reference dispatch over the boxed reference types (it can box more).
    finishRefFns
    let nvars := (← get).boxVariants.size
    let nominal := (← get).unboxTargets.map fun t => (s!"l2r_unbox_{t}", RR.Ty.named t)
    let arrays := (← get).unboxArrTargets.map fun (t, f) => (f, t)
    let fns := (← get).fnUnboxTargets.map fun t => (s!"l2r_unbox_fn_{t.enc}", t)
    let pending := (nominal ++ arrays ++ fns).filter fun (f, _) => done.getD f 0 != nvars + 1
    -- The identity of a `Box` (`genBoxAddr`) matches every variant too.
    let boxAddrPending := (← get).boxAddrWanted && (← get).boxAddrDone != nvars
    if pending.isEmpty && !boxAddrPending then break
    if boxAddrPending then genBoxAddr
    for (fname, t) in pending do
      let th? ← match t with
        | .named tn => nominalHead tn
        | _ => pure none
      let tArr := (← arrayRepr? t).isSome
      let mut arms : Array RR.Arm := #[]
      for (vt, vname) in (← get).boxVariants do
        let accept ← match th?, vt with
          | some th, .named vn => pure ((← nominalHead vn) == some th)
          | some _, _ => pure false
          | none, .fn .. =>
            -- A function value of any compatible representation (wrapped).
            pure (t matches .fn .. && (← reprCompatible vt t))
          | none, .app "LCell" _ =>
            -- A thunk or task of the same kind with compatible values.
            match ← lazyOf? t, ← lazyOf? vt with
            | some (_, k1, a), some (_, k2, b) => pure (k1 == k2 && (← reprCompatible a b))
            | _, _ => pure false
          | none, _ => pure (tArr && (← arrayRepr? vt).isSome && (← reprCompatible vt t))
        let cast := !accept && vt != .unit && (← boxCastCompatible vt t)
        if !accept && !cast then continue
        let x ← fresh "bx"
        -- Arrays of another representation go through `RVec<Box>` (boxing,
        -- then unboxing each element), so that the conversions generated
        -- stay linear in the number of array types, not quadratic (nested
        -- arrays under polymorphic recursion have many representations).
        let boxArr := RR.Ty.app "RVec" #[RR.Ty.box]
        let viaBoxArr := tArr && vt != t && vt != boxArr && t != boxArr && (← arrayRepr? vt).isSome
        let body ← if cast then boxCastConv (.var x) vt t
          else if !viaBoxArr then tryCoerce (.var x) vt t
          else match ← tryCoerce (.var x) vt boxArr with
            | some b => tryCoerce b boxArr t
            | none => pure none
        if let some body := body then
          arms := arms.push { ty := boxName, ctor := some vname, binders := #[some x], body := .ofExpr body }
      let u ← boxVariant .unit
      unless arms.any (·.ctor == some u) do
        arms := arms.push { ty := boxName, ctor := some u, binders := #[none], body := .ofExpr (← zeroValue t) }
      -- The `Box` is released out of line (`boxSink`) before the panic.
      arms := arms.push { ty := boxName, ctor := none, binders := #[],
                          body := ⟨#[boxSink (.var "b")], .call "l2r_unreachable" #[t] #[]⟩ }
      let item := RR.Item.fn fname #[("b", RR.Ty.box)] t (.ofExpr (.mtch (.var "b") arms))
      modify fun s => { s with fns := (s.fns.filter fun | .fn n .. => n != fname | _ => true).push item }
      -- Record the variant count this body was generated against; a later
      -- growth of the variant set makes it pending again.
      done := done.insert fname (nvars + 1)

/-- Target `tg` called with all its arguments. -/
def targetCall (tg : FnTarget) (args : Array RR.Expr) : LowerM RR.Expr := do
  match tg.call with
  | .code fn => return .call fn #[] args
  | .extern orig typeArgs params ret => lowerExternCall orig typeArgs params ret args
  | .ctor c fullRt => ctorBuild c fullRt args
  | .stream fd i streamTy => streamFieldCall fd i streamTy args

/-- Generate `l2r_ap<j>_T`, applying a function value of type `t` to `j`
arguments (see "Function values"): a match on the variant. -/
def genApply (t : RR.Ty) (j : Nat) : LowerM Unit := do
  let (doms, _) := fnChain t
  let resJ := fnResult t j
  let tn := RR.fnTypeName t
  let as := (List.range j).toArray.map fun i => s!"l2ra{i}"
  let argsFrom (k : Nat) : Array (RR.Expr × RR.Ty) :=
    (List.range (j - k)).toArray.map fun i => (RR.Expr.var as[k + i]!, doms[k + i]!)
  -- The value `e` of the first `k` arguments (at `fnResult t k`), applied to
  -- the others.
  let rest (e : RR.Expr) (k : Nat) : LowerM RR.Expr := do
    let (r, rt) ← applyExprs e (fnResult t k) (argsFrom k)
    coerce r rt resJ
  let mut arms : Array RR.Arm :=
    #[{ ty := tn, ctor := some "z", binders := #[], body := .ofExpr (← zeroValue resJ) }]
  let rawBody ← rest (.apply (.var "l2rc") (.var as[0]!)) 1
  arms := arms.push { ty := tn, ctor := some "raw", binders := #[some "l2rc"], body := .ofExpr rawBody }
  for v in (← get).fnVariants.getD t #[] do
    let (binders, body) ← match v with
      | .wrap src =>
        let k := min (fnChain src).1.size j
        let (e, et) ← applyExprs (.var "l2rg") src ((argsFrom 0).extract 0 k)
        pure (#[some "l2rg"], ← rest (← coerce e et (fnResult t k)) k)
      | .part id m =>
        let some tg := (← get).fnTargets[id]? | throwError "lean2rr: unknown function target {id}"
        let captured := (List.range m).toArray.map fun i => RR.Expr.var s!"l2rx{i}"
        let r := tg.params.size - m
        let k := min r j
        let mut cargs := #[]
        for i in [:k] do cargs := cargs.push (← coerce (.var as[i]!) doms[i]! tg.params[m + i]!)
        let body ← if k < r then do
            -- Fewer arguments than the target needs: a partial application.
            let (pv, pt) ← partValue tg (captured ++ cargs)
            coerce pv pt resJ
          else do
            let call ← targetCall tg (captured ++ cargs)
            rest (← coerce call tg.ret (fnResult t k)) k
        pure ((List.range m).toArray.map fun i => some s!"l2rx{i}", body)
    arms := arms.push { ty := tn, ctor := some (fnVariantName v), binders, body := .ofExpr body }
  let name := applyFnName t j
  let params := #[("l2rf", t)] ++ as.zip (doms.extract 0 j)
  let item := RR.Item.fn name params resJ (.ofExpr (.mtch (.var "l2rf") arms))
  modify fun s => { s with fns := (s.fns.filter fun | .fn n .. => n != name | _ => true).push item }

/-- Generate `l2r_fconv_S_T` (see `fnConvFn`). A value that is a wrapped
value `g` of a representation `R` (`w<R>(g)`) is converted from `R`
directly: `g` itself when `R` is `T`, otherwise `l2r_fconv_R_T(g)` (generated
on demand). So a function value that travels through several
representations (a reference read at `Nat → Nat`, `Nat → Box` and
`Box → Box` in a loop) stays one wrapper deep, and coming back to its own
representation gives the value itself (like `lazyConv`'s chains). Other
values are wrapped (`w<S>`). -/
def genFnConv (src dst : RR.Ty) : LowerM Unit := do
  let name := s!"l2r_fconv_{src.enc}_{dst.enc}"
  let wrapped := RR.Expr.ctor (RR.fnTypeName dst) (some (fnVariantName (.wrap src))) #[.var "l2rf"]
  let mut arms : Array RR.Arm := #[]
  for v in (← get).fnVariants.getD src #[] do
    let .wrap r := v | continue
    let some e ← tryCoerce (.var "l2rg") r dst | continue
    arms := arms.push { ty := RR.fnTypeName src, ctor := some (fnVariantName v), binders := #[some "l2rg"], body := .ofExpr e }
  let body : RR.Expr := if arms.isEmpty then wrapped
    else .mtch (.var "l2rf") (arms.push { ty := RR.fnTypeName src, ctor := none, binders := #[], body := .ofExpr wrapped })
  let item := RR.Item.fn name #[("l2rf", src)] dst (.ofExpr body)
  modify fun s => { s with fns := (s.fns.filter fun | .fn n .. => n != name | _ => true).push item }

/-- Generate the application functions requested so far, again for those
whose type gained variants. Whether anything was generated. -/
partial def finishFnValues : LowerM Bool := do
  let mut any := false
  repeat
    let mut progress := false
    for (src, dst) in (← get).fnConvs do
      let nv := ((← get).fnVariants.getD src #[]).size
      if (← get).fnConvDone[(src, dst)]? == some nv then continue
      genFnConv src dst
      modify fun s => { s with fnConvDone := s.fnConvDone.insert (src, dst) nv }
      progress := true
    for (t, j) in (← get).fnApplies do
      let nv := ((← get).fnVariants.getD t #[]).size
      if (← get).fnApplyDone[(t, j)]? == some nv then continue
      genApply t j
      modify fun s => { s with fnApplyDone := s.fnApplyDone.insert (t, j) nv }
      progress := true
    for t in (← get).fnAddrTargets do
      let nv := ((← get).fnVariants.getD t #[]).size
      if (← get).fnAddrDone[t]? == some nv then continue
      genFnAddr t
      modify fun s => { s with fnAddrDone := s.fnAddrDone.insert t nv }
      progress := true
    if !progress then break
    any := true
  return any

/-- The generated functions that rrc's MLIR inliner is to leave out of
line (`#[transform_anchor]`, see `Emit/Program`): the conversions between
representations of a function type (`l2r_fconv_S_T`), the unboxing
functions (`l2r_unbox_…`: to a nominal type, an array, a function type),
the application and identity functions of a function type with wrapped
values of other representations (their `w<S>` arms apply or inspect the
wrapped value at `S`), and the application functions of the function types
of uniform code (types that mention `Box`), whose arms call the targets of
the uniform code.

These functions call each other: an unboxing function converts what a
`Box` holds from every representation it can hold, a conversion of a
function value converts from the wrapped representation, and the
application of a wrapped value applies it at its own representation.
Polymorphic recursion through monad transformers makes hundreds of
representations of a few Lean types, and with them a call graph of small
mutually recursive functions. rrc's MLIR inliner follows every path of
distinct small functions in such a cycle, so the program grows
exponentially with the number of representations (an 8-line `StateT`
tower used at `IO` did not build within 30 minutes or 15 GB;
docs/reussir-bugs.md, bug 20); with the application functions of uniform
types inlinable, four towers in one program (`Cn3PolyScalar`) still took
4.5 GB, 2 GB without. Out of line, they cost a call each (LLVM, which runs
after Reussir's passes, still inlines them where it pays): the unboxing of
statically unknown values and the conversions are slow paths anyway, and
wrapped applications and function values of uniform types are rare outside
such programs. -/
def anchoredFns : LowerM (Std.HashSet String) := do
  let st ← get
  let wraps (t : RR.Ty) : Bool := (st.fnVariants.getD t #[]).any (· matches .wrap _)
  let mut out : Std.HashSet String := {}
  for (src, dst) in st.fnConvs do out := out.insert s!"l2r_fconv_{src.enc}_{dst.enc}"
  for t in st.fnUnboxTargets do out := out.insert s!"l2r_unbox_fn_{t.enc}"
  for t in st.unboxTargets do out := out.insert s!"l2r_unbox_{t}"
  for (_, f) in st.unboxArrTargets do out := out.insert f
  for (t, j) in st.fnApplies do
    if wraps t || (t.subterms).contains RR.Ty.box then out := out.insert (applyFnName t j)
  for t in st.fnAddrTargets do
    if wraps t then out := out.insert s!"l2r_fn_addr_{t.enc}"
  return out

/-- The fields of the variants of function type `t`, besides `z`/`raw`. -/
def fnVariantFields (v : FnVariant) : LowerM (Array RR.Ty) := do
  match v with
  | .wrap src => return #[src]
  | .part id m =>
    let some tg := (← get).fnTargets[id]? | throwError "lean2rr: unknown function target {id}"
    return tg.params.extract 0 m

/-- The enums of all function types the generated program mentions. -/
def fnTypeItems : LowerM (Array RR.Item) := do
  let st ← get
  let mut work : Array RR.Ty := #[]
  for it in st.fns ++ st.typeItems do
    for t in it.tys do work := t.subterms work
  for (t, _) in st.boxVariants do work := t.subterms work
  for (k, _) in st.tupleTypes.toList do
    for t in k do work := t.subterms work
  let mut seen : Std.HashSet RR.Ty := {}
  let mut items := #[]
  while !work.isEmpty do
    let t := work.back!
    work := work.pop
    let .fn d c := t | continue
    if seen.contains t then continue
    seen := seen.insert t
    let mut variants : Array (String × Array RR.Ty) := #[("z", #[]), ("raw", #[.cls d c])]
    work := (RR.Ty.cls d c).subterms work
    for v in (← get).fnVariants.getD t #[] do
      let fs ← fnVariantFields v
      for f in fs do work := f.subterms work
      variants := variants.push (fnVariantName v, fs)
    items := items.push (RR.Item.enum (RR.fnTypeName t) false variants)
  return items

end LeanToReussir
