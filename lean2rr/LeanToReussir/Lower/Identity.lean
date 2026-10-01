import LeanToReussir.Lower.Promises

/-! # Identity (`ptrAddrUnsafe`)

`ptrAddrUnsafe x` answers what native Lean answers (translation plan §9):
the word of a boxed scalar (`lean_box(n) = 2n+1`) for values Lean
represents so, the address of the Lean object otherwise. lean2rr's
representations are mapped back to Lean's: a `Box` answers its payload's
identity, a function value wrapped for another representation the wrapped
value's, a thunk or task converted to another representation the
original's, a `[value]` struct its field's. -/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Whether values of type `t` are natively boxed into a new cell each time
they are boxed (`lean_box_uint64`, `lean_box_float`, …; also `Int64`,
`ISize`, which are `UInt64` underneath). -/
def cellScalar (t : RR.Ty) : Bool :=
  match t with
  | .named n => n ∈ ["u64", "i64", "f64", "f32"]
  | _ => false

/-- The type a value of type `t` is natively represented by: through
`[value]` structs, their field's type. -/
partial def nativeLeaf (t : RR.Ty) : LowerM RR.Ty := do
  let .named n := t | return t
  let some info := (← get).typeInfos[n]? | return t
  if !info.value then return t
  let some layout := info.ctors.find? info.ctorOrder[0]! | return t
  let some ft := layout.posTys[0]? | return t
  nativeLeaf ft

/-- `l2r_lazy_addr_S(c)`: the identity of a thunk or task: its cell's
address, or the original's that a converted cell records (see
`lazyConv`). -/
def lazyAddrFn (z : String) : LowerM String := do
  let name := s!"l2r_lazy_addr_{z}"
  lazyFn name do
    let zt := RR.Ty.named z
    let body : RR.Block := .ofExpr (.mtch (.call "l2r_lcell_get" #[zt] #[.var "c"]) #[
      lazyArm z "conv" #[none, none, some "a"] (.ofExpr (.var "a")),
      lazyArm z "busyconv" #[some "a"] (.ofExpr (.var "a")),
      lazyArm z "convdone" #[none, none, some "a"] (.ofExpr (.var "a")),
      { ty := z, ctor := none, binders := #[], body := .ofExpr (.call "l2r_lcell_addr" #[zt] #[.var "c"]) }])
    return #[.fn name #[("c", .app "LCell" #[zt])] (.named "u64") body]

/-- `l2r_fn_addr_T(f)`, the identity of a function value of type `t`
(generated at the end, when its variants are known: `genFnAddr`). -/
def fnAddrFn (t : RR.Ty) : LowerM String := do
  unless (← get).fnAddrTargets.contains t do
    modify fun s => { s with fnAddrTargets := s.fnAddrTargets.push t }
  return s!"l2r_fn_addr_{t.enc}"

/-- `l2r_box_addr(b)`, the identity of a `Box`'s payload (generated at the
end, when the variants are known: `genBoxAddr`). -/
def boxAddrFn : LowerM String := do
  modify fun s => { s with boxAddrWanted := true }
  return "l2r_box_addr"

/-- A `u64` literal as an expression. -/
def u64Lit (k : Nat) : LowerM RR.Expr := do
  let o ← fresh "pa"
  return .block ⟨#[(o, some (.named "u64"), .atom (toString k))], .var o⟩

/-- `l2r_addr_T(x)` for a shared nominal type `tn` with constructors
without fields: natively those are the boxed scalars of their index. -/
def recAddrFn (tn : String) (info : TypeInfo) : LowerM String := do
  let name := s!"l2r_addr_{tn}"
  unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
    let mut arms : Array RR.Arm := #[]
    for h : i in [:info.ctorOrder.size] do
      let some l := info.ctors.find? info.ctorOrder[i] | continue
      if (l.fields.filterMap id).isEmpty then
        arms := arms.push { ty := tn, ctor := some l.variant, binders := #[], body := .ofExpr (← u64Lit (2 * i + 1)) }
    let dflt := RR.Expr.call "l2r_ptr_addr_rec" #[.named tn] #[.var "x"]
    arms := arms.push { ty := tn, ctor := none, binders := #[], body := .ofExpr dflt }
    modify fun s => { s with fns := s.fns.push (.fn name #[("x", .named tn)] (.named "u64") (.ofExpr (.mtch (.var "x") arms))) }
  return name

/-- `ptrAddrUnsafe` of value `e : t` (see the section comment). A value
natively boxed into a new cell at each boxing (`UInt64`, `Float`) answers
a fresh number: natively two calls on the same variable box it twice (only
Lean's CSE, which lean2rr keeps, merges calls). -/
partial def addrOf (e : RR.Expr) (t : RR.Ty) : LowerM RR.Expr := do
  let evalThen (k : RR.Expr) : LowerM RR.Expr := do
    let d ← fresh "pd"
    return .block ⟨#[(d, some t, e)], k⟩
  match t with
  | .named n =>
    if n == "Nat" then return .call "l2r_addr_nat" #[] #[e]
    if n == "Int" then return .call "l2r_addr_int" #[] #[e]
    -- `box(0)`.
    if n == "L2RUnit" then return ← evalThen (← u64Lit 1)
    if cellScalar t then return ← evalThen (.call "l2r_addr_fresh" #[] #[])
    if n == boxName then return .call (← boxAddrFn) #[] #[e]
    -- `UInt8/16/32`, `Char`, `Bool`, enumerations.
    if let some i ← scalarWord e n then return .call "l2r_addr_word" #[] #[i]
    if n ∈ ["LStr", "LBig", "LNatArr", "LIntArr", "LHandle"] then
      return .call "l2r_ptr_addr_obj" #[t] #[e]
    match (← get).typeInfos[n]? with
    | some info =>
      if info.value then
        let some layout := info.ctors.find? info.ctorOrder[0]! | return ← evalThen (← u64Lit 1)
        let some ft := layout.posTys[0]? | return ← evalThen (← u64Lit 1)
        return ← withVar "pv" t e fun v => addrOf (.field v 0) ft
      if hasNullaryCtor info then return .call (← recAddrFn n info) #[] #[e]
      return .call "l2r_ptr_addr_rec" #[t] #[e]
    | none =>
      if ← isBoundaryTy t then return .call "l2r_ptr_addr_obj" #[t] #[e]
      evalThen (.call "l2r_addr_fresh" #[] #[])
  | .app "RVec" _ | .app "LRef" _ => return .call "l2r_ptr_addr_obj" #[t] #[e]
  | .app "LCell" #[.named z] => return .call (← lazyAddrFn z) #[] #[e]
  | .fn .. => return .call (← fnAddrFn t) #[] #[e]
  | _ => evalThen (.call "l2r_addr_fresh" #[] #[])

/-- Generate `l2r_fn_addr_T` (see `fnAddrFn`): a wrapped value answers the
identity of the value it wraps, the `box(0)` placeholder `1`, others their
cell. -/
def genFnAddr (t : RR.Ty) : LowerM Unit := do
  let name := s!"l2r_fn_addr_{t.enc}"
  let tn := RR.fnTypeName t
  let mut arms : Array RR.Arm := #[{ ty := tn, ctor := some "z", binders := #[], body := .ofExpr (← u64Lit 1) }]
  for v in (← get).fnVariants.getD t #[] do
    let .wrap src := v | continue
    let a ← addrOf (.var "l2rg") src
    arms := arms.push { ty := tn, ctor := some (fnVariantName v), binders := #[some "l2rg"], body := .ofExpr a }
  arms := arms.push { ty := tn, ctor := none, binders := #[], body := .ofExpr (.call "l2r_ptr_addr_rec" #[t] #[.var "l2rf"]) }
  let item := RR.Item.fn name #[("l2rf", t)] (.named "u64") (.ofExpr (.mtch (.var "l2rf") arms))
  modify fun s => { s with fns := (s.fns.filter fun | .fn n .. => n != name | _ => true).push item }

/-- Generate `l2r_box_addr` (see `boxAddrFn`): the payload's identity; a
payload natively boxed into a cell (`UInt64`, `Float`, or a `[value]`
struct over one) answers the `Box` cell, which is that cell here. -/
def genBoxAddr : LowerM Unit := do
  let name := "l2r_box_addr"
  let mut arms : Array RR.Arm := #[]
  for (vt, v) in (← get).boxVariants do
    if cellScalar (← nativeLeaf vt) then
      let cell := RR.Expr.call "l2r_ptr_addr_rec" #[RR.Ty.box] #[.var "b"]
      arms := arms.push { ty := boxName, ctor := some v, binders := #[none], body := .ofExpr cell }
    else
      arms := arms.push { ty := boxName, ctor := some v, binders := #[some "x"], body := .ofExpr (← addrOf (.var "x") vt) }
  let item := RR.Item.fn name #[("b", RR.Ty.box)] (.named "u64") (.ofExpr (.mtch (.var "b") arms))
  modify fun s => { s with fns := (s.fns.filter fun | .fn n .. => n != name | _ => true).push item,
                           boxAddrDone := s.boxVariants.size }

/-- Whether code `c` asks for an object's identity: a call of
`ptrAddrUnsafe` (extern `lean_ptr_addr`, to which `ptrEq`,
`withPtrAddrUnsafe` and the like inline) or of `ST.Prim.Ref.ptrEq`, also
as a function value (`keys`: instance ↦ original declaration). -/
partial def codeObservesIdentity (env : Environment) (keys : NameMap InstKey) (c : Code .pure) : Bool :=
  match c with
  | .let d k =>
    (match d.value with
     | .const f _ _ _ =>
       let orig := (keys.find? f).map (·.decl) |>.getD f
       orig == ``ST.Prim.Ref.ptrEq || getExternNameFor env `c orig == some "lean_ptr_addr"
     | _ => false) || codeObservesIdentity env keys k
  | .fun d k _ | .jp d k => codeObservesIdentity env keys d.value || codeObservesIdentity env keys k
  | .cases cs => cs.alts.any (codeObservesIdentity env keys ·.getCode)
  | .jmp .. | .return _ | .unreach _ => false

/-- Whether any declaration of the program asks for an object's identity
(`LowerCtx.observesIdentity`). -/
def programObservesIdentity (env : Environment) (keys : NameMap InstKey) (decls : Array (Decl .pure)) : Bool :=
  decls.any fun d => match d.value with
    | .code c => codeObservesIdentity env keys c
    | _ => false

end LeanToReussir
