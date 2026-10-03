import LeanToReussir.Lower.Promises

/-! # Identity (`ptrAddrUnsafe`)

lean2rr does not emulate native pointer identity (translation plan §9).
`ptrAddrUnsafe x` answers the address of the cell that holds `x` in its
own representation, where it has one, and otherwise a word computed from
the value. Two answers are therefore equal only for the same cell or for
equal values: `ptrEq` saying `true` still means equal values, which code
using it as a shortcut for equality needs (`Array.mapMono`). Values that
are natively one object can answer differently (a value and its
conversion to another representation, two boxings of one value). -/

namespace LeanToReussir
open Lean Compiler LCNF

/-- A `u64` literal as an expression. -/
def u64Lit (k : Nat) : LowerM RR.Expr := do
  let o ← fresh "pa"
  return .block ⟨#[(o, some (.named "u64"), .atom (toString k))], .var o⟩

/-- `ptrAddrUnsafe` of value `e : t`:
- a heap value (a record, a function value, a `Box`, a string, an array, a
  big number, a reference, a thunk or task, a runtime handle): its cell's
  address (a nullary constructor of a shared enum: its immediate);
- a `Nat` below 2^63, an `Int` in the `int32` range, `UInt8/16/32`,
  `Char`, `Bool`, an enumeration: the boxed scalar word `2n+1`; `Unit`
  and erased values: `1`;
- `UInt64`, `Float`, `Float32`: their bits;
- a `[value]` struct: its field's;
- anything else (a `Nat` from 2^63 to 2^64, an `Int` outside `int32`):
  a number answered only once (`l2r_addr_fresh`). -/
partial def addrOf (e : RR.Expr) (t : RR.Ty) : LowerM RR.Expr := do
  let evalThen (k : RR.Expr) : LowerM RR.Expr := do
    let d ← fresh "pd"
    return .block ⟨#[(d, some t, e)], k⟩
  let u64 := RR.Ty.named "u64"
  match t with
  | .named n =>
    if n == "Nat" then return .call "l2r_addr_nat" #[] #[e]
    if n == "Int" then return .call "l2r_addr_int" #[] #[e]
    if n == "u64" then return e
    if n == "i64" then return .cast e u64
    if n == "f64" then return .call "l2r_f64_raw_bits" #[] #[e]
    if n == "f32" then return .cast (.call "l2r_f32_raw_bits" #[] #[e]) u64
    -- `box(0)`.
    if n == "L2RUnit" then return ← evalThen (← u64Lit 1)
    if n == boxName then return .call "l2r_ptr_addr_rec" #[t] #[e]
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
      return .call "l2r_ptr_addr_rec" #[t] #[e]
    | none =>
      if ← isBoundaryTy t then return .call "l2r_ptr_addr_obj" #[t] #[e]
      evalThen (.call "l2r_addr_fresh" #[] #[])
  | .app "RVec" _ | .app "LRef" _ | .app "LCell" _ => return .call "l2r_ptr_addr_obj" #[t] #[e]
  | .fn .. => return .call "l2r_ptr_addr_rec" #[t] #[e]
  | _ => evalThen (.call "l2r_addr_fresh" #[] #[])

/-- Whether code `c` asks for an object's identity or sharing: a call of
`ptrAddrUnsafe` (extern `lean_ptr_addr`, to which `ptrEq`,
`withPtrAddrUnsafe` and the like inline), of `ST.Prim.Ref.ptrEq`, or of
`dbgTraceIfShared` (extern `lean_dbg_trace_if_shared`, which reads the
count), also as a function value (`keys`: instance ↦ original
declaration). (`isExclusiveUnsafe` answers `false` here whatever the
count.) -/
partial def codeObservesIdentity (env : Environment) (keys : NameMap InstKey) (c : Code .pure) : Bool :=
  match c with
  | .let d k =>
    (match d.value with
     | .const f _ _ _ =>
       let orig := (keys.find? f).map (·.decl) |>.getD f
       orig == ``ST.Prim.Ref.ptrEq ||
         (getExternNameFor env `c orig).any (· ∈ ["lean_ptr_addr", "lean_dbg_trace_if_shared"])
     | _ => false) || codeObservesIdentity env keys k
  | .fun d k _ | .jp d k => codeObservesIdentity env keys d.value || codeObservesIdentity env keys k
  | .cases cs => cs.alts.any (codeObservesIdentity env keys ·.getCode)
  | .jmp .. | .return _ | .unreach _ => false

/-- Whether any declaration of the program asks for an object's identity
or sharing (`LowerCtx.observesIdentity`). -/
def programObservesIdentity (env : Environment) (keys : NameMap InstKey) (decls : Array (Decl .pure)) : Bool :=
  decls.any fun d => match d.value with
    | .code c => codeObservesIdentity env keys c
    | _ => false

end LeanToReussir
