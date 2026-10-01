import Lean
import LeanToReussir.PassConfig

/-!
# Cheap constants recomputed (optimization `cheap-consts`)

Native Lean emits simple ground values (literals, constructors of literals)
as static data, which costs nothing to read. lean2rr keeps a constant in a
once-cell (`cafAccessor`); for a constant that only builds unboxed values
from small literals, constructors and total scalar conversions, reading the
once-cell costs more than computing the value, so it is recomputed at every
use instead (translation plan §5.12). Such a constant cannot panic, trace or
allocate, so the change is unobservable. Without this pass every constant
is cached.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Types whose values need no heap cell. -/
def isUnboxedTy (t : RR.Ty) : LowerM Bool := do
  match t with
  | .named n =>
    if n ∈ ["Nat", "Int", "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "f32", "f64",
            "bool", "L2RUnit"] then return true
    return ((← get).typeInfos[n]?.map (·.shape == .enumLike)).getD false
  | _ => return false

/-- A constant whose code only builds unboxed values from small literals
and constructors (`Int.ofNat 0`, an enumeration value). It cannot panic,
trace or allocate, so it is recomputed at every use: cheaper than reading a
once-cell (native Lean emits such constants as static data). -/
partial def isCheapConst (c : Code .pure) (fuel : Nat := 8) : LowerM Bool := do
  match c with
  | .let d k =>
    unless ← isUnboxedTy (← lowerType d.type) do return false
    let ok ← match d.value with
      | .lit (.str _) => pure false
      | .lit (.nat n) => pure (n < 2 ^ 63)
      | .lit _ => pure true
      | .erased => pure true
      | .const f _ args =>
        if (← getEnv).isConstructor f then pure true
        -- Total conversions of scalars (`UInt32.ofNat 0`, the default of
        -- `Inhabited UInt32`, `Float.ofBits` of a bit pattern).
        else if isScalarConversion (((← read).keys.find? f).map (·.decl) |>.getD f) then pure true
        -- Another such constant.
        else if args.isEmpty && fuel > 0 then
          match (← read).decls.find? f with
          | some { params := #[], value := .code b, .. } => isCheapConst b (fuel - 1)
          | _ => pure false
        else pure false
      | _ => pure false
    if ok then isCheapConst k fuel else return false
  | .return _ => return true
  | _ => return false
where
  isScalarConversion (f : Name) : Bool :=
    f ∈ [``UInt8.ofNat, ``UInt16.ofNat, ``UInt32.ofNat, ``UInt64.ofNat, ``USize.ofNat,
         ``UInt8.ofNatLT, ``UInt16.ofNatLT, ``UInt32.ofNatLT, ``UInt64.ofNatLT, ``USize.ofNatLT,
         ``Int8.ofNat, ``Int16.ofNat, ``Int32.ofNat, ``Int64.ofNat, ``ISize.ofNat,
         ``Int8.ofInt, ``Int16.ofInt, ``Int32.ofInt, ``Int64.ofInt, ``ISize.ofInt,
         ``Float.ofBits, ``Float32.ofBits,
         ``Char.ofNat, ``Nat.toUInt8, ``Nat.toUInt16, ``Nat.toUInt32, ``Nat.toUInt64,
         ``Nat.toUSize]

/-- Registry entry point: a constant is recomputed when `isCheapConst` says
so (or an earlier hook did). -/
def Opt.CheapConsts.install (c : PassConfig) : PassConfig :=
  let prev := c.lower.recomputeConst
  { c with lower := { c.lower with recomputeConst := fun body => do
      if ← prev body then return true
      isCheapConst body } }

end LeanToReussir
