import Lean
import LeanToReussir.PassConfig

/-!
# Cheap constants recomputed (optimization `cheap-consts`)

Native Lean emits simple ground values (literals, constructors of literals)
as static data, which costs nothing to read. lean2rr keeps a constant in a
once-cell (`cafAccessor`); for a constant that only builds unboxed values
from small literals, constructors and total scalar conversions, reading the
once-cell costs more than computing the value, so it is recomputed at every
use instead (translation plan §5.12). Every `Nat` or `Int` such a constant
builds must be a small, one-word value (a `Nat` below 2^63, an `Int` in the
`int32` range): a bigger one is a heap big number, which recomputing would
allocate at every use (RV8N-01). Such a constant cannot panic, trace or
allocate, so the change is unobservable. Without this pass every constant
is cached.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Types whose values need no heap cell: for `Nat` and `Int`, their small
values only (`isCheapConst` checks the values). -/
def isUnboxedTy (t : RR.Ty) : LowerM Bool := do
  match t with
  | .named n =>
    if n ∈ ["Nat", "Int", "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "f32", "f64",
            "bool", "L2RUnit"] then return true
    return ((← get).typeInfos[n]?.map (·.shape == .enumLike)).getD false
  | _ => return false

/-- A constant whose code only builds unboxed values from small literals
and constructors (`Int.ofNat 0`, an enumeration value), every `Nat` and
`Int` among them small: a `Nat` literal or `Nat.succ` below 2^63, `Int.ofNat`
and `Int.negSucc` of a value in the `int32` range (a bigger `Nat`/`Int` is
a heap big number). It cannot panic, trace or allocate, so it is recomputed
at every use: cheaper than reading a once-cell (native Lean emits such
constants as static data). `known` holds the values of the `Nat`/`Int`
variables bound so far when they are known (a value from another such
constant is small but unknown). -/
partial def isCheapConst (c : Code .pure) (fuel : Nat := 8) (known : Std.HashMap FVarId Int := {}) :
    LowerM Bool := do
  match c with
  | .let d k =>
    unless ← isUnboxedTy (← lowerType d.type) do return false
    -- `none`: not cheap; `some v`: cheap, with the value `v` if known.
    let val : Option (Option Int) ← match d.value with
      | .lit (.str _) => pure none
      | .lit (.nat n) => pure (if n < 2 ^ 63 then some (some n) else none)
      | .lit _ => pure (some none)
      | .erased => pure (some none)
      | .const f _ args =>
        if (← getEnv).isConstructor f then pure (smallCtor f args known)
        -- Total conversions of scalars (`UInt32.ofNat 0`, the default of
        -- `Inhabited UInt32`, `Float.ofBits` of a bit pattern).
        else if isScalarConversion (((← read).keys.find? f).map (·.decl) |>.getD f) then pure (some none)
        -- Another such constant.
        else if args.isEmpty && fuel > 0 then
          match (← read).decls.find? f with
          | some { params := #[], value := .code b, .. } =>
            pure (if ← isCheapConst b (fuel - 1) then some none else none)
          | _ => pure none
        else pure none
      | _ => pure none
    match val with
    | some v => isCheapConst k fuel (match v with | some n => known.insert d.fvarId n | none => known)
    | none => return false
  | .return _ => return true
  | _ => return false
where
  /-- A constructor application that builds a small value (its value when
  it is a `Nat` or `Int`): `Nat.succ k` below 2^63, `Int.ofNat k` and
  `Int.negSucc k` in the `int32` range, for a known `k`; any other
  constructor (an enumeration value, `Nat.zero`). -/
  smallCtor (f : Name) (args : Array (Lean.Compiler.LCNF.Arg .pure)) (known : Std.HashMap FVarId Int) :
      Option (Option Int) :=
    let arg : Option Int := match args[0]? with
      | some (Lean.Compiler.LCNF.Arg.fvar x) => known[x]?
      | _ => none
    if f == ``Nat.zero then some (some 0)
    else if f == ``Nat.succ then
      match arg with
      | some k => if k + 1 < 2 ^ 63 then some (some (k + 1)) else none
      | none => none
    else if f == ``Int.ofNat then
      match arg with
      | some k => if k < 2 ^ 31 then some (some k) else none
      | none => none
    else if f == ``Int.negSucc then
      match arg with
      | some k => if k < 2 ^ 31 then some (some (-(k + 1))) else none
      | none => none
    else some none
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
