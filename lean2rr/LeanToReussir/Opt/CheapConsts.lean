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
builds must cost no allocation (NatEncoding): a literal (any is free, a
read-only object), and a computed value that is small (`natIsSmall`,
`intIsSmall`: in [-2^61, 2^61)). The limit on computed values comes from
leanrt's representation (until D8), where a bigger one was a heap number
made at every use (RV8N-01). Reussir folds arithmetic on literals (`+`,
`-`, negation) into a literal, so a bigger value computed from literals
usually costs no allocation either; the limit stays, a cost model on the
safe side (a constant it refuses is only cached). Such a constant cannot
panic, trace or allocate, so the change is unobservable.
Without this pass every constant is cached.
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

/-- A constant whose code only builds unboxed values from free literals
and constructors (`Int.ofNat 0`, an enumeration value), every `Nat` and
`Int` among them free: a literal (any is free), a computed
`Nat.succ`, `Int.ofNat` or `Int.negSucc` that is small (`natIsSmall`,
`intIsSmall`; a bigger `Nat`/`Int` is a heap big number). It cannot
panic, trace or allocate, so it is recomputed at every use: cheaper than
reading a once-cell (native Lean emits such constants as static data).
`known` holds the values of the `Nat`/`Int` variables bound so far when
they are known (a value from another such constant is free but
unknown). -/
partial def isCheapConst (c : Code .pure) (fuel : Nat := 8) (known : Std.HashMap FVarId Int := {}) :
    LowerM Bool := do
  match c with
  | .let d k =>
    unless ← isUnboxedTy (← lowerType d.type) do return false
    -- `none`: not cheap; `some v`: cheap, with the value `v` if known.
    let val : Option (Option Int) ← match d.value with
      | .lit (.str _) => pure none
      | .lit (.nat n) => pure (some (some n))
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
  it is a `Nat` or `Int`): `Nat.succ k`, `Int.ofNat k` and `Int.negSucc k`
  small (`natIsSmall`, `intIsSmall`), for a known `k`; any other
  constructor (an enumeration value, `Nat.zero`). -/
  smallCtor (f : Name) (args : Array (Lean.Compiler.LCNF.Arg .pure))
      (known : Std.HashMap FVarId Int) : Option (Option Int) :=
    let arg : Option Int := match args[0]? with
      | some (Lean.Compiler.LCNF.Arg.fvar x) => known[x]?
      | _ => none
    if f == ``Nat.zero then some (some 0)
    else if f == ``Nat.succ then
      match arg with
      | some k => if natIsSmall (k + 1).toNat then some (some (k + 1)) else none
      | none => none
    else if f == ``Int.ofNat then
      match arg with
      | some k => if intIsSmall k then some (some k) else none
      | none => none
    else if f == ``Int.negSucc then
      match arg with
      | some k => if intIsSmall (-(k + 1)) then some (some (-(k + 1))) else none
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
