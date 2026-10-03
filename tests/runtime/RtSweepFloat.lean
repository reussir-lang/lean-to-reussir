/-! Runtime test: `Float`/`Float32` sweep. FOps: 49 values (±0, NaN, ±inf,
subnormals, 1e±300, 2^53+1, the rounding boundaries of every integer width)
through `toString`, `toBits`, `floor`/`ceil`/`round`/`abs`, saturating
`toUInt8..64`/`toInt8..64`/`USize`/`ISize`, `frExp`, `toFloat32`, every libm
function, `^`, `atan2`, `scaleB` (10, -1074, ±2^40, 2^31), NaN comparisons,
`max`/`min`; Float32 counterparts; `ofBits` of signalling and negative NaNs;
`Float.ofNat`/`ofInt` up to 3^700. FSweep: the printing sweep (`%f`) of
123456789e-(8..337) and 987654321e(0..329) and their Float32 casts, 60
subnormals with `frExp`, 2^e±1 for e < 70, `%f` rounding at six decimals.
From the round-6 adversarial reviewers, area numbers (adv6/numbers), checks
FOps and FSweep. -/

namespace FOps
-- from adv6/numbers/FOps.lean
-- Float/Float32 runtime ops: special values, printing, rounding, conversions, libm.
@[noinline] def bf (x : Float) : Float := x
@[noinline] def bf32 (x : Float32) : Float32 := x
@[noinline] def bn (n : Nat) : Nat := n
@[noinline] def bi (n : Int) : Int := n

def nan : Float := 0.0 / 0.0
def inf : Float := 1.0 / 0.0

def vals : List Float :=
  [0.0, -0.0, 1.0, -1.0, 0.5, -0.5, 1.5, 2.5, -2.5, 0.1, 1.0/3.0, 2.0/3.0, 1e-7, 1e-6, 5e-7, 4.9999995e-7,
   0.0000005, 123456.789, 1e15, 1e16, 1e17, 9007199254740993.0, 1e22, 1e23, 1.7976931348623157e308, 2.2250738585072014e-308,
   4.9406564584124654e-324, 1e-300, 1e300, -1e300, 255.5, 256.0, 65535.99, 4294967295.5, 4294967296.0,
   9.2233720368547758e18, 9223372036854774784.0, 1.8446744073709552e19, 18446744073709549568.0, -9.2233720368547758e18, -9.3e18, 127.9, -128.9, -129.0, -0.9999]

def main : IO Unit := do
  let specials := [bf nan, bf inf, bf (-inf), bf (-nan)]
  let mut i := 0
  for x in specials ++ vals do
    let x := bf x
    IO.println s!"{i} {x}: bits {x.toBits} floor {x.floor} ceil {x.ceil} round {x.round} abs {x.abs} neg {-x} isNaN {x.isNaN} isInf {x.isInf} isFin {x.isFinite}"
    IO.println s!"  u8 {x.toUInt8} u16 {x.toUInt16} u32 {x.toUInt32} u64 {x.toUInt64} usz {x.toUSize} i8 {x.toInt8} i16 {x.toInt16} i32 {x.toInt32} i64 {x.toInt64} isz {x.toISize}"
    IO.println s!"  frexp {x.frExp} toF32 {x.toFloat32} back {x.toFloat32.toFloat} sqrt {x.sqrt} cbrt {x.cbrt} exp {x.exp} exp2 {x.exp2} log {x.log} log2 {x.log2} log10 {x.log10}"
    IO.println s!"  sin {x.sin} cos {x.cos} tan {x.tan} asin {x.asin} acos {x.acos} atan {x.atan} sinh {x.sinh} cosh {x.cosh} tanh {x.tanh} asinh {x.asinh} acosh {x.acosh} atanh {x.atanh}"
    IO.println s!"  pow2 {x ^ bf 2.0} pow.5 {x ^ bf 0.5} 2pow {(bf 2.0) ^ x} atan2 {Float.atan2 x (bf (-1.0))} {Float.atan2 (bf 0.0) x} scaleB10 {x.scaleB (bi 10)} scaleB-1074 {x.scaleB (bi (-1074))} scaleBbig {x.scaleB (bi (2^40))} {x.scaleB (bi (-(2^40)))} {x.scaleB (bi (2^31))}"
    IO.println s!"  cmp1 {decide (x < bf 1.0)} {decide (x ≤ bf 1.0)} {x == bf 1.0} {x != x} {x == x} max {max x (bf 1.0)} min {min x (bf 1.0)} {max (bf 1.0) x}"
    i := i + 1
  -- Float32
  let v32 : List Float32 := [0.0, -0.0, 1.0, 0.1, 16777216.0, 16777217.0, 3.4028235e38, 1e-45, 1.17549435e-38, 1e30, -2.5, 2.5, 255.9, 4294967296.0]
  for x in v32 do
    let x := bf32 x
    IO.println s!"f32 {x}: bits {x.toBits} floor {x.floor} ceil {x.ceil} round {x.round} toF {x.toFloat} u8 {x.toUInt8} u32 {x.toUInt32} u64 {x.toUInt64} i8 {x.toInt8} i32 {x.toInt32} i64 {x.toInt64} sqrt {x.sqrt} exp {x.exp} log {x.log} sin {x.sin} frexp {x.frExp} scaleB {x.scaleB (bi 3)} x*x {x*x} x/3 {x / bf32 3.0}"
  let f32nan : Float32 := bf32 0.0 / bf32 0.0
  IO.println s!"f32 nan {f32nan} {f32nan.toBits} {f32nan.toFloat} {f32nan.toInt32} inf {bf32 1.0 / bf32 0.0} {(bf32 1.0 / bf32 0.0).toUInt64}"
  IO.println s!"toF32 overflow: {(bf 1e39).toFloat32} {(bf (-1e39)).toFloat32} {(bf 1e-46).toFloat32} {(bf 3.4028235677973366e38).toFloat32} {(bf 3.4028235677973367e38).toFloat32}"
  -- bits
  for b in [0x7ff0000000000001, 0xfff8000000000000, 0x7ff8000000000001, 0x8000000000000000, 0x0000000000000001, 0x7fefffffffffffff, 0x3ff0000000000001] do
    let f := Float.ofBits (b : UInt64)
    IO.println s!"ofBits {b}: {f} {f.toBits} {f.isNaN}"
  for b in [0x7f800001, 0xffc00000, 0x00000001, 0x80000000] do
    let f := Float32.ofBits (b : UInt32)
    IO.println s!"ofBits32 {b}: {f} {f.toBits} {f.isNaN}"
  -- of nat / int, runtime
  for n in [0, 1, 2^53, 2^53 + 1, 2^53 + 2, 2^63, 2^64 - 1, 2^64, 2^64 + 1, 2^1023, 2^1024 - 2^970, 2^1024 - 2^970 - 1, 2^1024, 10^400, 3^700] do
    IO.println s!"ofNat {Float.ofNat (bn n)} f32 {Float32.ofNat (bn n)} ofInt- {Float.ofInt (-(bi n))} {Float32.ofInt (-(bi n))} toFloat {(bn n).toFloat}"
  IO.println s!"conv ints: {(bn 5).toUInt64.toFloat} {(18446744073709551615 : UInt64).toFloat} {(-9223372036854775808 : Int64).toFloat} {(-1 : Int8).toFloat} {(4294967295 : UInt32).toFloat32} {(9007199254740993 : UInt64).toFloat}"
  IO.println s!"repr: {repr (bf (-1.5))} {repr (some (bf (-1.5)))} {repr [bf 2.0, bf (-0.0)]} {reprPrec (bf (-2.0)) 1024}"
  IO.println s!"bits: {(bf 1.5).toBits} {(bf 0.0).toBits} {(bf (-0.0)).toBits}"
end FOps

namespace FSweep
-- from adv6/numbers/FSweep.lean
-- Float/Float32 printing sweep over magnitudes and mantissas.
@[noinline] def bf (x : Float) : Float := x
@[noinline] def bn (n : Nat) : Nat := n

def main : IO Unit := do
  for k in [0:330] do
    let small := Float.ofScientific (bn 123456789) true (bn (k + 8))
    let large := Float.ofScientific (bn 987654321) false (bn k)
    IO.println s!"{k}: {small} {large} {-small} {small.toFloat32} {large.toFloat32} {small * 1e300} {large / 1e300}"
  -- subnormals
  let mut x := bf 2.2250738585072014e-308
  for i in [0:60] do
    IO.println s!"sub {i} {x} {x.toBits} {x * 1e308} {x.frExp}"
    x := x / 2.0
  -- integers near powers of two
  for e in [0:70] do
    let p := (bn 2) ^ (bn e)
    IO.println s!"p2 {e} {p.toFloat} {(p - 1).toFloat} {(p + 1).toFloat} {p.toFloat32} {(p.toFloat + 0.5)}"
  -- rounding of %f at 6 decimals
  for v in [0.0000005, 0.0000015, 0.0000025, 1.0000005, 2.5e-7, 0.1234565, 0.1234575, 999999.9999995, 1e-6 * 0.5] do
    IO.println s!"r {bf v} {bf (-v)}"
end FSweep

def main : IO Unit := do
  IO.println "=== FOps"
  FOps.main
  IO.println "=== FSweep"
  FSweep.main
