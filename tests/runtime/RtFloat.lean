/-! Runtime test: `Float`/`Float32`: `toString` (printf `%f`), literals
(`ofScientific`), arithmetic with NaN, inf and -0.0, comparisons, libm functions,
bit casts, `scaleB`, conversions from `Nat`/`Int`. (`scaleB` by an `Int`
outside the C `int` range where native's result is wrong, lean-runtime's
LB-36: `RtFloatScaleBBig`.) -/

def vals (k : Nat) : List Float :=
  [0.0, -0.0, 1.0, -1.0, 0.1, 0.2, 0.3, 1.0/3.0, 2.0/3.0, 0.5, 1.5, 2.5, -2.5, 0.0078125, 1e-7, 5e-7,
   123456789.123456789, 1e15, 1e16, 1e21, 1e22, 1.7976931348623157e308, 2.2250738585072014e-308,
   5e-324, 1e300, -1e300, 3.141592653589793, 2.718281828459045, 1.0/0.0, -1.0/0.0, 0.0/0.0,
   k.toFloat, (k.toFloat) / 7.0, 100.0, 255.5, 4294967296.5]

def main (args : List String) : IO Unit := do
  let k := args.length + 42
  let xs := vals k
  for x in xs do
    IO.println s!"{x} neg {-x} abs {x.abs} floor {x.floor} ceil {x.ceil} round {x.round} sqrt {x.sqrt} cbrt {x.cbrt}"
    IO.println s!"  exp {x.exp} exp2 {x.exp2} log {x.log} log2 {x.log2} log10 {x.log10}"
    IO.println s!"  sin {x.sin} cos {x.cos} tan {x.tan} asin {x.asin} acos {x.acos} atan {x.atan}"
    IO.println s!"  sinh {x.sinh} cosh {x.cosh} tanh {x.tanh} asinh {x.asinh} acosh {x.acosh} atanh {x.atanh}"
    IO.println s!"  isNaN {x.isNaN} isInf {x.isInf} isFinite {x.isFinite} bits {x.toBits} ofBits {Float.ofBits x.toBits}"
    let fs : List (Float → Float) := [Float.sqrt, Float.cbrt, Float.exp, Float.exp2, Float.log, Float.log2, Float.log10,
      Float.sin, Float.cos, Float.tan, Float.asin, Float.acos, Float.atan, Float.sinh, Float.cosh, Float.tanh,
      Float.asinh, Float.acosh, Float.atanh, Float.floor, Float.ceil, Float.round, Float.abs, (· ^ 0.37), (Float.atan2 · 0.3)]
    IO.println s!"  bits of results {fs.map fun f => (f x).toBits}"
    let gs : List (Float32 → Float32) := [Float32.sqrt, Float32.cbrt, Float32.exp, Float32.log, Float32.sin, Float32.tan,
      Float32.atan, Float32.tanh, Float32.asinh, Float32.acosh, Float32.atanh, (· ^ 0.37), (Float32.atan2 · 0.3)]
    IO.println s!"  f32 bits of results {gs.map fun f => (f x.toFloat32).toBits}"
    IO.println s!"  toUInt64 {x.toUInt64} toInt64 {x.toInt64} scaleB3 {x.scaleB 3} scaleB-2000 {x.scaleB (-2000)}"
    IO.println s!"  f32 {x.toFloat32} f32 sqrt {x.toFloat32.sqrt} f32 sin {x.toFloat32.sin} f32 bits {x.toFloat32.toBits} back {x.toFloat32.toFloat}"
    for y in [0.0, -0.0, 1.0, -2.0, 0.5, 1e308, 1.0/0.0, 0.0/0.0] do
      IO.println s!"  {x} {y}: + {x + y} - {x - y} * {x * y} / {x / y} pow {x ^ y} atan2 {Float.atan2 x y} < {decide (x < y)} <= {decide (x ≤ y)} == {x == y} max {max x y} min {min x y}"
  IO.println s!"literals {(1.23456789 : Float)} {(123.456e10 : Float)} {(0.000001 : Float)} {(1e-320 : Float)} {(1.7976931348623159e308 : Float)} {(2.5e-324 : Float)}"
  IO.println s!"ofNat {(2^53 + 1).toFloat} {(2^64).toFloat} {(10^400).toFloat} {(123456789012345678901234567890 : Nat).toFloat}"
  IO.println s!"ofInt {Float.ofInt (-(2^70))} {Float.ofInt (-7)} ofScientific {Float.ofScientific 12345 true 2} {Float.ofScientific 12345 false 400} {Float.ofScientific 1 true 400}"
  IO.println s!"scaleB big {(1.5 : Float).scaleB (2^40)} {(1.5 : Float).scaleB (-(2^40))} {(0.0 : Float).scaleB (2^40)} {(-1.5 : Float).scaleB (2^70)}"
  IO.println s!"f32 literals {(0.1 : Float32)} {(1e30 : Float32)} {(16777217 : Float32)} {(1.0 : Float32) / 3.0} {(3.0e38 : Float32) * 10.0}"
  IO.println s!"f32 ops {(2.0 : Float32).sqrt} {(0.5 : Float32).exp} {(10.0 : Float32).log} {Float32.ofBits 2143289344} {(1.5 : Float32).scaleB 10}"
  IO.println s!"toString {toString (2.0 : Float)} repr {repr (2.5 : Float)} {repr (0.0/0.0 : Float)} {repr (-1.0/0.0 : Float)}"
  let sum := (List.range 1000).foldl (fun (acc : Float) i => acc + 1.0 / (i.toFloat + 1.0)) 0.0
  IO.println s!"harmonic {sum}"
  let arr : FloatArray := (List.range 10).foldl (fun a i => a.push (i.toFloat * 0.5)) FloatArray.empty
  IO.println s!"floatarray {arr.size} {arr.get! 3} {arr.get! 100} {(arr.set! 2 9.5).get! 2} {arr.toList}"
