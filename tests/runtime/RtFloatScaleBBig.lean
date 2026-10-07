/-! Runtime test: `Float.scaleB x i` and `Float32.scaleB x i` with an `Int`
`i` outside the C `int` range (-2^31 to 2^31 - 1), and at its ends for
comparison. lean2rr computes `x * 2^i` for every `Int` (lean-runtime's
`scaleb`: `scalbn` of the exponent clamped to the `int` range, so the
correctly rounded zero or infinity with `x`'s sign, and zeros, infinities
and NaN kept; `NAME.l2r.out`). Natively the big-`Int` branch returns `+0.0`
when `x == 0` or `i < 0`, so a NaN, an infinity scaled down, `-0.0` and a
negative value scaled down lose their value or sign (`NAME.native.out`):
lean-runtime's LB-36, which lean2rr does not reproduce. The values are a
subset of `RtSweepFloat`'s and `RtFloat`'s, whose big exponents moved here. -/

@[noinline] def bf (x : Float) : Float := x
@[noinline] def bf32 (x : Float32) : Float32 := x
@[noinline] def bi (n : Int) : Int := n

def nan : Float := 0.0 / 0.0
def inf : Float := 1.0 / 0.0

def vals : List Float :=
  [0.0, -0.0, 1.0, -1.0, 0.5, -0.5, 1.5, -1.5, 2.5, -2.5, 0.1, 1.0/3.0, 1e-7, 123456.789, 1e22,
   1.7976931348623157e308, 2.2250738585072014e-308, 4.9406564584124654e-324, -4.9406564584124654e-324,
   1e-300, 1e300, -1e300, -9.3e18, -0.9999]

def exps : List Int :=
  [2^31 - 1, -(2^31), 2^31, -(2^31) - 1, 2^40, -(2^40), 2^70, -(2^70)]

def main : IO Unit := do
  for x in [bf nan, bf inf, bf (-inf), bf (-nan)] ++ vals do
    let x := bf x
    IO.println s!"{x}: {exps.map fun i => x.scaleB (bi i)}"
  let v32 : List Float32 := [0.0, -0.0, 1.0, -2.5, 1e-45, 3.4028235e38, -3.4028235e38]
  for x in [bf32 0.0 / bf32 0.0, bf32 1.0 / bf32 0.0, bf32 (-1.0) / bf32 0.0] ++ v32 do
    let x := bf32 x
    IO.println s!"f32 {x}: {exps.map fun i => x.scaleB (bi i)}"
