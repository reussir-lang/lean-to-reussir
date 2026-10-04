/-! Runtime test: Lean loops (self tail calls, natively loops) that call every
`Float` and `Float32` libm extern, on a 1 MiB stack (`LEAN_STACK_SIZE_KB=1024`,
`.pipe`). A libm call that is a texture LLVM does not inline (a call through
the packed-argument FFI boundary: lean-runtime's `cbrt` port, review
RULR-01), or that inlines lean-runtime's `black_box` (`pow`, `exp2`, the
`Float32` functions), leaves a stack slot that escapes into the loop, and
LLVM then keeps the self tail call: the stack grew at every iteration and
overflowed ("Stack overflow detected"). leanrt calls those out of line
(`leanrt::float::libm_call`). Natively each is a call into libm. -/

partial def l64 (i n : UInt64) (acc : Float) : Float :=
  if i == n then acc else
  let x := i.toFloat / 1000.0 + 0.5
  let y := Float.sin x + Float.cos x + Float.tan x + Float.asin (x / 1.0e9) + Float.acos (x / 1.0e9)
    + Float.atan x + Float.atan2 x 3.0 + Float.sinh (x / 1.0e6) + Float.cosh (x / 1.0e6) + Float.tanh x
    + Float.asinh x + Float.acosh (x + 1.0) + Float.atanh (x / 1.0e9) + Float.exp (x / 1.0e6)
    + Float.exp2 (x / 1.0e6) + Float.log x + Float.log2 x + Float.log10 x + Float.pow x 0.3
    + Float.sqrt x + Float.cbrt x + Float.ceil x + Float.floor x + Float.round x + Float.abs x
  l64 (i + 1) n (acc + y)

partial def l32 (i n : UInt64) (acc : Float32) : Float32 :=
  if i == n then acc else
  let x := i.toFloat32 / 1000.0 + 0.5
  let y := Float32.sin x + Float32.cos x + Float32.tan x + Float32.asin (x / 1.0e9) + Float32.acos (x / 1.0e9)
    + Float32.atan x + Float32.atan2 x 3.0 + Float32.sinh (x / 1.0e6) + Float32.cosh (x / 1.0e6) + Float32.tanh x
    + Float32.asinh x + Float32.acosh (x + 1.0) + Float32.atanh (x / 1.0e9) + Float32.exp (x / 1.0e6)
    + Float32.exp2 (x / 1.0e6) + Float32.log x + Float32.log2 x + Float32.log10 x + Float32.pow x 0.3
    + Float32.sqrt x + Float32.cbrt x + Float32.ceil x + Float32.floor x + Float32.round x + Float32.abs x
  l32 (i + 1) n (acc + y)

-- The same through `for` (a range loop specialized into a recursive function).
def loopFor (n : Nat) : Float := Id.run do
  let mut acc : Float := 0
  for i in [0:n] do
    acc := acc + Float.pow i.toFloat 0.5 + Float.exp2 (i.toFloat / 1.0e7) + Float.cbrt i.toFloat
      + (Float32.sin i.toFloat32).toFloat
  return acc

def main (args : List String) : IO Unit := do
  let n := (args.headD "200000").toNat!
  IO.println (l64 0 n.toUInt64 0)
  IO.println (l32 0 n.toUInt64 0)
  IO.println (loopFor n)
