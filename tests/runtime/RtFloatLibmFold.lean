/-! Runtime test: libm functions on literal operands (cross-tests XT-3, XT-4;
fixtures A720 and the `float32` literal rows). Natively Lean's C calls the C
library's function at run time even when the operand is a literal (a closed
term sits in a once-cell clang cannot see into), so the results are glibc's.
lean2rr used LLVM's intrinsics, and LLVM evaluates or rewrites a call whose
operand it knows, one ulp away from glibc on these inputs:
- `Float32` functions folded by evaluating the `Float` one and rounding;
- `Float.exp2` folded through `pow(2, x)`;
- `x ^ 0.5` rewritten into `sqrt x`, `x ^ 2.0` into `x * x`, `x ^ -1.0`
  into `1 / x`, `2.0 ^ y` into `exp2 y` (and `10.0 ^ y` into `exp10 y`,
  which LLVM may do), for `Float` and `Float32`, with the other operand
  known or not;
- `Float32.pow` and `Float32.atan2` on two literals folded in double
  precision.
Each line computes a function once on a literal operand and once on the
same operand read from the command line, and prints both results as bits.
The inputs are ones where the folded or rewritten value differs from
glibc's (searched with glibc 2.39 on aarch64). -/

-- `x ^ c` and `c ^ y` with a literal `c`, as in fixture A720.
def half (x : Float) : Float := x ^ 0.5
def sq (x : Float) : Float := x ^ 2.0
def inv (x : Float) : Float := x ^ Float.ofBits 0xBFF0000000000000
def two (y : Float) : Float := 2.0 ^ y
def ten (y : Float) : Float := 10.0 ^ y
def half32 (x : Float32) : Float32 := x ^ 0.5
def sq32 (x : Float32) : Float32 := x ^ 2.0
def inv32 (x : Float32) : Float32 := x ^ (-1.0)
def two32 (y : Float32) : Float32 := 2.0 ^ y
def ten32 (y : Float32) : Float32 := 10.0 ^ y

def main (args : List String) : IO Unit := do
  let a := args.toArray.map String.toNat!
  let f32 (i : Nat) : Float32 := Float32.ofBits a[i]!.toUInt32
  let f64 (i : Nat) : Float := Float.ofBits a[i]!.toUInt64
  let p32 (name : String) (lit arg : Float32) : IO Unit :=
    IO.println s!"{name}: literal {lit.toBits} argv {arg.toBits}"
  let p64 (name : String) (lit arg : Float) : IO Unit :=
    IO.println s!"{name}: literal {lit.toBits} argv {arg.toBits}"
  p64 "exp2 35.74477454358792" (Float.exp2 35.74477454358792) (Float.exp2 (f64 25))
  p32 "sin 0x3f19c612" (Float32.sin (Float32.ofBits 0x3f19c612)) (Float32.sin (f32 0))
  p32 "sin 0x3d525610" (Float32.sin (Float32.ofBits 0x3d525610)) (Float32.sin (f32 1))
  p32 "cos 0x3f88c811" (Float32.cos (Float32.ofBits 0x3f88c811)) (Float32.cos (f32 2))
  p32 "cos 0x3dce4fee" (Float32.cos (Float32.ofBits 0x3dce4fee)) (Float32.cos (f32 3))
  p32 "tan 0x3f56cf56" (Float32.tan (Float32.ofBits 0x3f56cf56)) (Float32.tan (f32 4))
  p32 "asin 0x3f22fcc1" (Float32.asin (Float32.ofBits 0x3f22fcc1)) (Float32.asin (f32 5))
  p32 "acos 0x3f13ed6a" (Float32.acos (Float32.ofBits 0x3f13ed6a)) (Float32.acos (f32 6))
  p32 "atan 0x4033b00b" (Float32.atan (Float32.ofBits 0x4033b00b)) (Float32.atan (f32 7))
  p32 "sinh 0x4087ada2" (Float32.sinh (Float32.ofBits 0x4087ada2)) (Float32.sinh (f32 8))
  p32 "sinh 0x3c036224" (Float32.sinh (Float32.ofBits 0x3c036224)) (Float32.sinh (f32 9))
  p32 "cosh 0x403fc55f" (Float32.cosh (Float32.ofBits 0x403fc55f)) (Float32.cosh (f32 10))
  p32 "cosh 0x3e00944e" (Float32.cosh (Float32.ofBits 0x3e00944e)) (Float32.cosh (f32 11))
  p32 "tanh 0x3fef4398" (Float32.tanh (Float32.ofBits 0x3fef4398)) (Float32.tanh (f32 12))
  p32 "asinh 0x40aa87de" (Float32.asinh (Float32.ofBits 0x40aa87de)) (Float32.asinh (f32 13))
  p32 "acosh 0x402dd0ac" (Float32.acosh (Float32.ofBits 0x402dd0ac)) (Float32.acosh (f32 14))
  p32 "atanh 0x3e9a4996" (Float32.atanh (Float32.ofBits 0x3e9a4996)) (Float32.atanh (f32 15))
  p32 "exp 0xbfe53b48" (Float32.exp (Float32.ofBits 0xbfe53b48)) (Float32.exp (f32 16))
  p32 "exp2 0xbf992292" (Float32.exp2 (Float32.ofBits 0xbf992292)) (Float32.exp2 (f32 17))
  p32 "exp2 0x3c1db9aa" (Float32.exp2 (Float32.ofBits 0x3c1db9aa)) (Float32.exp2 (f32 18))
  p32 "log 0x42531480" (Float32.log (Float32.ofBits 0x42531480)) (Float32.log (f32 19))
  p32 "log 0x3e1978a0" (Float32.log (Float32.ofBits 0x3e1978a0)) (Float32.log (f32 20))
  p32 "log2 0x3f733c0e" (Float32.log2 (Float32.ofBits 0x3f733c0e)) (Float32.log2 (f32 21))
  p32 "log10 0x40e7550a" (Float32.log10 (Float32.ofBits 0x40e7550a)) (Float32.log10 (f32 22))
  p32 "log10 0x3c043aad" (Float32.log10 (Float32.ofBits 0x3c043aad)) (Float32.log10 (f32 23))
  p32 "cbrt 0x3f8ee836" (Float32.cbrt (Float32.ofBits 0x3f8ee836)) (Float32.cbrt (f32 24))
  p64 "exp2 4630227447100591422" (Float.exp2 (Float.ofBits 4630227447100591422)) (Float.exp2 (f64 25))
  p64 "exp2 4631144597734966002" (Float.exp2 (Float.ofBits 4631144597734966002)) (Float.exp2 (f64 26))
  p32 "atan2f 0x3f9c337a 0x400a5a20" (Float32.atan2 (Float32.ofBits 0x3f9c337a) (Float32.ofBits 0x400a5a20)) (Float32.atan2 (f32 27) (f32 28))
  p32 "powf 0x3fe79089 0x3dcdfa40" (Float32.pow (Float32.ofBits 0x3fe79089) (Float32.ofBits 0x3dcdfa40)) (Float32.pow (f32 29) (f32 30))
  p64 "pow half 4607190032495475448" (half (Float.ofBits 4607190032495475448)) (half (f64 31))
  p64 "pow sq 4607189316783422666" (sq (Float.ofBits 4607189316783422666)) (sq (f64 32))
  p64 "pow inv 4613815095151227306" (inv (Float.ofBits 4613815095151227306)) (inv (f64 33))
  p64 "pow two 4600071516463376106" (two (Float.ofBits 4600071516463376106)) (two (f64 34))
  p64 "pow two 4614091398025240904" (two (Float.ofBits 4614091398025240904)) (two (f64 35))
  p64 "pow ten 4617989366598126008" (ten (Float.ofBits 4617989366598126008)) (ten (f64 36))
  p32 "powf half 0x41551907" (half32 (Float32.ofBits 0x41551907)) (half32 (f32 37))
  p32 "powf sq 0x42ba6fe9" (sq32 (Float32.ofBits 0x42ba6fe9)) (sq32 (f32 38))
  p32 "powf inv 0x418a9927" (inv32 (Float32.ofBits 0x418a9927)) (inv32 (f32 39))
  p32 "powf two 0xbf992292" (two32 (Float32.ofBits 0xbf992292)) (two32 (f32 40))
  p32 "powf ten 0xc115e92b" (ten32 (Float32.ofBits 0xc115e92b)) (ten32 (f32 41))
