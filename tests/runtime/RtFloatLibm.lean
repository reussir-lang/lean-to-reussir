/-! Runtime test: libm results compared bit for bit: 26 functions (sin..atanh,
exp/exp2/log/log2/log10, sqrt, cbrt, ceil/floor/round/abs, `^`, atan2) over
440 inputs, `Float` and `Float32` (hashes of the result bits, plus per-value
bits of tan/sinh/cbrt/exp2 for 60 inputs).
From the round-6 adversarial reviewers, area numbers (adv6/numbers), check
FBits. -/

-- libm results compared bit for bit (Float and Float32), over many inputs.
@[noinline] def bf (x : Float) : Float := x
@[noinline] def bf32 (x : Float32) : Float32 := x
@[noinline] def bn (n : Nat) : Nat := n

def fns : List (String × (Float → Float)) :=
  [("sin", Float.sin), ("cos", Float.cos), ("tan", Float.tan), ("asin", Float.asin), ("acos", Float.acos), ("atan", Float.atan),
   ("sinh", Float.sinh), ("cosh", Float.cosh), ("tanh", Float.tanh), ("asinh", Float.asinh), ("acosh", Float.acosh), ("atanh", Float.atanh),
   ("exp", Float.exp), ("exp2", Float.exp2), ("log", Float.log), ("log2", Float.log2), ("log10", Float.log10), ("sqrt", Float.sqrt),
   ("cbrt", Float.cbrt), ("ceil", Float.ceil), ("floor", Float.floor), ("round", Float.round), ("abs", Float.abs),
   ("pow3.7", fun x => x ^ bf 3.7), ("powx", fun x => bf 1.0001 ^ x), ("atan2", fun x => Float.atan2 x (bf 0.3))]

def fns32 : List (String × (Float32 → Float32)) :=
  [("sin", Float32.sin), ("cos", Float32.cos), ("tan", Float32.tan), ("asin", Float32.asin), ("acos", Float32.acos), ("atan", Float32.atan),
   ("sinh", Float32.sinh), ("cosh", Float32.cosh), ("tanh", Float32.tanh), ("asinh", Float32.asinh), ("acosh", Float32.acosh), ("atanh", Float32.atanh),
   ("exp", Float32.exp), ("exp2", Float32.exp2), ("log", Float32.log), ("log2", Float32.log2), ("log10", Float32.log10), ("sqrt", Float32.sqrt),
   ("cbrt", Float32.cbrt), ("ceil", Float32.ceil), ("floor", Float32.floor), ("round", Float32.round), ("abs", Float32.abs),
   ("pow3.7", fun x => x ^ bf32 3.7), ("powx", fun x => bf32 1.0001 ^ x), ("atan2", fun x => Float32.atan2 x (bf32 0.3))]

def main : IO Unit := do
  -- inputs: a deterministic spread
  let mut xs : Array Float := #[]
  for i in [0:400] do
    let t := (bn i).toFloat
    xs := xs.push ((t - 200.0) * 0.0371 + 0.000123 * t * t / 7.0)
  for e in [0:40] do
    xs := xs.push (Float.ofScientific (bn (1234567 + e * 7919)) (e % 2 == 0) (bn e))
  for (name, f) in fns do
    let mut h : UInt64 := 0
    let mut firsts : Array UInt64 := #[]
    for x in xs do
      let b := (f (bf x)).toBits
      h := h * 1000003 + b
      if firsts.size < 3 then firsts := firsts.push b
    IO.println s!"{name}: {h} {firsts}"
  for (name, f) in fns32 do
    let mut h : UInt64 := 0
    for x in xs do
      let b := (f (bf32 x.toFloat32)).toBits
      h := h * 1000003 + b.toUInt64
    IO.println s!"f32 {name}: {h}"
  -- per-value detail for a few functions where libms tend to differ
  for x in xs.extract 0 60 do
    IO.println s!"d {x.toBits}: {(Float.tan x).toBits} {(Float.sinh x).toBits} {(Float.cbrt x).toBits} {(Float.exp2 x).toBits} {(Float32.tan x.toFloat32).toBits} {(Float32.cbrt x.toFloat32).toBits}"

