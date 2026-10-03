/-! Runtime test: 3000 random `Float`/`Float32` bit patterns (fixed LCG seed)
through `toString`, `reprPrec` at precedence 70, `frExp`, saturating
`toUInt64`/`toInt64`/`toUInt8`/`toInt16`/Float32 `toUInt32`/`toInt32`,
`scaleB -1000`, `toFloat32`/`toFloat`, `round`/`floor`/`abs`.
From the round-7 review, area D (rv7/rtdata), check DFloat. -/

-- Printing of random doubles and floats from random bit patterns; repr,
-- frExp, scaleB, toUInt*/toInt* saturation on them.
def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def main : IO Unit := do
  let mut s : UInt64 := 4242
  let mut h : UInt64 := 0
  for k in [0:3000] do
    s := lcg s
    let bits := s ^^^ (lcg s >>> 7)
    let x := Float.ofBits bits
    let y := Float32.ofBits (bits >>> 32).toUInt32
    let (m, e) := x.frExp
    let line := s!"{k} {x} {reprPrec x 70} {y} {m} {e} {x.toUInt64} {x.toInt64} {x.toUInt8} {x.toInt16} {y.toUInt32} {y.toInt32} {x.scaleB (-1000)} {x.toFloat32} {y.toFloat} {x.round} {x.floor} {x.abs}"
    h := mixHash h (hash line)
    if k % 3 == 0 then IO.println line
  IO.println s!"h {h}"

