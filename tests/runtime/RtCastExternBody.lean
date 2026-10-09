/-! Runtime test (`programCasts`, the externs of the program): an
`@[extern]` declaration whose Lean definition reads an `Array UInt64` as an
`Array Float`, a `cast` through an equation that an axiom of the program
states. lean2rr runs the definition (translation plan §5.8), so the program
can cast: every compact kind is off (`RtCastExternBody.l2r-debug`), and the
words' boxes are read as floats by their bits, as natively (where the C
code in `RtCastExternBody.ffi.c` reads the same boxed cells). The extern is
a `partial def`: its value is only an inhabitant of its type, and the code
Lean compiles, which mentions the axiom, is its `_unsafe_rec` copy; the
compiled code erases the proof. So only the walk of `programCasts` through
the extern's own code (the `_unsafe_rec` copy) sees the cast: an extern of
the program no longer counts as one by itself (`RtCArrExtern`). -/

axiom wordsAreFloats : Array UInt64 = Array Float

/-- The sum of `a`'s words from index `i` on, each read as a `Float`. -/
@[extern "rt_cast_sum_as_floats"]
partial def sumAsFloats (a : @& Array UInt64) (i : USize) (acc : Float) : Float :=
  let fs : Array Float := cast wordsAreFloats a
  if i.toNat < fs.size then sumAsFloats a (i + 1) (acc + fs[i.toNat]!) else acc

def main (args : List String) : IO Unit := do
  let k := args.length.toUInt64
  let words : Array UInt64 := #[0x3FF0000000000000 + k, 0x4000000000000000, 0xBFF8000000000000,
    0x400921FB54442D18 + k]
  let s := sumAsFloats words 0 0.0
  IO.println s!"{s} {s.toBits}"
  -- Arrays of the same kinds elsewhere in the program.
  let fs : Array Float := #[1.5, 2.5 + k.toFloat]
  let us : Array UInt64 := #[7, 9 + k]
  IO.println s!"{fs.foldl (· + ·) 0.0} {us.foldl (· + ·) 0}"
