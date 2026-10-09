/-! Runtime test (`programCasts`, axioms): a user axiom that states a `Bool`
equation, `true = false`. It proves `False`, and so `Array UInt64 = Array
Float`: `asFloats` reads an array of `UInt64` as an array of `Float`, as an
`unsafeCast` does. Natively both are arrays of 8-byte cells, and the
`Float` view reads the bits. Only the axioms that Lean adds for a proof by
native evaluation (`native_decide`, `bv_decide`: `nativeEvalStatement?`)
can let a program count as one that cannot cast; a user axiom never does,
whatever it states. Before, the compact arrays let every axiom that states
a `Bool` equation pass (`isBoolEqAxiom`), so this program kept `RVec<u64>`
and `RVec<f64>` arrays with no conversion between them, while the rest of
the lowering counted it as one that casts. `RtCastAxiomBoolEq.l2r-debug`:
the program casts, and no compact kind stays on. -/

axiom bad : true = false

theorem u64IsFloat : Array UInt64 = Array Float := absurd bad (by decide)

@[noinline] def asFloats (a : Array UInt64) : Array Float := cast u64IsFloat a

def main (args : List String) : IO Unit := do
  let k := args.length.toUInt64
  let words : Array UInt64 := #[0x3FF0000000000000 + k, 0x400921FB54442D18 + k, 0xC000000000000000 + k,
    0x7FF0000000000000 + k, 0x0000000000000001 + k]
  let fs := asFloats words
  IO.println s!"{fs.toList} {fs.foldl (· + ·) 0} {(fs.map (· * 2)).toList}"
