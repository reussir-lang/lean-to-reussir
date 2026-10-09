/-! Runtime test (`programCasts`, axioms of native evaluation): `native_decide`
proves `lie = true` because the compiled code of `lie` is its
`implemented_by` target, `lieImpl`, which gives `true`; the definition
gives `false`. The axiom that `native_decide` adds is then false, proves
`False`, and so `Array UInt64 = Array Float` (Lean's `implemented_by` doc:
a wrong implementation lets `native_decide` prove `False`). `asFloats`
reads an array of `UInt64` as an array of `Float`; natively the `Float`
view reads the bits of the 8-byte cells. Such an axiom counts as a cast
when the evaluation of its statement may have run other code than the
definitions: an `implemented_by` target or an extern of the program on its
way, or a `@[csimp]` theorem that can be false (`nativeExempt`).
`RtCastNativeImplBy.l2r-debug`: the program casts, and no compact kind
stays on. -/

def lieImpl : Bool := true

@[implemented_by lieImpl] def lie : Bool := false

theorem lieTrue : lie = true := by native_decide

theorem u64IsFloat : Array UInt64 = Array Float := absurd lieTrue (by decide)

@[noinline] def asFloats (a : Array UInt64) : Array Float := cast u64IsFloat a

def main (args : List String) : IO Unit := do
  let k := args.length.toUInt64
  let words : Array UInt64 := #[0x3FF0000000000000 + k, 0x400921FB54442D18 + k, 0xC000000000000000 + k,
    0x7FF0000000000000 + k, 0x0000000000000001 + k]
  let fs := asFloats words
  IO.println s!"{fs.toList} {fs.foldl (· + ·) 0} {(fs.map (· * 2)).toList} {lie}"
