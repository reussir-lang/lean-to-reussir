/-! Runtime test (`programCasts`, axioms of native evaluation): a `@[csimp]`
theorem of the program, proved by `sorry`, replaces `f` (whose definition
gives `false`) by `g` (`true`) in compiled code. `native_decide` compiles
`f = true` with the replacement, sees `true`, and adds a false axiom, which
proves `False`, and so `Array UInt64 = Array Float`. `asFloats` reads an
array of `UInt64` as an array of `Float`; natively the `Float` view reads
the bits of the 8-byte cells. The evaluation's walk (`nativeEvalWalk`)
meets `f`, which `f_eq` replaces, and `f_eq`'s proof can be false (it uses
`sorry`, `proofAxioms`): the axiom counts as a cast (`nativeExempt`; the
walk of `programCasts` does not reach `f_eq` and its `sorry`).
`RtCastNativeCsimp.l2r-debug`: the program casts, and no compact kind stays
on. -/

def f : Bool := false

def g : Bool := true

@[csimp] theorem f_eq : @f = @g := sorry

theorem fTrue : f = true := by native_decide

theorem u64IsFloat : Array UInt64 = Array Float := absurd fTrue (by decide)

@[noinline] def asFloats (a : Array UInt64) : Array Float := cast u64IsFloat a

def main (args : List String) : IO Unit := do
  let k := args.length.toUInt64
  let words : Array UInt64 := #[0x3FF0000000000000 + k, 0x400921FB54442D18 + k, 0xC000000000000000 + k,
    0x7FF0000000000000 + k, 0x0000000000000001 + k]
  let fs := asFloats words
  IO.println s!"{fs.toList} {fs.foldl (· + ·) 0} {(fs.map (· * 2)).toList}"
