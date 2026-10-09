import CastNativeLibShapeDep

/-! Runtime test (`programCasts`, axioms of native evaluation and the
`@[csimp]` theorems that act on them, `nativeExempt`): the companion module
`CastNativeLibShapeDep` has a theorem `@List.length = @myLength` without the
`@[csimp]` attribute, a candidate that replaces a library constant, which
could act on any axiom of native evaluation. Its proof uses only Lean's
standard axioms, so it is true and acts on nothing: `myLength` computes
what `List.length` computes. It made every axiom of native evaluation count,
the program counted as one that casts, and no compact kind stayed on.
`RtCastNativeLibShape.l2r-debug`: the program does not cast, and every
compact kind stays on. -/

def table : Array UInt64 := #[1, 2, 4, 8, 16, 32, 64, 128]

theorem table_size : table.size = 8 := by native_decide

@[noinline] def pick (i : Fin 8) : UInt64 := table[i.val]'(by rw [table_size]; exact i.isLt)

def main (args : List String) : IO Unit := do
  let k := args.length
  let picked := (List.range 8).toArray.map fun l => pick ⟨(l + k) % 8, Nat.mod_lt _ (by decide)⟩
  let fs : Array Float := picked.map fun p => p.toFloat * 0.5
  IO.println s!"{picked.toList} {fs.toList} {myLength [1, 2, 3]}"
