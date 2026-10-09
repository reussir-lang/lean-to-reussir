/-! Runtime test (`programCasts`, axioms of native evaluation and the
`@[csimp]` theorems that act on them, `nativeExempt`): the usual idiom
`theorem tableOk_eq : tableOk = true := by native_decide` has the shape of
a constant replacement, `@f = @g`, which `programCsimps` takes as a possible
`local` `@[csimp]` theorem (an attribute saved nowhere). It counted for the
axiom of its own proof, so the program counted as one that casts and no
compact kind stayed on. A candidate acts on no axiom that it comes after:
the axiom is its own (`tableOk_eq._native.native_decide.ax_1_1`), or its
proof uses the axiom. And once that axiom is exempt, the theorem's proof is
true. The equation lemma `tableAlias.eq_1 : tableAlias = table`, which
`simp [tableAlias]` adds, is a candidate whose `f` the evaluation of
`alias_ok`'s axiom (a `native_decide` over `tableAlias`) reaches; its
proof uses no axiom, so it cannot be false. `(tableOk && true) = true` has
no such shape. `RtCastNativeEqIdiom.l2r-debug`: the program does not cast,
and every compact kind stays on. -/

def table : Array UInt64 := #[1, 2, 4, 8, 16, 32, 64, 128]

def tableOk : Bool := table.size == 8

theorem tableOk_eq : tableOk = true := by native_decide

theorem tableOk_eq' : (tableOk && true) = true := by native_decide

theorem table_size : table.size = 8 := by
  have := tableOk_eq; simp [tableOk] at this; exact this

theorem table_size' : table.size = 8 := by
  have := tableOk_eq'; simp [tableOk] at this; exact this

def tableAlias : Array UInt64 := table

theorem alias_ok : (tableAlias.size == 8) = true := by native_decide

theorem alias_size : tableAlias.size = 8 := by simp [tableAlias, table_size]

@[noinline] def pick (i : Fin 8) : UInt64 := table[i.val]'(by rw [table_size]; exact i.isLt)

@[noinline] def pick' (i : Fin 8) : UInt64 := table[i.val]'(by rw [table_size']; exact i.isLt)

@[noinline] def pickAlias (i : Fin 8) : UInt64 :=
  tableAlias[i.val]'(by have h := alias_ok; simp at h; rw [h]; exact i.isLt)

def main (args : List String) : IO Unit := do
  let k := args.length
  let picked := (List.range 8).toArray.map fun l => pick ⟨(l + k) % 8, Nat.mod_lt _ (by decide)⟩
  let picked' := (List.range 8).toArray.map fun l => pick' ⟨(l + 3 * k) % 8, Nat.mod_lt _ (by decide)⟩
  let aliased := (List.range 8).toArray.map fun l => pickAlias ⟨(l + 5) % 8, Nat.mod_lt _ (by decide)⟩
  let fs : Array Float := picked.map fun p => p.toFloat * 0.5
  IO.println s!"{picked.toList} {picked'.toList} {aliased.toList} {fs.toList}"
