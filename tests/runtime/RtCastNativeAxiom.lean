import Std.Tactic.BVDecide

/-! Runtime test (`programCasts`, axioms of native evaluation): code whose
proofs use the axioms that `bv_decide` and `native_decide` add (each
`e = true`, for a closed `Bool` term `e` that Lean compiled, ran and saw
`true`; `nativeEvalStatement?`). The walk of `programCasts` reaches them
(the values of `low3`, `pick` and `sized` mention the theorems). The code
that ran for each statement is the code of its definitions (no
`implemented_by`, extern or `@[csimp]` theorem that can be false on its
way: `nativeExempt`), so each axiom is true of the definitions, proves
no equation between two types, and the program does not cast: every
compact kind stays on, and `unread-fields` runs
(`RtCastNativeAxiom.l2r-debug`). Before, the compact arrays let these
axioms pass (and every other axiom that states a `Bool` equation), but the
rest of the lowering and `unread-fields` counted the program as one that
casts (lean-zip's `bv_decide` axioms kept `unread-fields` off). -/

theorem and7_lt (x : UInt64) : x &&& 7 < 8 := by bv_decide

def table : Array UInt64 := #[1, 2, 4, 8, 16, 32, 64, 128]

theorem table_size : table.size = 8 := by native_decide

theorem fives : (List.range 10).foldl (· + ·) 0 = 45 := by native_decide

/-- The low three bits, with a proof by `bv_decide`. -/
@[noinline] def low3 (x : UInt64) : {y : UInt64 // y < 8} := ⟨x &&& 7, and7_lt x⟩

/-- An entry of `table`, its index bound proved through `native_decide`. -/
@[noinline] def pick (i : Fin 8) : UInt64 := table[i.val]'(by rw [table_size]; exact i.isLt)

@[noinline] def sized (n : Nat) : {m : Nat // m = 45 + n} :=
  ⟨(List.range 10).foldl (· + ·) 0 + n, by rw [fives]⟩

def main (args : List String) : IO Unit := do
  let k := args.length.toUInt64
  let xs : Array UInt64 := #[13 + k, 22, 7, 1000 + k, 0xFFFFFFFFFFFFFFFF]
  let lows := xs.map fun x => (low3 x).val
  let picked := lows.map fun l => pick ⟨l.toNat % 8, Nat.mod_lt _ (by decide)⟩
  let fs : Array Float := picked.map fun p => p.toFloat * 0.5
  let bytes : Array UInt8 := picked.map (·.toUInt8)
  IO.println s!"{lows.toList} {picked.toList} {fs.toList} {bytes.toList} {(sized k.toNat).val}"
