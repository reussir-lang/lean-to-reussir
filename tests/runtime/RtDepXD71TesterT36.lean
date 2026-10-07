/-! Runtime test: case `D71TesterT36` of the shared dependent-type corpus
(programs built by another translator's team and checked against native
Lean). It checks: A million-long chain of records holding Box values
(alternating Nat and String): drop must not overflow the stack Small size
(10). -/
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
  next : Option AnyS
@[noinline] def nest : Nat → Nat → AnyS → AnyS
  | 0, _, s => s
  | k+1, i, s => nest k (i + 1) (if i % 2 == 0 then ⟨(i : Nat), some s⟩ else ⟨s!"s{i}", some s⟩)
@[noinline] def top (s : AnyS) : String := s.inst.toString s.val
@[noinline] partial def len (s : AnyS) (c : Nat) : Nat :=
  match s.next with
  | some t => len t (c + 1)
  | none => c
def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000000
  let s := nest n 0 ⟨(0 : Nat), none⟩
  IO.println s!"{top s} {len s 1}"
