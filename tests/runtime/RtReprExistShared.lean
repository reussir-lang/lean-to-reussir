/-! Runtime test: one typed list packed into n existentials that all stay
alive (blowup audit BA-08). Natively the n packages share the list: O(n)
memory for n packages of a list of n. Through lean2rr each package holds
its own copy of the list in the uniform layout (one conversion per
package): n x n cells (16004000 at n = 4000, 634 MB). The conversion is
the representation change itself, so a memo per conversion does not help;
only keeping the list in the uniform layout from its creation would. The
output is checked here; the allocations and the peak memory by
tests/runtime/alloc-check.sh (RtReprExistShared.alloc). -/
structure Packed where
  α : Type
  xs : List α
  f : α → Nat

@[noinline] def Packed.headVal (p : Packed) : Nat :=
  match p.xs with
  | [] => 0
  | x :: _ => p.f x

def main (args : List String) : IO Unit := do
  let n := (args.headD "300").toNat!
  let big : List Nat := List.range n
  let ps : List Packed := (List.range n).map fun i => ⟨Nat, big, (· + i)⟩
  let s := ps.foldl (fun acc p => acc + p.headVal) 0
  IO.println s!"{s} {ps.length}"
