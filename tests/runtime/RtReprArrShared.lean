/-! Runtime test: an array whose n elements are one array (blowup audit
BA-06). `Array.replicate n row` holds the same row of n numbers n times;
packed once in an existential whose field is `Array (Array α)`, it is
converted to the uniform layout. Natively the package holds the same
object (O(n) memory); a conversion that converts the row once per element
copies n x n numbers (16004000 elements at n = 4000). The output is
checked here; the allocations by tests/runtime/alloc-check.sh
(RtReprArrShared.alloc). -/
structure Grid where
  α : Type
  rows : Array (Array α)
  f : α → Nat

@[noinline] def Grid.corner (g : Grid) : Nat :=
  match g.rows[0]? with
  | some r => match r[0]? with
    | some x => g.f x + g.rows.size
    | none => 0
  | none => 0

def main (args : List String) : IO Unit := do
  let n := (args.headD "1000").toNat!
  let row : Array Nat := Array.range n
  let rows : Array (Array Nat) := Array.replicate n row
  IO.println (Grid.corner ⟨Nat, rows, id⟩)
