/-! Runtime test: memory of long lists whose elements native Lean stores
in three ways (review of the dependent-type design, probe mem): `List
Float` (natively each element is a separate boxed `Float`), `List Nat` of
`i + 1` and `List.range` (small `Nat`s, no allocation for an element).
Arguments: MODE N, MODE `f`, `n` or `r` (default: all three, N = 1000).
The output is checked here; the allocations and the peak memory by
tests/runtime/alloc-check.sh (RtDepListMem.alloc), which runs each mode at
two sizes. -/
@[noinline] def mkF (n : Nat) : List Float := (List.range n).map fun i => i.toFloat
@[noinline] def mkN (n : Nat) : List Nat := (List.range n).map fun i => i + 1
@[noinline] def mkR (n : Nat) : List Nat := List.range n

def main (args : List String) : IO Unit := do
  let n := (args.getD 1 "1000").toNat!
  match args.head? with
  | some "f" => IO.println s!"f {(mkF n).length} {(mkF n).foldl (· + ·) 0}"
  | some "n" => IO.println s!"n {(mkN n).length} {(mkN n).foldl (· + ·) 0}"
  | some "r" => IO.println s!"r {(mkR n).length} {(mkR n).foldl (· + ·) 0}"
  | _ =>
    IO.println s!"f {(mkF n).length} {(mkF n).foldl (· + ·) 0}"
    IO.println s!"n {(mkN n).length} {(mkN n).foldl (· + ·) 0}"
    IO.println s!"r {(mkR n).length} {(mkR n).foldl (· + ·) 0}"
