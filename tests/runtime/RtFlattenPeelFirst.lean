/-! Runtime test: optimization `flatten-structs` and a peeled loop's first
step (review of the pass, round 4, F2). `outer` is peeled: its wrapper runs
the first step on the caller's record, which it gives to `inner`; with
k = 0, `inner` returns it at once. A peeled loop's parameters count as
existing objects (`allowedWhole`), so `inner`'s result stays whole there
and the caller's record is stored, not a copy (natively `first=true`,
`atonce=true`; `RtFlattenPeelFirst.alloc`). -/
structure P where
  a : Nat
  b : Nat
  deriving Inhabited

-- every step builds a new P; with k = 0 it returns p itself
@[noinline] def inner (p : P) : Nat → P
  | 0 => p
  | k+1 => inner ⟨p.a + 1, p.b⟩ k

-- reads inner's result field by field
@[noinline] def innerA (k : Nat) : Nat := (inner ⟨k, k⟩ k).a

-- peeled: s is stored at the exit, every step builds a new P
@[noinline] def outer (s : P) (k : Nat) : Nat → Array P → Array P
  | 0, acc => acc.push s
  | n+1, acc =>
    let t := inner s k
    outer ⟨t.a, t.b + 1⟩ k n (acc.push t)

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [k] =>
    let n := k.toNat!
    let b0 : P := ⟨n, 1⟩
    let mut tot := 0
    for _ in [0:n] do
      tot := tot + (outer b0 0 1 #[]).size
    IO.println s!"{tot} {innerA 3}"
  | _ =>
    let b0 : P := ⟨7, 1⟩
    let acc := outer b0 0 1 #[]
    let acc0 := outer b0 0 0 #[]
    IO.println s!"{acc[0]!.a} {acc[1]!.b} {innerA 2} first={ptrAddrUnsafe acc[0]! == ptrAddrUnsafe b0} atonce={ptrAddrUnsafe acc0[0]! == ptrAddrUnsafe b0}"
