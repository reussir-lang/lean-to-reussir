/-! Runtime test: polymorphic recursion at a doubling type (blowup audit,
probe NestPair, checked and not a problem): `nest` calls itself at
`α × α`, so its value doubles in size at each level but shares its two
halves (n + 1 cells natively, a list of 1000 at the bottom). The recursive
calls go to the uniform instance; its pairs are built there, so nothing is
converted level by level: the allocations grow with n as native's do,
not with 2^n or with the list's length per level. The output is checked
here; the allocations by tests/runtime/alloc-check.sh
(RtReprNestPair.alloc). -/
@[noinline] def leftDepthOf {α : Type} (d : α → Nat) (x : α) : Nat := d x

def nest {α : Type} (d : α → Nat) : Nat → α → Nat
  | 0, x => leftDepthOf d x
  | n + 1, x => nest (fun p : α × α => 1 + d p.1) n (x, x)

def main (args : List String) : IO Unit := do
  let n := (args.headD "10").toNat!
  let big := List.range 1000
  IO.println (nest (fun (l : List Nat) => l.length) n big)
