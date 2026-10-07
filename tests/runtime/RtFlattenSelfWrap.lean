/-! Runtime test: as `RtFlattenWrapArgs` for a self-call (review of
optimization `flatten-structs`, round 5, G2): a non-tail self-call whose
result the declaration keeps whole goes through the wrapper with whole
arguments, constrained as whole uses (not as passed to the split
parameter). -/
structure P where
  a : Nat
  b : Nat
  deriving Inhabited

-- takes its argument whole
@[noinline] def keepN (p : Nat × Nat) : Nat := (#[p, p]).size

-- reads walk's result field by field
@[noinline] def sumW (n : Nat) : Nat := (walk ⟨n, 1⟩ n).1
where
  walk (s : P) : Nat → Nat × Nat
    | 0 => (s.a, s.b)
    | n+1 =>
      let r := walk s n
      let q := if n % 2 == 0 then r else (n, n)
      (keepN q + keepN r + r.1, r.2)

def main (args : List String) : IO Unit := do
  match args with
  | [k] =>
    let n := k.toNat!
    let mut t := 0
    for i in [0:n] do
      t := t + sumW (i % 5 + 2)
    IO.println s!"{t}"
  | _ =>
    IO.println s!"sumW {sumW 4}"
