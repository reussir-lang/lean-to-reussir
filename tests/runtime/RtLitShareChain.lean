/-!
Array literals whose elements run inside the literal's closed term: `tr`'s
type `F` is not syntactically a function type, so `tr 1` is no closed term
of its own. Natively each literal is one closed term (Lean's
`searchArrayLiteral`), so `d1`'s and `d2`'s literals each run `tr 1`, and
stderr is `t1 t1 t2 t4`. lean2rr's polymorphic extern instances are renamed
(`Array.push._l2r.k`), which Lean's name-based literal search missed, so a
literal became a chain of one closed term per push, and `d1` and `d2` shared
the prefix `push (mkEmpty 2) (tr 1)`: `t1` once. Now the search matches the
instances through their Lean names (`ExtractClosedK.leanCall?`). A review of
the pass-parity branch (repro LitShare).
-/
def F := Nat → Nat
@[noinline] def tr : F := fun n => dbgTrace s!"t{n}" fun _ => n

@[noinline] def d1 (u : Nat) : Array Nat := #[tr 1, 2].push u
@[noinline] def d2 (u : Nat) : Array Nat := #[tr 1, 3].push u
@[noinline] def d3 (u : Nat) : Array (Array Nat) := #[#[tr 2], #[tr 2]].push #[u]
@[noinline] def d4 (u : Nat) : Array Nat := #[tr 4, u]

def main (args : List String) : IO Unit := do
  let n := args.length
  IO.println (d1 n)
  IO.println (d2 n)
  IO.println (d3 n)
  IO.println (d4 n)
  IO.println (d1 (n + 1))
