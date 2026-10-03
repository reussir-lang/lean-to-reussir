/-! Runtime test: `Array.map` whose function projects a field of a
parametric structure (round 7 RV7D-01). Inside Lean's `map` loop the
element is read from the uniform `Array NonScalar` (`Array lcAny`), so its
type is `lcAny`, and Stage 3 must leave the fields of a `cases` on it
`lcAny` too. Taking the constructor's parameter types for the fields gave
`Prod.mk (fst : ◾)` and `R.mk (s : String) (y : String)` (`y` holds a
`Nat`); `split-map-loops` then took that type for the result's elements:
an `Array ◾` read back as zeros (`#[0, 0]` for `#[5, 7]`), or an
`Array String` holding `Nat`s ("INTERNAL PANIC: unreachable code has been
reached"). Each map below is used at one site, and some at two (the shared
function value of `twoSites`). -/

structure Pair (α β : Type) where
  a : α
  b : β

structure R (α : Type) where
  s : String
  y : α

@[noinline] def pairs (k : Nat) : Array (Nat × Nat) := #[(k, k + 1), (k + 2, k + 3)]
@[noinline] def mkP (k : Nat) : Array (Pair Nat String) := #[⟨k, "x"⟩, ⟨k + 1, "y"⟩]
@[noinline] def mkT (k : Nat) : Array (Nat × Nat × Nat) := #[(k, k + 1, k + 2)]
@[noinline] def mkS (k : Nat) : Array (Σ _ : Nat, Nat) := #[⟨k, k + 1⟩]
@[noinline] def rs (k : Nat) : Array (R Nat) := #[⟨"a", k⟩, ⟨"bb", k + 1⟩]
@[noinline] def flts (k : Nat) : Array (Float × String) := #[(k.toFloat, "f"), (2.5, "g")]
@[noinline] def chars (k : Nat) : Array (UInt8 × Char) := #[(k.toUInt8, 'a'), (2, 'é')]
@[noinline] def rows (n : Nat) : Array (Array (Nat × String)) :=
  (Array.range n).map fun i => #[(i, s!"r{i}"), (i + 1, "x")]

def twoSites : IO Unit := do
  let f := fun (r : Array (Nat × String)) => r.map (·.1)
  IO.println s!"two sites {(rows 3).map f} {(rows 2).map f}"

def main : IO Unit := do
  IO.println s!"Prod {(pairs 5).map (·.1)} {(pairs 5).map (·.2)} {(pairs 5).map Prod.fst}"
  IO.println s!"Pair {(mkP 3).map (·.a)} {(mkP 3).map Pair.b}"
  IO.println s!"triple {(mkT 3).map (·.2.1)} {(mkT 3).map (·.2)}"
  IO.println s!"sigma {(mkS 3).map (·.2)} {(mkS 3).map (·.1)}"
  IO.println s!"R {(rs 3).map (·.y)} {(rs 3).map (·.s)} {((rs 3).map (fun r => r.y)).foldl (· + ·) 0}"
  IO.println s!"Float {(flts 3).map (·.1)} {(flts 3).map (·.2)}"
  IO.println s!"Char {(chars 1).map (·.1)} {(chars 1).map (·.2)}"
  let xs := #[1, 2, 3]
  let ys := #["a", "b", "c"]
  IO.println s!"zip {(xs.zip ys).map (·.2)} {(xs.zip ys).map (·.1)}"
  IO.println s!"zipIdx {ys.zipIdx.map (·.2)} {ys.zipIdx.map (·.1)}"
  IO.println s!"mapM {Id.run ((pairs 1).mapM fun p => pure p.1)}"
  twoSites
