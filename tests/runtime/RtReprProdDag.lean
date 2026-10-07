/-! Runtime test: a shared tree reached through a pair (blowup audit BA-03).
Each node holds its two children in a `Prod` (`T α × T α`, a nested
inductive through `Prod`), both the same subtree: `build n` has n + 1
distinct nodes and 2^(n+1) - 1 paths. Packing it once in an existential
(`Packed`: the element type is a field, so `leftDepth.go` is the uniform
instance) converts it from the layout with `Nat` leaves to the uniform one.
A conversion that follows every path builds 2^(n+1) - 1 cells (6291452 at
n = 20; natively nothing is converted). The output is checked here; that
the allocations grow as native's do is checked by
tests/runtime/alloc-check.sh (RtReprProdDag.alloc). -/
inductive T (α : Type) where
  | leaf (x : α)
  | pair (p : T α × T α)

@[noinline] def build : Nat → T Nat
  | 0 => .leaf 7
  | n + 1 => let c := build n; .pair (c, c)

structure Packed where
  α : Type
  t : T α

@[noinline] def leftDepth (p : Packed) : Nat := go p.t
where
  go {α : Type} : T α → Nat
    | .leaf _ => 0
    | .pair (l, _) => 1 + go l

def main (args : List String) : IO Unit := do
  let n := (args.headD "16").toNat!
  IO.println (leftDepth ⟨Nat, build n⟩)
