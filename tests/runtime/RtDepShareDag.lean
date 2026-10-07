/-! Runtime test: a shared tree stays shared when it goes through code that
does not know its element type (blowup audit BA-01; the DagTree programs of
the design site and of the DAG blowup report; branch fix-conv-sharing's
RtConvShareDag without its address checks). `build n` makes a tree whose
every node points twice to one child: n + 1 objects and 2^n paths. The tree
goes into an existential package (`Packed`, its element type a field) and
is read there by code over an unknown type; it is also built by that code
(`grow`, from a seed in a package) and read back at `Tree Nat` with
`unsafeCast` (the package holds a `Tree Nat`: the same object). Each read
walks one path (the left or the right spine), so native Lean does O(n)
work and holds n + 1 nodes at any n. A translation that rebuilds the tree
when it changes its representation builds every path: 2^(n+1) cells (about
1 GB at n = 24). The output (depths and leaves) is checked here; the
allocations and the peak memory at n = 12 and n = 18 by
tests/runtime/alloc-check.sh (RtDepShareDag.alloc). Argument: N (default 16). -/

inductive Tree (α : Type) where
  | leaf (x : α)
  | node (left right : Tree α)

@[noinline] def build : Nat → Tree Nat
  | 0 => .leaf 7
  | n + 1 => let t := build n; .node t t

structure Packed where
  α : Type
  tree : Tree α

@[noinline] def leftDepth (p : Packed) : Nat := go p.tree
where
  go {α : Type} : Tree α → Nat
    | .leaf _ => 0
    | .node l _ => 1 + go l

@[noinline] def rightDepth (p : Packed) : Nat := go p.tree
where
  go {α : Type} : Tree α → Nat
    | .leaf _ => 0
    | .node _ r => 1 + go r

/-- Built where the element type is a field: the same sharing. -/
@[noinline] def buildG {α : Type} (x : α) : Nat → Tree α
  | 0 => .leaf x
  | n + 1 => let t := buildG x n; .node t t

structure Seed where
  α : Type
  x : α

@[noinline] def Seed.grow (s : Seed) (n : Nat) : Packed := ⟨s.α, buildG s.x n⟩

/-- Read back at `Tree Nat`: the package holds a `Tree Nat`. -/
@[noinline] unsafe def back (p : Packed) : Tree Nat := unsafeCast p.tree

/-- The depth of the left spine and the leaf at its end. -/
def leftLeaf : Tree Nat → Nat → Nat × Nat
  | .leaf x, d => (d, x)
  | .node l _, d => leftLeaf l (d + 1)

/-- The same along the right spine. -/
def rightLeaf : Tree Nat → Nat → Nat × Nat
  | .leaf x, d => (d, x)
  | .node _ r, d => rightLeaf r (d + 1)

unsafe def main (args : List String) : IO Unit := do
  let n := (args.headD "16").toNat!
  -- The program of the design site: the tree is consumed by the package.
  IO.println s!"left depth {leftDepth ⟨Nat, build n⟩}"
  IO.println s!"right depth {rightDepth ⟨Nat, build n⟩}"
  -- The program still holds the tree.
  let t := build n
  let p : Packed := ⟨Nat, t⟩
  IO.println s!"held: {leftDepth p} {rightDepth p} {leftLeaf t 0} {rightLeaf t 0}"
  IO.println s!"round trip: {leftLeaf (back p) 0} {rightLeaf (back p) 0}"
  -- Built by code over an unknown type, read at `Tree Nat`.
  let g := Seed.grow ⟨Nat, 5⟩ n
  IO.println s!"grown: {leftDepth g} {rightDepth g} {leftLeaf (back g) 0} {rightLeaf (back g) 1}"
  let gs := Seed.grow ⟨String, "s"⟩ (n + 1)
  IO.println s!"grown at String: {leftDepth gs} {rightDepth gs}"
