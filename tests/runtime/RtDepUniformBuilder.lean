/-! Runtime test: a generic recursive builder used at a type too large for
one copy per type argument (blowup audit BA-18, the data case; branch
fix-proof-builder's RtUniformBuilder). `Big` has more than 256 nodes, so
the builder runs in code over an unknown element type, while its caller
holds the result at `WL Big`. Natively each builder is O(N). A
translation that converts the list built so far between the two
representations at each level is quadratic (8014042 allocations for 4000
elements). Also a mutual pair and a tail-recursive builder in the same
situation. The output is checked here; the allocations by
tests/runtime/alloc-check.sh (RtDepUniformBuilder.alloc). Argument: N
(default 2000). -/

structure W8 (a b c d e f g h : Type) where
  x : Nat

abbrev T10 := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat

abbrev Big := W8 T10 T10 T10 T10 T10 T10 T10 T10

structure Wrap (α : Type) where
  val : α
  tag : Nat

inductive WL (α : Type) where
  | nil
  | cons (w : Wrap α) (r : WL α)

@[noinline] def sumTags {α : Type} : WL α → Nat
  | .nil => 0
  | .cons w ws => w.tag + sumTags ws

@[noinline] def sumVals : WL Big → Nat
  | .nil => 0
  | .cons w ws => w.val.x + sumVals ws

def mkWL {α : Type} (f : Nat → Wrap α) : Nat → WL α
  | 0 => .nil
  | k + 1 => .cons (f k) (mkWL f k)

mutual
def mkA {α : Type} (f : Nat → Wrap α) : Nat → WL α
  | 0 => .nil
  | k + 1 => .cons (f k) (mkB f k)
def mkB {α : Type} (f : Nat → Wrap α) : Nat → WL α
  | 0 => .nil
  | k + 1 => .cons (f (k + 1)) (mkA f k)
end

def mkT {α : Type} (f : Nat → Wrap α) (acc : WL α) : Nat → WL α
  | 0 => acc
  | k + 1 => mkT f (.cons (f k) acc) k

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 2000
  let xs : WL Big := mkWL (fun i => ⟨⟨2 * i⟩, i⟩) n
  IO.println s!"mkWL {sumTags xs} {sumVals xs}"
  let ms : WL Big := mkA (fun i => ⟨⟨i + 1⟩, i⟩) n
  IO.println s!"mutual {sumTags ms} {sumVals ms}"
  let ts : WL Big := mkT (fun i => ⟨⟨i⟩, i⟩) .nil n
  IO.println s!"tail {sumTags ts} {sumVals ts}"
