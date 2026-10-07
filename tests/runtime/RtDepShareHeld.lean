/-! Runtime test: values without shared parts, packed in existentials while
the program still holds them and as their last use, and read back at
their own type with `unsafeCast` (the package holds that type's value, so
natively the cast is the same object): a complete binary tree of 2^d
leaves, a list of 2^d elements and an array of 2^(d-3) small trees
(branch fix-conv-sharing's RtConvShareHeld). Native Lean allocates
nothing to pack or read them; the sums are checked here, and that the
allocations grow with 2^d as native's do (one value built, none copied
per use) by tests/runtime/alloc-check.sh (RtDepShareHeld.alloc).
Argument: D (default 18). -/

inductive Tree (α : Type) where
  | leaf (x : α)
  | node (left right : Tree α)

@[noinline] def full : Nat → Nat → Tree Nat
  | 0, i => .leaf i
  | d + 1, i => .node (full d (2 * i)) (full d (2 * i + 1))

structure PTree where
  α : Type
  t : Tree α

@[noinline] unsafe def sumTree (p : PTree) : Nat := go (unsafeCast p.t : Tree Nat) 0
where
  go : Tree Nat → Nat → Nat
    | .leaf x, a => a + x
    | .node l r, a => go r (go l a)

structure PList where
  α : Type
  l : List α

@[noinline] unsafe def sumList (p : PList) : Nat := (unsafeCast p.l : List Nat).foldl (· + ·) 0

structure PArr where
  α : Type
  a : Array (Tree α)

@[noinline] unsafe def sumArr (p : PArr) : Nat :=
  (unsafeCast p.a : Array (Tree Nat)).foldl (fun s t => sumTree.go t s) 0

unsafe def main (args : List String) : IO Unit := do
  let d := (args.headD "18").toNat!
  let t := full d 0
  IO.println s!"tree held {sumTree ⟨Nat, t⟩}"
  IO.println s!"tree again {sumTree.go t 0}"
  IO.println s!"tree consumed {sumTree ⟨Nat, full d 1⟩}"
  let l := List.range (2 ^ d)
  IO.println s!"list held {sumList ⟨Nat, l⟩}, length {l.length}"
  IO.println s!"list consumed {sumList ⟨Nat, List.range (2 ^ d + 1)⟩}"
  let a := (List.range (2 ^ (d - 3))).toArray.map (full 3)
  IO.println s!"array held {sumArr ⟨Nat, a⟩}, size {a.size}"
