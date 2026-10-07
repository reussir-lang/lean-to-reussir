/-! Runtime test: dropping a value deep through records only, along a
field that is not the last one freed, at an 8 MB stack (`RtDropGlue.pipe`):
a binary tree deep along its left child whose right children are fresh
nodes, and a rose tree in uniform code, whose list cells hold the deep tree
in their head and a fresh node in the tail. Native Lean frees iteratively.
Reussir's drop glue releases the last chain member being freed in a loop
(local patch 13-a) and pushes the other members being freed on a stack of
pending work (13-b), so it does not recurse either; with 13-a alone it
recursed once per level and overflowed. -/

inductive T2 | leaf | node (l : T2) (v : Nat) (r : T2)
inductive Rose (α : Type) | node (v : α) (kids : List (Rose α))
structure G where
  α : Type
  x : α

@[noinline] def leftDeep (n : Nat) : T2 := Id.run do
  let mut acc : T2 := .leaf
  for i in [0:n] do acc := .node acc i (.node .leaf i .leaf)
  return acc
@[noinline] def top : T2 → Nat | .leaf => 0 | .node _ v _ => v
@[noinline] def mkRoseAny {α : Type} (x : α) (n : Nat) : Rose α := Id.run do
  let mut acc : Rose α := .node x []
  for _ in [0:n] do acc := .node x [acc, .node x []]
  return acc
@[noinline] def roseU (g : G) (n : Nat) : Nat := match mkRoseAny g.x n with | .node _ ks => ks.length

def main : IO Unit := do
  IO.println s!"left spine {top (leftDeep 1000000)}"
  IO.println s!"rose {roseU ⟨Nat, 3⟩ 1000000}"
