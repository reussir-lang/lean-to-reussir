/-! Runtime test (memory, review P1 of the shared drop stack): a deep value
whose free leaves one pending child per level, the pending children
alternating two release functions. `A` and `B` are mutually recursive with
two recursive fields each, so Reussir frees them through its stack of
pending drops. The chain alternates `A.node small rest` and
`B.node small rest`, where `small` is a node of the other type with its own
number (not a shared constant): freeing the chain defers `small` at every
level and goes on along `rest`, so `n` pairs leave `2 n` pending records.
A deferred record whose release function differs from the one deferred
before it is linked through its own header (the link keeps its release
function): here every one, the functions alternating, so the pending
records take no stack memory, as natively, where the to-do list is linked
through the freed objects. (A record with the same release function as the
one before is one 8-byte cell of a run.) Built
bottom-up in a loop; `consume` reads only the root, and its drop frees the
chain. At 500000 pairs (10^6 levels) the peak is about 45.7 MB, native's
55.1 MB (with a 24-byte entry of the stack per pending child, before the
linking: 88.6 MB). Argument: the number of pairs (default 1000). -/
mutual
inductive A where
  | leaf : A
  | small : Nat → A
  | node : B → B → A
inductive B where
  | leaf : B
  | small : Nat → B
  | node : A → A → B
end

@[noinline] def build (n : Nat) : A := Id.run do
  let mut acc : A := .leaf
  for k in [0:n] do
    acc := .node (.small k) (.node (.small (k + 1)) acc)
  return acc

@[noinline] def consume (a : A) : Nat :=
  match a with
  | .leaf => 0
  | .small _ => 2
  | .node _ _ => 1

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000
  let a := build n
  IO.println s!"root {consume a}"
  IO.println "done"
