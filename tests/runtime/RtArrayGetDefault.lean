/-! Runtime test: `a[i]!` whose default holds the other reference to the
array it reads (review PAR-01). A read gives its reference to the array up
first, for a view; with the array shared only with the default, releasing
the default before the element was taken freed the block the view reads
(a crash, or a hang at exit). Three shapes: a tree's child or the tree
itself, a closure default that captures the array, a default record that
holds the array. -/

namespace DfltTree
-- "child i, or the tree itself when out of range": the default of get! is
-- the tree, which holds the children array being read
inductive Tree where
  | leaf : Nat → Tree
  | node : Array Tree → Tree

def Tree.val : Tree → Nat
  | .leaf k => k
  | .node cs => 1000000 + cs.size

@[noinline] def Tree.childOr (t : Tree) (i : Nat) : Tree :=
  match t with
  | .node cs => have : Inhabited Tree := ⟨t⟩; cs[i]!
  | _ => t

@[noinline] def mk (k : Nat) : Tree := .node #[.leaf k, .leaf (k + 1), .node #[.leaf 7]]

def run : IO Unit := do
  let mut acc := 0
  for r in [0:300] do
    let c := (mk r).childOr (r % 3)
    let junk := mk (r + 5000)
    acc := acc + c.val + junk.val % 2
  -- out of range: the tree itself (the panic message goes to stderr)
  let t := (mk 1).childOr 5
  IO.println s!"tree acc {acc} oob {t.val}"
end DfltTree

namespace DfltClo
-- get! on an array of closures whose default closure captures the array
@[noinline] def mk (n : Nat) : Array (Nat → Nat) := Id.run do
  let mut a := #[]
  for i in [0:n] do a := a.push (fun x => x + i * 1000)
  return a

@[noinline] def rd (a : Array (Nat → Nat)) (i : Nat) : Nat → Nat :=
  let _ : Inhabited (Nat → Nat) := ⟨fun x => x + a.size⟩
  a[i]!

@[noinline] def churn (n : Nat) : Array (Nat → Nat) := mk n

def run (n : Nat) : IO Unit := do
  let mut bad := 0
  for r in [0:200] do
    let f := rd (mk n) (r % n)
    let junk := churn 4
    let v := f r
    if v != r + (r % n) * 1000 then
      bad := bad + 1
      if bad < 5 then IO.println s!"bad at {r}: {v}"
    if junk.size != 4 then IO.println "?"
  IO.println s!"closures bad {bad} oob {rd (mk n) (n + 3) 10}"
end DfltClo

namespace DfltHold
inductive T where
  | leaf : Nat → T
  | node : Array T → T

instance : Inhabited T := ⟨.leaf 0⟩

@[noinline] def mk (n : Nat) : Array T := Id.run do
  let mut a := #[]
  for i in [0:n] do a := a.push (.leaf (i + 1000))
  return a

-- get! whose default holds the other reference to the array
@[noinline] def rd (a : Array T) (i : Nat) : T :=
  let _ : Inhabited T := ⟨.node a⟩
  a[i]!

def val : T → Nat
  | .leaf k => k
  | .node a => a.size

@[noinline] def churn (n : Nat) : List T := (List.range n).map fun i => .leaf (i + 5000)

def run (n : Nat) : IO Unit := do
  let mut total := 0
  let mut bad := 0
  for r in [0:2000] do
    let x := rd (mk n) (r % n)
    let junk := churn 8
    let v := val x
    if v != 1000 + r % n then bad := bad + 1
    total := total + v + junk.length
  IO.println s!"hold total {total} bad {bad} oob {val (rd (mk n) (2^64))}"
end DfltHold

def main (args : List String) : IO Unit := do
  let n := args.length + 4
  DfltTree.run
  DfltClo.run n
  DfltHold.run n
