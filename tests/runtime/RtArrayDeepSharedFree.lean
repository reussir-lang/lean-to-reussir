/-! Runtime test (review of the runtime's speed items): deeply nested arrays
of boxes, 10^6 levels (`RtArrayDeepSharedFree.args`), with shared and unique
siblings at each level, freed outside a free (a reference set) on a 256 KiB
stack (`LEAN_STACK_SIZE_KB=256`, `RtArrayDeepSharedFree.pipe`): each nested
array is pushed on the pending stack, and the first pass of an array's free
(native's decrement of every element in index order, `drop::free_vec`) is a
loop, so the free uses no stack per level. Then a chain built twice that
shares its tail, both copies in one array, freed the same way. -/

inductive T where
  | leaf (n : Nat)
  | node (xs : Array T)

@[noinline] def build (d : Nat) (shared : T) : T := Id.run do
  let mut t := T.leaf 0
  for i in [0:d] do
    t := if i % 2 == 0 then T.node #[T.leaf i, t, shared, T.leaf (i + 1)]
         else T.node #[shared, T.leaf i, t]
  t

@[noinline] def depth : T → Nat
  | .leaf _ => 0
  | .node xs => xs.foldl (fun m x => max m (depth x)) 0 + 1

def main (args : List String) : IO Unit := do
  let d := args.head!.toNat!
  let shared := T.node #[T.leaf 7]
  let r ← IO.mkRef (T.leaf 0)
  r.set (build d shared)
  match ← r.get with
  | .node xs => IO.println s!"top {xs.size}"
  | .leaf _ => IO.println "leaf"
  r.set (T.leaf 1)
  IO.println s!"freed; shared {depth shared}"
  -- the same chain built twice sharing its tail, both freed
  let t := build (d / 2) shared
  let a := T.node #[t, t, shared]
  r.set a
  r.set (T.leaf 2)
  IO.println "done"
