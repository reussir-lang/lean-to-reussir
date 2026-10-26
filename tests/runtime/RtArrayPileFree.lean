/-! Runtime test (review RB-03 of the destructor port): the peak memory of
many arrays freed in one free. Each mode builds N one-element arrays
(`#[i]`, a small `Nat`) inside another structure, reads it, and frees it:
- `list`: a `List (Array Nat)` dropped by user code;
- `ref`: the same list in an `IO.Ref`, freed by `r.set []`
  (`lean_st_ref_set` frees the old value);
- `arr`: the same list as the one element of an array, replaced by
  `Array.set!`;
- `tree`: a balanced tree of N nodes, each holding one array, in an
  `IO.Ref`, freed by `r.set .leaf`;
- `treeu`: the same tree dropped by user code;
- `treeb`: a tree whose arrays each hold a counted value (`#[some i]`), in
  an `IO.Ref`, freed by `r.set .leaf`.
Natively `lean_dec`'s stack of objects to free is linked through the
objects and takes no memory of its own. In a free that the runtime starts
(`ref`, `arr`, `tree`), Reussir's glue releases the whole list or tree
within one pop of the runtime's stack of pending work, and each array it
reaches would wait there: one 24-byte step entry per array (`tree` at
N = 10^6: 111 MB against native's 69 MB). Now an array that holds
nothing counted (a small `Nat`) is freed at once, and another one (`treeb`)
waits as one pointer of a run (8 bytes).
Arguments: MODE N, MODE one of `list`, `ref`, `arr`, `tree`, `treeu`,
`treeb` (default: all six, N = 1000). The output is checked here; the
allocations and the peak memory by tests/runtime/alloc-check.sh
(RtArrayPileFree.alloc). -/

inductive AT where
  | leaf
  | node (l : AT) (a : Array Nat) (r : AT)

instance : Inhabited AT := ⟨.leaf⟩

/-- A tree whose arrays hold a counted value each. -/
inductive BT where
  | leaf
  | node (l : BT) (a : Array (Option Nat)) (r : BT)

instance : Inhabited BT := ⟨.leaf⟩

@[noinline] def mkList (n : Nat) : List (Array Nat) := Id.run do
  let mut acc := []
  for i in [0:n] do acc := #[i] :: acc
  return acc

partial def mkTree (lo hi : Nat) : AT :=
  if lo ≥ hi then .leaf
  else
    let mid := (lo + hi) / 2
    .node (mkTree lo mid) #[mid] (mkTree (mid + 1) hi)

partial def mkTreeB (lo hi : Nat) : BT :=
  if lo ≥ hi then .leaf
  else
    let mid := (lo + hi) / 2
    .node (mkTreeB lo mid) #[some mid] (mkTreeB (mid + 1) hi)

@[noinline] def sumHeads : List (Array Nat) → Nat → Nat
  | [], s => s
  | a :: t, s => sumHeads t (s + a[0]!)

@[noinline] def sumTree : AT → Nat
  | .leaf => 0
  | .node l a r => sumTree l + a[0]! + sumTree r

@[noinline] def sumTreeB : BT → Nat
  | .leaf => 0
  | .node l a r => sumTreeB l + (a[0]!).getD 0 + sumTreeB r

def run (mode : String) (n : Nat) : IO Unit := do
  match mode with
  | "list" => IO.println s!"list {n}: {sumHeads (mkList n) 0}"
  | "ref" =>
    let r ← IO.mkRef (mkList n)
    IO.println s!"ref {n}: {sumHeads (← r.get) 0}"
    r.set []
  | "arr" =>
    let a := #[mkList n]
    IO.println s!"arr {n}: {sumHeads a[0]! 0}"
    let a := a.set! 0 []
    IO.println s!"arr size {a.size}"
  | "tree" =>
    let r ← IO.mkRef (mkTree 0 n)
    IO.println s!"tree {n}: {sumTree (← r.get)}"
    r.set .leaf
  | "treeu" => IO.println s!"treeu {n}: {sumTree (mkTree 0 n)}"
  | "treeb" =>
    let r ← IO.mkRef (mkTreeB 0 n)
    IO.println s!"treeb {n}: {sumTreeB (← r.get)}"
    r.set .leaf
  | _ => throw (IO.userError s!"unknown mode {mode}")

def main (args : List String) : IO Unit := do
  let n := (args.getD 1 "1000").toNat!
  match args.head? with
  | some mode => run mode n
  | none => for mode in ["list", "ref", "arr", "tree", "treeu", "treeb"] do run mode n
