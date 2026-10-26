/-! Runtime test (hunt HMEM-01 of leanrt's memory core): the peak memory
of a long list dropped whole. When the hunt found it, lean2rr's Reussir
patches had Reussir's glue push every boxed head on one pending stack
while it walked the list, one 24-byte entry each (n = 4M pairs: 391 MB
against native's 258 MB; a list of function values, HRT2-02: n = 10^6,
89 MB against native's 70 MB). Now a list that user code drops pushes
nothing: Reussir's glue releases each boxed head as a free of its own,
and a leaf head (a structure of scalars) is freed at once.
Two more modes (tests for the destructor port) build the list of pairs,
read its first element and have the runtime free it: `ref` puts it in an
`IO.Ref` and sets the reference to `[]` (`lean_st_ref_set` frees the old
value); `arr` puts it in a one-element array whose element `clearFirst`
(not inlined) replaces with `[]` (`Array.set!` frees the old element).
Natively both frees go through `lean_dec`, whose stack of objects to free
is linked through the objects themselves (no memory of its own). The free
in the runtime pushes every head on the runtime's stack of pending work:
the heads have one release function, so they share one entry, and the
stack keeps one pointer (8 bytes) per head (it never writes a cell).
Arguments: MODE N, MODE one of `pairs`, `leaf`, `opt`, `lists`, `strs`,
`fns`, `ref`, `arr` (default: all eight, N = 1000). Each of the first six
modes builds a list of N elements, reads its first element and drops the
list whole. The output is checked here;
the allocations and the peak memory by tests/runtime/alloc-check.sh
(RtListDropWhole.alloc), which runs each mode at two sizes. -/

structure P where
  a : UInt64
  b : UInt64

structure S where
  s : String
  k : Nat

@[noinline] def pairs (n : Nat) : List (Nat × Nat) := (List.range n).map fun i => (i, i + 1)
@[noinline] def leaves (n : Nat) : List P := (List.range n).map fun i => { a := i.toUInt64, b := i.toUInt64 + 1 }
@[noinline] def opts (n : Nat) : List (Option Nat) := (List.range n).map fun i => some (i + 2)
@[noinline] def lists (n : Nat) : List (List Nat) := (List.range n).map fun i => [i, i + 1]
@[noinline] def strs (n : Nat) : List S := (List.range n).map fun i => { s := "s", k := i }
@[noinline] def fns (n : Nat) : List (Nat → Nat) := (List.range n).map fun i => fun x => x + i

@[noinline] def firstPair : List (Nat × Nat) → Nat
  | (a, b) :: _ => a + b
  | [] => 0

@[noinline] def firstLeaf : List P → UInt64
  | p :: _ => p.a + p.b
  | [] => 0

@[noinline] def firstOpt : List (Option Nat) → Nat
  | some a :: _ => a
  | _ => 0

@[noinline] def firstList : List (List Nat) → Nat
  | l :: _ => l.length
  | [] => 0

@[noinline] def firstStr : List S → Nat
  | s :: _ => s.s.length + s.k
  | [] => 0

@[noinline] def firstFn : List (Nat → Nat) → Nat
  | f :: _ => f 1
  | [] => 0

@[noinline] def clearFirst (a : Array (List (Nat × Nat))) : Array (List (Nat × Nat)) := a.set! 0 []

/-- The list of pairs in an `IO.Ref`, freed by `r.set []`. -/
@[noinline] def viaRef (n : Nat) : IO Nat := do
  let l := pairs n
  let v := firstPair l
  let r ← IO.mkRef l
  r.set []
  pure v

/-- The list of pairs as an array's element, freed by `Array.set!`. -/
@[noinline] def viaArr (n : Nat) : Nat :=
  let l := pairs n
  let v := firstPair l
  v + (clearFirst #[l]).size

def run (mode : String) (n : Nat) : IO Unit := do
  let r ← match mode with
    | "pairs" => pure (firstPair (pairs n))
    | "leaf" => pure (firstLeaf (leaves n)).toNat
    | "opt" => pure (firstOpt (opts n))
    | "lists" => pure (firstList (lists n))
    | "strs" => pure (firstStr (strs n))
    | "fns" => pure (firstFn (fns n))
    | "ref" => viaRef n
    | "arr" => pure (viaArr n)
    | _ => throw (IO.userError s!"unknown mode {mode}")
  IO.println s!"{mode} {n}: {r}"

def main (args : List String) : IO Unit := do
  let n := (args.getD 1 "1000").toNat!
  match args.head? with
  | some mode => run mode n
  | none => for mode in ["pairs", "leaf", "opt", "lists", "strs", "fns", "ref", "arr"] do run mode n
