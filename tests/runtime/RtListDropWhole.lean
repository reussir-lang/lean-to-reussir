/-! Runtime test (hunt HMEM-01 of leanrt's memory core): the peak memory
of a long list dropped whole. Reussir's glue frees a list along its tail
before the drain pops anything, so every boxed head waits on Reussir's
pending stack until the walk ends. A head whose cell has a wide header (a
pair, an `Option`, a list, a structure with a `String`, a function value:
lean2rr numbers its payload type with `WIDE_BIT`) is deferred `_wide` and
links to the head before it through its header; a leaf head (a structure
of scalars) is freed at once. Before, each head took one 24-byte entry of
the stack's vector (n = 4M pairs: 391 MB against native's 258 MB; a
function value's enum got the mark only after HRT2-02: n = 10^6, 89 MB
against native's 70 MB).
Arguments: MODE N, MODE one of `pairs`, `leaf`, `opt`, `lists`, `strs`,
`fns` (default: all six, N = 1000). Each mode builds a list of N elements, reads
its first element and drops the list whole. The output is checked here;
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

def run (mode : String) (n : Nat) : IO Unit := do
  let r ← match mode with
    | "pairs" => pure (firstPair (pairs n))
    | "leaf" => pure (firstLeaf (leaves n)).toNat
    | "opt" => pure (firstOpt (opts n))
    | "lists" => pure (firstList (lists n))
    | "strs" => pure (firstStr (strs n))
    | "fns" => pure (firstFn (fns n))
    | _ => throw (IO.userError s!"unknown mode {mode}")
  IO.println s!"{mode} {n}: {r}"

def main (args : List String) : IO Unit := do
  let n := (args.getD 1 "1000").toNat!
  match args.head? with
  | some mode => run mode n
  | none => for mode in ["pairs", "leaf", "opt", "lists", "strs", "fns"] do run mode n
