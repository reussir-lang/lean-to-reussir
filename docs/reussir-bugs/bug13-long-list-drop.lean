/-! Bug 13 through lean2rr: releasing a long chain of cells at once.
Usage: prog CASE N
  CASE 0: `List.replicate N 7`, Lean's List (the tail is the cell's last field)
  CASE 1: a snoc list `SnocS.snoc : SnocS → String → SnocS` (the chain is the
          first field, a String is last)
Each case builds the chain, prints one element and drops the chain when
`main` returns. Expected output (as native Lean): `(some 7)` (CASE 0) or
`0` (CASE 1). lean2rr runs `main` on a thread with a 1 GiB stack; with
Reussir ef922049 both cases at N = 40000000 abort with "Stack overflow
detected. Aborting." (SIGABRT). -/
inductive SnocS where
  | nil : SnocS
  | snoc : SnocS → String → SnocS

def mkSnocS : Nat → SnocS → SnocS
  | 0, acc => acc
  | n+1, acc => mkSnocS n (.snoc acc (if n % 1000 == 0 then toString n else "x"))

def SnocS.last : SnocS → String | .nil => "" | .snoc _ x => x

def main (args : List String) : IO Unit := do
  let c := (args.head? >>= String.toNat?).getD 0
  let n := ((args.drop 1).head? >>= String.toNat?).getD 40000000
  match c with
  | 0 => let l := List.replicate n 7; IO.println s!"{l.head?}"
  | _ => let s := mkSnocS n .nil; IO.println s!"{s.last}"
