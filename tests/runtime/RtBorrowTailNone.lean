/-! Runtime test: self tail calls that pass a constructor without relevant
fields (`none`) to a parameter Lean borrows, in a program that makes a
promise (borrow emulation on). Natively `none` is a scalar: Lean's borrow
inference does not make it owned and its `explicitRc` puts no `dec` after
the call, so the parameter stays borrowed and the call stays a loop. A
join point's parameter to which every jump passes a borrowed value or
`none` is borrowed too. lean2rr's `borrowedVars` counted neither as
borrowed, kept the argument until the call returned
(`l2r_release_after`), and the loops of 10^6 steps overflowed an 8 MB
stack (review of hunt3 own; a promise program since promises count as
resources). Runs with `LEAN_STACK_SIZE_KB=8192` (`.pipe`).
- `loopNone`: passes `none` directly;
- `loopJp`: passes a join point's parameter, the borrowed `p` or `none`. -/

@[noinline] def loopNone (p : Option (IO.Promise Nat)) (n acc : Nat) : IO Nat := do
  match p with
  | some q => if ← IO.hasFinished q.result? then IO.println "resolved" else pure ()
  | none => pure ()
  match n with
  | 0 => return acc
  | n + 1 => loopNone none n (acc + 1)

@[noinline] def loopJp (p : Option (IO.Promise Nat)) (n acc : Nat) (flip : Bool) : IO Nat := do
  match p with
  | some q => if ← IO.hasFinished q.result? then IO.println "resolved" else pure ()
  | none => pure ()
  match n with
  | 0 => return acc
  | n + 1 =>
    let next := if flip then p else none
    let a1 := acc * 7 % 1000003
    let a2 := (a1 + n) * 13 % 1000033
    let a3 := (a2 + acc) * 17 % 1000037
    loopJp next n (a3 + 1) (!flip)

def main (args : List String) : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  IO.println s!"{← loopNone (some p) (1000000 + args.length) 0}"
  IO.println s!"{← loopJp (some p) 3 0 true}"
  IO.println s!"{← loopJp (some p) (1000000 + args.length) 0 (args.length == 0)}"
