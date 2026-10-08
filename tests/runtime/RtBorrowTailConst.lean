/-! Runtime test: a self tail call that passes a constant (here the closed
term `#[]`) to a parameter Lean borrows, in a program that creates
resources (plan §5.8, "Borrowing"). Natively the value of a constant is
borrowed (Lean's `fap c #[]`: its borrow inference does not make it owned,
its `explicitRc` puts no `dec` after the call), so the parameter stays
borrowed and the tail call stays a loop. lean2rr's `borrowedVars` did not
count constants as borrowed: it kept the argument until the call returned
(`l2r_release_after`), so the call was no longer a tail call, and a loop of
10^6 steps overflowed an 8 MB stack (hunt3 own, `Stack overflow detected`).
Runs with `LEAN_STACK_SIZE_KB=8192` (`.pipe`). -/

@[noinline] def loop (hs : Array IO.FS.Handle) (n acc : Nat) : IO Nat := do
  for h in hs do h.putStr "."
  match n with
  | 0 => return acc
  | n + 1 => loop #[] n (acc + hs.size + 1)

def main (args : List String) : IO Unit := do
  let n := 1000000 + args.length
  if args.length > 3 then
    -- Never runs: the program creates resources (borrow emulation on).
    let h ← IO.FS.Handle.mk "rtborrowtailconst-unused.txt" .write
    IO.println s!"{← loop #[h] 3 0}"
  IO.println s!"{← loop #[] n 0}"
