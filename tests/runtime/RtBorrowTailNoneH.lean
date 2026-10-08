/-! Runtime test: `RtBorrowTailNone`'s join point loop over a handle (a
program that creates files: the borrow emulation was on before promises
counted as resources too). The join point's parameter is passed the
borrowed `p` or `none`; natively it is borrowed and the self tail call
stays a loop. lean2rr kept it until the call returned, and the loop of
10^6 steps overflowed an 8 MB stack (review of hunt3 own; it failed on dev
83a5dbac). Runs with `LEAN_STACK_SIZE_KB=8192` (`.pipe`). -/

@[noinline] def loop (p : Option IO.FS.Handle) (n acc : Nat) (flip : Bool) : IO Nat := do
  match p with
  | some h => h.putStr ""
  | none => pure ()
  match n with
  | 0 => return acc
  | n + 1 =>
    let next := if flip then p else none
    let a1 := acc * 7 % 1000003
    let a2 := (a1 + n) * 13 % 1000033
    let a3 := (a2 + acc) * 17 % 1000037
    loop next n (a3 + 1) (!flip)

def main (args : List String) : IO Unit := do
  let h ← IO.FS.Handle.mk "rtborrowtailnoneh-tmp.txt" .write
  IO.println s!"{← loop (some h) 3 0 true}"
  IO.println s!"{← loop (some h) (1000000 + args.length) 0 (args.length == 0)}"
  IO.FS.removeFile "rtborrowtailnoneh-tmp.txt"
