/-! Runtime test: a cycle of tail calls that passes a new thunk to a parameter
the other declaration borrows (`Thunk.get` borrows), in a program that makes
resources (it opens a file), where lean2rr emulates Lean's borrowed
parameters. Natively the caller releases the thunk after the call
(`l_pong(x, ..); lean_dec_ref(x); return`), so the call is no tail call and
the cycle recurses. The thunk holds no resource (the flow analysis of
`keepsAt`, Lower/Borrow), so lean2rr does not keep it and the cycle is a
state machine: the same result with less stack. (Kept by type, closures and
thunks counted, the cycle recursed as natively, with smaller frames.) The
depth, 10^5 on an 8 MB stack (`.pipe`), passes on both sides: the test pins
the result, not an overflow. -/

mutual
@[noinline] partial def ping (t : Thunk Nat) (n : Nat) : Nat :=
  if n == 0 then t.get else pong (Thunk.pure (t.get + 1)) (n - 1)
@[noinline] partial def pong (t : Thunk Nat) (n : Nat) : Nat :=
  if n == 0 then t.get else ping (Thunk.pure (t.get + 2)) (n - 1)
end

def main : IO Unit := do
  let p : System.FilePath := "rtbtc.txt"
  let h ← IO.FS.Handle.mk p .write
  h.putStrLn s!"ping {ping (Thunk.pure 0) 100000}"
  h.flush
  IO.print (← IO.FS.readFile p)
  IO.FS.removeFile p
