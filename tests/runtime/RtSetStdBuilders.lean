prelude
import Init.System.IO
/-! Runtime test of the `IO.Error` builders (hunt r7 B): a program that
reaches the standard streams only through `IO.setStdin` and `IO.setStdout`
(the externs `lean_get_set_stdin`, `lean_get_set_stdout`), with no
`IO.getStdout` & co., no file IO and no `IO.getRandomBytes` at startup (a
`prelude` program without `Init.Data.Random`). The streams' operations
report errors through the runtime's last-error protocol, so the program
needs Lean's `IO.Error` builders. Stage 1 made them only for the three
getters, and the error builder `l2r_io_err_R` had no arm for the error:
the write to the old stdin (glibc's stdin takes no writes: EBADF) ended in
`INTERNAL PANIC: unreachable code has been reached`. Natively it is caught
as `invalid argument (error code: 9, bad file descriptor)`. -/

def main : IO UInt32 := do
  let r ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let oldIn ← IO.setStdin (IO.FS.Stream.ofBuffer r)
  let oldOut ← IO.setStdout (IO.FS.Stream.ofBuffer r)
  try
    oldIn.putStr "x"
    oldOut.putStr "no error\n"
  catch e =>
    oldOut.putStr ("caught: " ++ toString e ++ "\n")
  return 0
