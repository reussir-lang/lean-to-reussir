/-!
Runtime test of the optimization `unread-fields` (off by default; this
test turns it on, `RtUnreadFieldsStream.enable-opts`): a callback that only
the runtime calls. `main` installs a stderr stream (`IO.setStderr`) whose
`putStr` writes, with a prefix, to a handle on `/dev/stdout`; the program
prints only through that handle (`IO.FS.Handle.putStrLn`), so no Lean code
of it reads a stream's fields. The panic of `a[i]!` writes its message
with the current stderr stream's `putStr`, natively and here
(`l2r_stderr_put`). The fields of `IO.FS.Stream` always count as read (an
extern takes the type, and the runtime reads them), so the callback stays.
-/

def main (args : List String) : IO Unit := do
  let out ← IO.FS.Handle.mk "/dev/stdout" .append
  let s : IO.FS.Stream := {
    flush := pure ()
    read := fun _ => pure .empty
    write := fun _ => pure ()
    getLine := pure ""
    putStr := fun m => out.putStr s!"[custom stderr] {m}"
    isTty := pure false }
  let _ ← IO.setStderr s
  let a : Array Nat := #[1, 2, 3]
  let i := args.length + 5
  out.putStrLn s!"before: {a.size}"
  out.putStrLn s!"value: {a[i]!}"
  out.putStrLn "after"
  out.flush
