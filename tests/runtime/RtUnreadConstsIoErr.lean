/-! Runtime test of the optimization `unread-consts` (review of size-core):
a left-out constant whose code calls an `IO.Error` builder
(`IO.Error.mkAlreadyExistsFile`, the `@[export]` behind
`lean_mk_io_error_already_exists_file`) does not take the builder with it.
The lowering calls the builders by name for every fallible IO extern, here
`createDir`'s error for a directory that exists. Before the fix the builder
was left out with the constant and the error ended in an internal panic. -/

def errVal : IO.Error := IO.Error.mkAlreadyExistsFile "a" 2 "b"

def main : IO Unit := do
  try
    IO.FS.createDir "."
  catch e => IO.println s!"caught: {e}"
