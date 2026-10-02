import Std.Internal.UV.System
/-! Runtime test: strings from the system that are not valid UTF-8 (set up by
`RtOsStringsLossy.pipe`) become Lean strings as `lean_mk_string` makes them:
each invalid sequence is replaced by U+FFFD. Environment values (libuv's and
`IO.getEnv`), the home and temporary directories, a process title cut in the
middle of a character (the title can only grow over the memory of the
arguments: 8 bytes with `argv` = `P title`), and the paths of new temporary
files and directories under such a directory (which then do not exist under
the decoded name). -/
open Std.Internal.UV.System

def info (s : String) : String := s!"{s.quote} ({s.utf8ByteSize} bytes, {s.length} characters)"

def main (args : List String) : IO Unit := do
  match args with
  | ["title"] =>
    setProcessTitle "üüüüü"
    IO.println s!"title {info (← getProcessTitle)}"
  | ["temp"] =>
    let (h, p) ← IO.FS.createTempFile
    h.putStr "x"
    IO.println s!"createTempFile in {info ((p.parent.bind (·.fileName)).getD "")}, name of {(p.fileName.getD "").length}, exists {← p.pathExists}"
    let d ← IO.FS.createTempDir
    IO.println s!"createTempDir in {info ((d.parent.bind (·.fileName)).getD "")}, name of {(d.fileName.getD "").length}, exists {← d.pathExists}"
  | _ =>
    IO.println s!"osGetenv {((← osGetenv "L2R_BAD").map info).getD "none"}"
    IO.println s!"osEnviron {(((← osEnviron).find? (·.1 == "L2R_BAD")).map (info ·.2)).getD "none"}"
    IO.println s!"IO.getEnv {((← IO.getEnv "L2R_BAD").map info).getD "none"}"
    IO.println s!"osHomedir {info (← osHomedir)}"
    IO.println s!"osTmpdir {info (← osTmpdir)}"
