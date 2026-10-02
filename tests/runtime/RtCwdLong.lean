import Std.Internal.UV.System
/-! Runtime test: working directories around `PATH_MAX` (4096 bytes, the
NUL included). Lean's C code passes `PATH_MAX` buffers to `getcwd`
(`IO.currentDir`, `IO.Process.getCurrentDir`) and to `realpath`
(`IO.FS.realPath`), and libuv's `cwd` retries a path that does not fit in
a buffer one byte longer (`ENOBUFS`): a path of 4095 bytes works, one of
4096 or more fails. -/

def tryIO (label : String) (x : IO String) : IO Unit := do
  try IO.println s!"  {label}: {← x}" catch e => IO.println s!"  {label}: error: {e}"

def report (len : Nat) : IO Unit := do
  IO.println s!"cwd of {len} bytes"
  tryIO "IO.currentDir" do return toString (← IO.currentDir).toString.utf8ByteSize
  tryIO "IO.Process.getCurrentDir" do return toString (← IO.Process.getCurrentDir).toString.utf8ByteSize
  tryIO "realPath ." do return toString (← IO.FS.realPath ".").toString.utf8ByteSize
  tryIO "uv cwd" do return toString (← Std.Internal.UV.System.cwd).utf8ByteSize

/-- Create directory `ddd…` (`n` bytes) in the current one and enter it. -/
def enter (n : Nat) : IO Unit := do
  let d := String.ofList (List.replicate n 'd')
  IO.FS.createDir d
  IO.Process.setCurrentDir d

def main : IO Unit := do
  let home ← IO.currentDir
  let top := home / "rtcwdlong"
  IO.FS.createDir top
  IO.Process.setCurrentDir top
  -- Directories of 200 bytes, then one of 50 to 250 bytes: 4095 bytes.
  let mut len := top.toString.utf8ByteSize
  while 4095 - len > 251 do
    enter 200
    len := len + 201
  let k := 4095 - len - 1
  enter k
  report 4095
  -- Its sibling one byte longer: 4096 bytes.
  IO.Process.setCurrentDir ".."
  enter (k + 1)
  report 4096
  enter 200
  report 4297
  IO.Process.setCurrentDir home
  discard <| IO.Process.output { cmd := "rm", args := #["-rf", top.toString] }
  IO.println s!"removed {!(← top.pathExists)}"
