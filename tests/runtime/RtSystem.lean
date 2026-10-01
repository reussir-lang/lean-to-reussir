import Std.Internal.UV.System
/-! Runtime test: `Std.Internal.UV.System` (libuv's process, user and
system queries). Only what is the same for every run of every build of the
program on one machine is printed: identities with the `IO` equivalents,
relations between values, the user's and host's names. -/
open Std.Internal.UV.System

def main : IO Unit := do
  IO.println s!"pid {(← osGetPid) == (← IO.Process.getPID).toUInt64}"
  IO.println s!"ppid positive {decide ((← osGetPpid) > 0)}"
  IO.println s!"cwd {(← cwd) == (← IO.currentDir).toString}"
  IO.println s!"home {(← osHomedir) == ((← IO.getEnv "HOME").getD "")}"
  IO.println s!"tmpdir {← osTmpdir}"
  let u ← osUname
  IO.println s!"uname {u.sysname} {u.machine} release nonempty {!u.release.isEmpty}"
  IO.println s!"hostname {← osGetHostname}"
  let pw ← osGetPasswd
  IO.println s!"passwd {pw.username} uid {pw.uid.isSome} home {pw.homedir == some (← osHomedir)}"
  match pw.gid with
  | some g => IO.println s!"group {((← osGetGroup g).map (·.gid)) == some g}"
  | none => pure ()
  IO.println s!"no group {(← osGetGroup 4000000).isNone}"
  osSetenv "L2R_SYS_TEST" "value 1"
  IO.println s!"getenv {← osGetenv "L2R_SYS_TEST"} {← IO.getEnv "L2R_SYS_TEST"}"
  IO.println s!"environ has it {(← osEnviron).contains ("L2R_SYS_TEST", "value 1")}"
  osUnsetenv "L2R_SYS_TEST"
  IO.println s!"after unset {← osGetenv "L2R_SYS_TEST"}"
  try osSetenv "" "x" catch e => IO.println s!"empty name: {e}"
  try osSetenv "A\x00B" "x" catch e => IO.println s!"NUL: {e}"
  let p ← osGetPriority 0
  osSetPriority 0 p
  IO.println s!"priority {p} {(← osGetPriority 0) == p}"
  let t1 ← hrtime
  let t2 ← hrtime
  IO.println s!"hrtime monotonic {decide (t2 ≥ t1)}"
  let r ← random 16
  match ← IO.wait r.result! with
  | .ok b => IO.println s!"random {b.size}"
  | .error e => IO.println s!"random failed {e}"
  let ru ← getrusage
  IO.println s!"rusage maxRSS positive {decide (ru.maxRSS > 0)}"
  IO.println s!"exePath {(← exePath) == (← IO.appPath).toString}"
  let total ← totalMemory
  IO.println s!"memory {decide (total > 0)} {decide ((← freeMemory) ≤ total)} {decide ((← availableMemory) ≤ total)}"
  let cpus ← cpuInfo
  IO.println s!"cpus {cpus.size} models {(cpus.toList.map (·.model)).eraseDups}"
  IO.println s!"constrained memory {← constrainedMemory}"
  IO.println s!"uptime positive {decide ((← uptime) > 0)}"
  setProcessTitle "ab"
  IO.println s!"title {← getProcessTitle}"
  chdir "/"
  IO.println s!"cwd after chdir {← cwd}"
  try chdir "/no/such/dir" catch e => IO.println s!"chdir: {e}"
