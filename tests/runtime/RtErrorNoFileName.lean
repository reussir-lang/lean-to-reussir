/-! Runtime test: IO errors that carry no file name, an intended difference
from native (plan §10, "Runtime: Lean bugs we do not reproduce", LB-03 in
lean-runtime's docs/lean-bugs.md). Natively an error of
the classes `noFileOrDirectory` (ENOENT) and `interrupted` (EINTR) from a
call that passes no file name (`getcwd`, `waitpid`, `kill`, `flock`,
`fflush`, `fseek`, `ftruncate`, `fread`, `fwrite`, getline, `fputs`)
crashes: Lean's `decode_io_error` dereferences the null name (SIGSEGV, exit
139, buffered stdout lost). lean2rr raises the class's error with an empty
file name. The `.pipe` runs each scenario in its own process:
- `cwd`: `getCurrentDir` after the working directory was removed (ENOENT):
  natively a crash, with lean2rr `noFileOrDirectory "" 2 ...`;
- `temp`: `createTempFile` and `createTempDir` with `TMPDIR` naming a
  missing directory (ENOENT from libuv's `mkstemp`/`mkdtemp`, decoded by
  `decode_uv_error` without a name): natively a crash at the first;
- `wait`: `Child.wait` on a child already waited for (ECHILD) and `kill` of
  it (ESRCH): nameless errors of other classes, the same natively.
Expectation files: RtErrorNoFileName.native.out and .l2r.out. -/

def describe : IO.Error → String
  | .noFileOrDirectory f c m => s!"noFileOrDirectory {repr f} {c} {repr m}"
  | .interrupted f c m => s!"interrupted {repr f} {c} {repr m}"
  | e => s!"other class: {e}"

def main (args : List String) : IO Unit := do
  IO.println s!"{args[0]!}: start"
  match args[0]! with
  | "cwd" =>
    let d : System.FilePath := "rterrnoname-tmp"
    IO.FS.createDirAll d
    let abs ← IO.FS.realPath d
    IO.Process.setCurrentDir abs
    IO.FS.removeDir abs
    try
      let c ← IO.Process.getCurrentDir
      IO.println s!"cwd {c}"
    catch e => IO.println (describe e)
  | "temp" =>
    try
      let (_, p) ← IO.FS.createTempFile
      IO.println s!"temp file {p}"
    catch e => IO.println (describe e)
    try
      let p ← IO.FS.createTempDir
      IO.println s!"temp dir {p}"
    catch e => IO.println (describe e)
  | _ =>
    let child ← IO.Process.spawn { cmd := "true" }
    let code ← child.wait
    IO.println s!"first wait {code}"
    try
      let c ← child.wait
      IO.println s!"second wait {c}"
    catch e => IO.println (describe e)
    try child.kill; IO.println "killed" catch e => IO.println (describe e)
  IO.println s!"{args[0]!}: end"
