/-! Runtime test: more child processes — a child that cannot execute or
change directory: natively it first flushes the parent's pending stdout
into its own stdout (`std::cerr` is tied to `std::cout`), which
`IO.Process.output` captures, so the bytes appear twice
(`NAME.native.out`); lean2rr's child writes none of them
(lean-runtime's LB-42; `NAME.l2r.out`); `wait` borrows the child, so an unread pipe
stays open while it runs; `tryWait` after exit and after reaping; `kill`
of a reaped child; `setsid` (the group is killed); `output` with input;
`run` failures; a non-UTF-8 stdout (reported after `wait`); children in
polymorphic code and a configuration computed at run time. -/
open IO.Process

def showOut (tag : String) (o : Output) : IO Unit :=
  IO.println s!"{tag}: code {o.exitCode} out {repr o.stdout} err {repr o.stderr}"

def waitAll {cfg} (cs : List (Child cfg)) : IO (List UInt32) := cs.mapM (·.wait)

def main (argv : List String) : IO Unit := do
  IO.println "pending"
  showOut "missing" (← output { cmd := "rt-process-spawn-no-such-command" })
  showOut "badcwd" (← output { cmd := "pwd", cwd := some "/rt-process-spawn-no-such-dir" })
  showOut "env" (← output { cmd := "sh", args := #["-c", "echo \"[${A-unset}][${B-unset}][${C-unset}]\""], env := #[("A", some "1"), ("A", some "2"), ("B", some ""), ("C", some "x"), ("C", none)] })
  showOut "noinherit" (← output { cmd := "/usr/bin/env", env := #[("ONLY", some "me")], inheritEnv := false })
  showOut "signal" (← output { cmd := "sh", args := #["-c", "kill -TERM $$"] })
  showOut "input" (← output { cmd := "sh", args := #["-c", "cat; echo done >&2"] } (some "fed\n"))
  -- The child writes to its unread stdout pipe while the parent waits.
  let c ← spawn { cmd := "sh", args := #["-c", "sleep 0.2; echo late || echo write-failed >&2"], stdout := .piped }
  IO.println s!"late writer: {← c.wait}"
  let s ← spawn { cmd := "sleep", args := #["30"] }
  IO.println s!"tryWait running: {← s.tryWait}"
  s.kill
  IO.println s!"killed: {← s.wait}"
  try IO.println s!"tryWait after reap: {← s.tryWait}" catch e => IO.println s!"tryWait after reap: {e}"
  try s.kill; IO.println "kill after reap ok" catch e => IO.println s!"kill after reap: {e}"
  let r ← spawn { cmd := "sh", args := #["-c", "sleep 0.1; exit 7"] }
  let mut res := none
  while res.isNone do
    res ← r.tryWait
    IO.sleep 20
  IO.println s!"polled: {res}"
  -- `setsid`: `kill` kills the process group, the grandchild too.
  let g ← spawn { cmd := "sh", args := #["-c", "sleep 30 & echo $!; wait"], stdout := .piped, setsid := true }
  let line ← g.stdout.getLine
  g.kill
  IO.println s!"group killed: {← g.wait}"
  IO.sleep 100
  let chk ← output { cmd := "sh", args := #["-c", s!"kill -0 {line.trimAscii} 2>/dev/null && echo alive || echo gone"] }
  IO.println s!"grandchild: {chk.stdout.trimAscii}"
  try
    let _ ← run { cmd := "sh", args := #["-c", "echo oops >&2; exit 3"] }
  catch e => IO.println s!"run failed: {e}"
  -- A configuration computed at run time, children through polymorphic code.
  let cfg : StdioConfig := { stdout := if argv.isEmpty then .piped else .inherit }
  let cs : List (Child cfg) ← [1, 2, 3].mapM fun i =>
    (spawn { toStdioConfig := cfg, cmd := "sh", args := #["-c", s!"exit {i}"] } : IO (Child cfg))
  IO.println s!"codes: {← waitAll cs}"
  try
    let o ← output { cmd := "printf", args := #["\\377"] }
    IO.println s!"bad stdout?? {o.exitCode}"
  catch e => IO.println s!"bad stdout: {e}"
