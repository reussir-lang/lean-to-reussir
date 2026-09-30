/-! Runtime test: child processes — `IO.Process.output`/`run` (piped
stdout and stderr), a piped stdin closed with `takeStdin`, environment
changes, the working directory, a command that cannot be executed (the
child reports it and exits with 255), `kill` (exit code 128 + 9) and
`tryWait`. -/

def main : IO Unit := do
  let o ← IO.Process.output { cmd := "sh", args := #["-c", "echo out; echo err >&2; exit 3"] }
  IO.println s!"output: code {o.exitCode} stdout {repr o.stdout} stderr {repr o.stderr}"
  let r ← IO.Process.run { cmd := "echo", args := #["run", "me"] }
  IO.println s!"run: {repr r}"
  let e ← IO.Process.output { cmd := "sh", args := #["-c", "echo \"[$RT_A][$RT_B]\""], env := #[("RT_A", some "set"), ("RT_B", none)] }
  IO.println s!"env: {repr e.stdout}"
  let c ← IO.Process.output { cmd := "pwd", cwd := some "/" }
  IO.println s!"cwd: {repr c.stdout}"
  let bad ← IO.Process.output { cmd := "rt-process-no-such-command" }
  IO.println s!"missing: code {bad.exitCode} stderr {repr bad.stderr}"
  let child ← IO.Process.spawn { cmd := "tr", args := #["a-z", "A-Z"], stdin := .piped, stdout := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr "piped through tr\n"
  stdin.flush
  let (_, child) ← child.takeStdin  -- drop the handle: tr sees end of file
  let _ := stdin
  let out ← child.stdout.readToEnd
  IO.println s!"tr: {repr out} code {← child.wait}"
  let sleeper ← IO.Process.spawn { cmd := "sleep", args := #["30"] }
  IO.println s!"tryWait while running: {(← sleeper.tryWait).isSome}"
  sleeper.kill
  IO.println s!"killed: {← sleeper.wait}"
  let quick ← IO.Process.spawn { cmd := "true" }
  let _ ← quick.wait
  try
    let _ ← quick.wait
    IO.println "second wait ok"
  catch err => IO.println s!"second wait: {err}"
