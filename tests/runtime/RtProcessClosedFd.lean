/-! Runtime test: a program started with stdout closed (`RtProcessClosedFd.pipe`)
spawns children. Natively libuv's close-on-exec descriptor takes the place
of descriptor 1, so the children see it closed (`EBADF`, not `EINVAL`). -/
def main : IO Unit := do
  let c ← IO.Process.spawn { cmd := "sh", args := #["-c",
    "if [ -e /proc/$$/fd/1 ]; then echo 'child: stdout open' >&2; else echo 'child: stdout closed' >&2; fi"] }
  IO.eprintln s!"exit {← c.wait}"
  let c ← IO.Process.spawn { cmd := "cat", args := #["/dev/null", "-"], stdin := .null }
  IO.eprintln s!"cat exit {← c.wait}"
  let o ← IO.Process.output { cmd := "sh", args := #["-c", "echo captured"] }
  IO.eprintln s!"output {repr o.stdout} {o.exitCode}"
