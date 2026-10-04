/-! Runtime test (review RST3-04): the `Child` operations after the child has been reaped.
Natively the pid then names no child of the program: `wait` and `tryWait` are `waitpid` on it
(`ECHILD`), `kill` is `kill` or, after `setsid`, `killpg` on it (`ESRCH`). lean2rr's runtime keeps
lean-runtime's process object of a child only until it is reaped (by `wait`, or by a `tryWait`
that sees it exit), then makes the same system calls. 200 children spawned and reaped one after
another leave no entry behind. -/
def main : IO Unit := do
  let c ← IO.Process.spawn { cmd := "sh", args := #["-c", "exit 3"] }
  IO.println s!"wait: {← c.wait}"
  try IO.println s!"wait again: {← c.wait}" catch e => IO.println s!"wait again: {e}"
  try IO.println s!"tryWait: {← c.tryWait}" catch e => IO.println s!"tryWait: {e}"
  try c.kill; IO.println "kill: ok" catch e => IO.println s!"kill: {e}"
  let g ← IO.Process.spawn { cmd := "sh", args := #["-c", "exit 4"], setsid := true }
  IO.println s!"wait (setsid): {← g.wait}"
  try g.kill; IO.println "kill (setsid): ok" catch e => IO.println s!"kill (setsid): {e}"
  let t ← IO.Process.spawn { cmd := "sh", args := #["-c", "exit 5"] }
  let mut r := none
  while r.isNone do
    r ← t.tryWait
    if r.isNone then IO.sleep 1
  IO.println s!"tryWait until exited: {r}"
  try IO.println s!"wait after tryWait: {← t.wait}" catch e => IO.println s!"wait after tryWait: {e}"
  try IO.println s!"tryWait after tryWait: {← t.tryWait}" catch e => IO.println s!"tryWait after tryWait: {e}"
  let mut sum := 0
  for i in [0:200] do
    let k ← IO.Process.spawn { cmd := "sh", args := #["-c", s!"exit {i % 7}"] }
    sum := sum + (← k.wait).toNat
  IO.println s!"sum of 200 exit codes: {sum}"
