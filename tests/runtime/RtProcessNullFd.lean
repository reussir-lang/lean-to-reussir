/-! Runtime test: the descriptors a spawned program starts with when a
standard stream is `null` (LB-15 in lean-runtime's docs/lean-bugs.md; plan
§10, "Runtime: Lean bugs we do not reproduce"). Natively the forked child
opens `/dev/null` without close-on-exec and never closes it after `dup2`,
so the program inherits one more `/dev/null` descriptor per `null` stream,
at the lowest number free in the child (`IO.Process.output` without input
spawns with `stdin := .null`, so every program it runs gets one). lean2rr
opens `/dev/null` in the parent, close-on-exec, so the program gets its
standard streams and what the parent inherited, as with `piped`.

Each child is a shell that lists its own descriptors with `ls -l
/proc/$$/fd`: `ls` runs as a child of the shell, which opens nothing
meanwhile (the trailing `:` keeps dash from replacing itself with `ls`;
with stdout `null`, a second shell lists its parent's on stderr). The
output names no descriptor number, which depends on the host:
descriptors 0-2 are shown by kind (`null` or `pipe` with the access mode
the listing shows, `r`, `w` or `rw`; `other`; `closed`), and the ones
above 2 by their targets, compared with the first child's, which has no
`null` stream: `extra` (here only) and `missing` (there only). -/

/-- The `(descriptor, mode, target)` triples of an `ls -l` listing of
`/proc/PID/fd` (the mode of such a link is `lr-x------`, `l-wx------` or
`lrwx------`, after the descriptor's access mode). -/
def parse (out : String) : List (Nat × String × String) :=
  (out.splitOn "\n").filterMap fun line =>
    match line.splitOn " -> " with
    | [left, target] =>
      let words := left.splitOn " "
      (words.getLast?.bind String.toNat?).map fun n => (n, words.headD "", target)
    | _ => none

def kind (fds : List (Nat × String × String)) (n : Nat) : String :=
  match fds.lookup n with
  | some (mode, t) =>
    let access := match mode.toList with
      | _ :: r :: w :: _ => (if r == 'r' then "r" else "") ++ (if w == 'w' then "w" else "")
      | _ => "?"
    if t == "/dev/null" then s!"null-{access}"
    else if t.startsWith "pipe:" then s!"pipe-{access}"
    else "other"
  | none => "closed"

def lsfd : String := "ls -l /proc/$$/fd; :"

def report (name : String) (base : List (Nat × String × String)) (out : String) : IO Unit := do
  let fds := parse out
  let above (l : List (Nat × String × String)) := l.filter (·.1 > 2)
  let extra := ((above fds).filter fun p => !(above base).contains p).map (·.2.2)
  let missing := ((above base).filter fun p => !(above fds).contains p).map (·.2.2)
  IO.println s!"{name}: 0-2 {kind fds 0} {kind fds 1} {kind fds 2}; above 2: extra {extra}, missing {missing}"

def main : IO Unit := do
  let c ← IO.Process.spawn { cmd := "sh", args := #["-c", lsfd], stdin := .piped, stdout := .piped }
  let out ← c.stdout.readToEnd
  let _ ← c.wait
  let base := parse out
  if base.isEmpty then
    IO.println s!"no listing: {repr out}"
  report "stdin piped" base out
  let c ← IO.Process.spawn { cmd := "sh", args := #["-c", lsfd], stdin := .null, stdout := .piped }
  let out ← c.stdout.readToEnd
  let _ ← c.wait
  report "stdin null" base out
  let c ← IO.Process.spawn
    { cmd := "sh", args := #["-c", lsfd], stdin := .null, stdout := .piped, stderr := .null }
  let out ← c.stdout.readToEnd
  let _ ← c.wait
  report "stdin null, stderr null" base out
  -- The listing comes on stderr, redirected by a second shell: a shell that
  -- redirects a command's output keeps its own descriptor 1 open meanwhile
  -- (dash saves it above 9), which the listing would show.
  let c ← IO.Process.spawn
    { cmd := "sh", args := #["-c", "sh -c 'ls -l /proc/$PPID/fd >&2'; :"], stdin := .piped,
      stdout := .null, stderr := .piped }
  let out ← c.stderr.readToEnd
  let _ ← c.wait
  report "stdout null" base out
  let o ← IO.Process.output { cmd := "sh", args := #["-c", lsfd] }
  report "IO.Process.output" base o.stdout
