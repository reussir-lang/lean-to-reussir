/-! Runtime test: when a resource passed to a function that borrows it is
released (plan §5.8, §10). Natively a borrowed parameter is released by the
caller after the call, not at its last use inside the callee.
- A helper writes to a file handle it borrows, then reads the same file
  through another handle: natively the data is still in the handle's buffer
  (nothing read); the file is flushed once the caller drops the handle.
- The same through a loop helper, and through a function value called by
  another function (natively Lean's `_boxed` releases the handle after the
  call); `IO.FS.withFile`'s callback, inlined, releases it at its last
  use.
- A child's stdin pipe, taken out of the `Child`, written by a helper that
  then waits for the child; and the `Child` itself, held by the caller
  while a helper sleeps after its last use: natively the child does not see
  end of file while the helper runs (`timeout 1 cat` is killed: 124). -/

@[noinline] def helper (h : IO.FS.Handle) (path : System.FilePath) : IO String := do
  h.putStr "hello"
  IO.FS.readFile path

@[noinline] def helper2 (h : IO.FS.Handle) (path : System.FilePath) (n : Nat) : IO Nat := do
  for i in [0:n] do
    h.putStr s!"line {i}\n"
  return (← IO.FS.readFile path).length

-- Calls its argument: a closure call passes `h` owned.
@[noinline] def applyTo (f : IO.FS.Handle → IO String) (h : IO.FS.Handle) : IO String := f h

@[noinline] def feed (h : IO.FS.Handle) (c : IO.Process.Child { stdin := .null }) : IO UInt32 := do
  h.putStrLn "hi"
  h.flush
  c.wait

@[noinline] def feedSleep (c : IO.Process.Child { stdin := .piped }) : IO Unit := do
  c.stdin.putStrLn "hi"
  c.stdin.flush
  IO.sleep 1500

def main : IO Unit := do
  let dir : System.FilePath := "rtborrow-tmp"
  IO.FS.createDirAll dir
  let a := dir / "a.txt"
  let h ← IO.FS.Handle.mk a .write
  IO.println s!"helper read [{← helper h a}]"
  IO.println s!"after [{← IO.FS.readFile a}]"
  let b := dir / "b.txt"
  let h2 ← IO.FS.Handle.mk b .write
  IO.println s!"helper2 read {← helper2 h2 b 3}"
  IO.println s!"after2 {(← IO.FS.readFile b).length}"
  let d := dir / "d.txt"
  let hd ← IO.FS.Handle.mk d .write
  IO.println s!"closure read [{← applyTo (fun h => helper h d) hd}] after [{← IO.FS.readFile d}]"
  let c := dir / "c.txt"
  let r ← IO.FS.withFile c .write fun h => do
    h.putStr "in callback"
    IO.FS.readFile c
  IO.println s!"withFile read [{r}] after [{← IO.FS.readFile c}]"
  let out1 := dir / "child1.txt"
  let child ← IO.Process.spawn { cmd := "sh", args := #["-c", s!"read x; timeout 1 cat > /dev/null; echo \"got $x cat=$?\" > {out1}"], stdin := .piped }
  let (stdin, child) ← child.takeStdin
  IO.println s!"code {← feed stdin child} child [{(← IO.FS.readFile out1).replace "\n" ""}]"
  let out2 := dir / "child2.txt"
  let c2 ← IO.Process.spawn { cmd := "sh", args := #["-c", s!"read x; timeout 1 cat > /dev/null; echo \"got $x cat=$?\" > {out2}"], stdin := .piped }
  feedSleep c2
  IO.sleep 1000
  IO.println s!"child2 [{(← IO.FS.readFile out2).replace "\n" ""}]"
  IO.FS.removeDirAll dir
