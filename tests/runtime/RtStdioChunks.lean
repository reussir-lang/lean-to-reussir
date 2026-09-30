/-! Runtime test (glibc stdio model): write chunking of stdout and file handles (compare the
write(2) calls under strace; also see RvChunks.pipe). -/

def rep (c : Char) (n : Nat) : String := String.ofList (List.replicate n c)

def seq : List String :=
  [rep 'a' 1, rep 'b' 4095, rep 'c' 1, rep 'd' 4096, rep 'e' 8192, rep 'f' 4097,
   "x\ny\nz", rep 'g' 100, rep 'h' 12293, "p\nq\n", rep 'i' 3000 ++ "\n" ++ rep 'j' 2000 ++ "\nk",
   "\n", rep 'l' 4000, rep 'm' 96, rep 'n' 4096]

def main : IO Unit := do
  for s in seq do
    IO.print s
    IO.eprint "|"
  let h ← IO.FS.Handle.mk "rvchunks.txt" .write
  for s in seq do
    h.putStr s
  h.flush
  -- readWrite interplay
  IO.FS.writeFile "rvchunks2.txt" (rep 'z' 20000)
  let r ← IO.FS.Handle.mk "rvchunks2.txt" .readWrite
  let _ ← r.getLine
  r.putStr (rep 'A' 10)
  let _ ← r.read 100
  r.putStr (rep 'B' 5000)
  let _ ← r.read 3000
  r.putStr (rep 'C' 1500)
  r.rewind
  r.putStr (rep 'D' 4096)
  let _ ← r.read 1
  r.putStr "E"
  r.flush
  let s ← IO.FS.readFile "rvchunks2.txt"
  IO.println s!"\nsize {s.length} hash {hash s}"
