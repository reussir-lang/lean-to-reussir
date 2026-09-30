/-! Runtime test: glibc's stdout write rules, seen through where the
unbuffered stderr lines land (`RtStdoutBlock.pipe` merges the streams into
one pipe, block size 4096). The very first write finds no buffer: whole
blocks go straight to the descriptor. Later writes fill the buffer first. -/

def line (c : Char) (n : Nat) : String := String.ofList (List.replicate (n - 1) c) ++ "\n"

def main : IO Unit := do
  IO.print (line 'a' 4096)
  IO.eprintln "STDERR 1"
  IO.print (line 'b' 100)
  IO.eprintln "STDERR 2"
  IO.print (line 'c' 4096)
  IO.eprintln "STDERR 3"
  IO.print (line 'd' 8192)
  IO.eprintln "STDERR 4"
  IO.print (line 'e' 3900)
  IO.eprintln "STDERR 5"
  IO.print (line 'f' 20000)
  IO.eprintln "STDERR 6"
  IO.println "end"
