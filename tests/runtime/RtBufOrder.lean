/-! Runtime test: stdout reaches the descriptor in the same chunks as glibc's
stdio (`st_blksize` blocks, whole blocks of large writes written directly),
so stdout and the unbuffered stderr interleave identically when both go to
one pipe (`RtBufOrder.pipe` runs `$BIN 2>&1`). -/

def main : IO Unit := do
  for i in [0:700] do
    IO.println s!"line {i}"
    if i % 150 == 0 then IO.eprintln s!"ERR {i}"
  IO.print ("x".pushn 'y' 10000)
  IO.eprintln "ERR big"
  IO.println ""
  for i in [0:50] do
    IO.print ("z".pushn 'w' (i * 97 % 5000))
    IO.eprintln s!"ERR {i}"
  let out ← IO.getStdout
  out.putStr "before flush"
  out.flush
  IO.eprintln "ERR after flush"
  IO.println "end"
