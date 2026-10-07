/-! Runtime test (lean-runtime's LB-46): an `append` handle's cursor starts
at the end of the file. `IO.FS.Mode.append` documents that "the read/write
cursor is positioned at the end of the file", and `Handle.truncate`
"Truncates the handle to its read/write cursor". Natively the cursor is at
0 after the open (Lean opens the file with `O_APPEND`, and glibc's
`fdopen(fd, "a")` then does not seek), so a `truncate` right after the open
empties the file and only the later write is left (`NAME.native.out`).
lean2rr opens files through lean-runtime's `Handle::open`, which moves an
`append` descriptor of a regular file to its end before `fdopen`, as glibc's
`fopen(path, "a")` does: the content is kept (`NAME.l2r.out`). The second
file is the contrast of LB-49 (not a bug, the same both ways): a byte
written but not flushed, then `truncate`, which counts that byte from the
end of the file, so the flush appends it after a NUL. lean-runtime's case
`io/append_starts_at_end`. -/

def main : IO Unit := do
  IO.FS.writeFile "a.txt" "keep"
  let h ← IO.FS.Handle.mk "a.txt" .append
  h.truncate
  h.putStr "+more"
  h.flush
  IO.println s!"truncate after open: {repr (← IO.FS.readFile "a.txt")}"
  IO.FS.writeFile "b.txt" "keep"
  let h2 ← IO.FS.Handle.mk "b.txt" .append
  h2.putStr "x"
  h2.truncate
  h2.flush
  IO.println s!"truncate with a pending byte: {repr (← IO.FS.readFile "b.txt")}"
