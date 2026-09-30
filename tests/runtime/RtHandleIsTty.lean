/-! Runtime test: `IO.FS.Handle.isTty` is a `BaseIO` operation (it cannot
fail), unlike the other handle operations. -/

def main : IO Unit := do
  IO.FS.writeFile "rthandleistty.txt" "x"
  let h ← IO.FS.Handle.mk "rthandleistty.txt" .read
  IO.println s!"isTty {← h.isTty}"
  IO.FS.removeFile "rthandleistty.txt"
