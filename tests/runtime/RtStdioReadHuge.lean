/-! Runtime test (glibc stdio model): `Handle.read n` allocates an `n`-byte array first
(`lean_alloc_sarray_would_overflow` → ENOMEM error; failed malloc →
out-of-memory panic). -/

def showErr (act : IO α) (fmt : α → String) : IO String := do
  try return fmt (← act) catch e => return s!"error: {e}"

def main : IO Unit := do
  IO.FS.writeFile "rvreadhuge.txt" "abc"
  let h ← IO.FS.Handle.mk "rvreadhuge.txt" .read
  IO.println (← showErr (h.read (USize.ofNat (2^64 - 1))) fun b => s!"read {b.size}")
  h.rewind
  IO.println (← showErr (h.read (USize.ofNat (2^40))) fun b => s!"read {b.size}")
  h.rewind
  IO.println (← showErr (h.read (USize.ofNat (2^50))) fun b => s!"read {b.size}")
