/-! String literals containing `[:` (Reussir bug 21: lean2rr's literal table
is a polymorphic FFI texture, whose `[:` without a later `:]` was dropped). -/

def main : IO Unit := do
  IO.println "slice a[:3] and b[:4]"
  IO.println "[::1]"
  IO.println s!"{"x[:"}{"y"}"
  IO.println ("p[:q".splitOn "[:")
  IO.println ("a[:b".replace "[:" "<>")
