/-! Runtime test: `allocprof` runs the action, then prints its message (up
to the first NUL) and the note of a Lean runtime built without
`RUNTIME_STATS` on stderr. -/

def main (args : List String) : IO Unit := do
  let r ← allocprof "profile\u0000hidden" (pure (args.length + 1))
  IO.println s!"allocprof {r}"
