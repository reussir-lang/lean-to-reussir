/-! Runtime test (glibc stdio model): NUL bytes in diagnostics. Native prints the uncaught
exception with `string_cstr` (cut at the first NUL), and dbgTraceIfShared's
message too. -/

def main (args : List String) : IO Unit := do
  let a := #[1, 2, 3, args.length]
  let b := dbgTraceIfShared "sh\u0000ared" a
  IO.println s!"{a.size + b.size}"
  throw (IO.userError s!"bad\u0000tail {args.length}")
