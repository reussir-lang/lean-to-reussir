/-! Runtime test: `LEAN_ABORT_ON_PANIC` (see `RtAbortPanic.pipe`): the panic
message goes to `std::cerr` (flushing stdout first), then the process aborts
(exit 134) without running anything else. -/

def boom (n : Nat) : Nat := if n > 2 then panic! s!"boom {n}" else n

def main (args : List String) : IO Unit := do
  IO.println "stdout before"
  IO.eprintln "stderr before"
  IO.println s!"value {boom (args.length + 5)}"
  IO.println "never"
