/-! Runtime test: output order around panics with stdout and stderr on one
pipe. A user panic goes through Lean's unbuffered stderr stream; an internal
panic (`Nat.pow` with a huge exponent) writes `INTERNAL PANIC` straight to
stderr and exits, flushing stdout only then. The exponent is 2^40: lean2rr
computes powers with an exponent of 2^32 or more where the result fits
(lean-runtime's LB-11, plan §10), and `2 ^ 2^40` does not, so both sides
end with `Nat.pow exponent is too big`. With `LEAN_ABORT_ON_PANIC`
(RtAbortPanic) the message goes to `std::cerr`, which flushes stdout first,
and the process aborts. -/

def boom (n : Nat) : Nat := if n > 2 then panic! s!"boom {n}" else n

def main (args : List String) : IO Unit := do
  IO.println "stdout line 1"
  IO.eprintln "stderr line 1"
  IO.println s!"panicking: {boom (args.length + 5)}"
  IO.println "stdout line 2"
  IO.eprintln "stderr line 2"
  let e : Nat := 1099511627776 + args.length
  IO.println s!"{(2 : Nat) ^ e}"
  IO.println "never"
