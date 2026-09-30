/-! Runtime test: deep non-tail recursion runs on Lean's 1 GiB main stack;
overflowing it prints Lean's `Stack overflow detected. Aborting.` and aborts
(exit 134; buffered stdout is lost, as natively). -/

def deep : Nat → Nat
  | 0 => 0
  | n + 1 => deep n + 1

def main (args : List String) : IO Unit := do
  IO.eprintln s!"depth 100000: {deep (100000 + args.length)}"
  IO.eprintln s!"depth 1000000: {deep (1000000 + args.length)}"
  IO.println "this stdout line is still buffered when the stack overflows"
  IO.eprintln s!"overflow: {deep (10000000000 + args.length)}"
