/-! Runtime test: case `D71TesterT06` of the shared dependent-type corpus
(programs built by another translator's team and checked against native
Lean). It checks: A cast between two rigid positions (inductive read by tag
and field slot), and a cast node in generic code -/
inductive Sum3 where
  | a
  | b (x : Nat)
  | c (x : Nat) (y : Nat)
unsafe def asOpt (s : Sum3) : Option Nat := unsafeCast s
@[implemented_by asOpt, noinline] def asOptS (_ : Sum3) : Option Nat := none
unsafe def coerceU {α β : Type} [Inhabited β] (x : α) : β := unsafeCast x
@[implemented_by coerceU, noinline] def coerceS {α β : Type} [Inhabited β] (_ : α) : β := default
@[noinline] def mkS (n : Nat) : Sum3 := if n % 2 == 0 then Sum3.a else Sum3.b n
def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 7
  let u : UInt32 := coerceS n
  let k : Nat := coerceS (n % 2 == 0)
  IO.println s!"{asOptS (mkS n)} {asOptS (mkS (n+1))} {u} {k}"
