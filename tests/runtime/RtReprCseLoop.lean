/-! Runtime test: a value merged by Lean's mono-phase `cse` read in a loop
(blowup audit, probe CseLoop, checked and not a problem). `cse` merges the
calls `emptyRow n` at `List (Option Nat)` and at `List (Option String)`
(their erased arguments agree); lean2rr calls one instance and converts
its result to the other type, once, before the loop, which reads both
lists with O(1) functions: the allocations grow with n as native's do
(one conversion of n cells, not one per step). The output is checked
here; the allocations by tests/runtime/alloc-check.sh
(RtReprCseLoop.alloc). -/
@[noinline] def emptyRow {α : Type} (n : Nat) : List (Option α) := List.replicate n none

@[noinline] def firstIsNone {α : Type} : List (Option α) → Nat
  | none :: _ => 1
  | _ => 0

@[noinline] def secondIsNone {α : Type} : List (Option α) → Nat
  | _ :: none :: _ => 1
  | _ => 0

def main (args : List String) : IO Unit := do
  let n := (args.headD "1000").toNat!
  let a : List (Option Nat) := emptyRow n
  let b : List (Option String) := emptyRow n
  let mut acc := 0
  for i in [0:n] do
    acc := acc + firstIsNone a + secondIsNone b + i % 2
  IO.println acc
