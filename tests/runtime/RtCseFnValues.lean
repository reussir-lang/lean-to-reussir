/-! Runtime test: a call that Lean's mono `cse` merges across types whose
value is a function (review of XT-6, rv7/frontend/xt6 XT6-01). Partial
applications of a polymorphic function with the same value arguments
(`List.take k` as `List Nat → List Nat` and as `List String → List String`,
`tagger n` as `Nat → Nat` and `String → String`) are one closure natively.
Aligning the later partial application to the earlier one's type arguments
made it a `List Nat → List Nat` (`Nat → Nat`) closure used at the String
type: no representation conversion exists ("no representation conversion
from L2RFn_F3nNat3nNat to L2RFn_F4nLStr4nLStr"), and the program died with
"INTERNAL PANIC: unreachable code has been reached". Such calls now go to
the instance at `lcAny`, whose closures serve both types through wrappers
(`Mono.serves`, `uniformArgs`). -/

@[noinline] def tagger {α : Type} (n : Nat) (x : α) : α := dbgTrace s!"tag {n}" fun _ => x

@[noinline] def applyTo {α : Type} (f : α → α) (x : α) : α := f x

def closures (n : Nat) : String :=
  let f : Nat → Nat := tagger n
  let g : String → String := tagger n
  s!"{applyTo f 5} {applyTo g "s"}"

def stored (k : Nat) : String :=
  let fs : Array (List Nat → List Nat) := #[List.take k, List.drop k]
  let gs : Array (List String → List String) := #[List.take k, List.drop k]
  s!"{fs.map (· [7, 8, 9])} {gs.map (· ["x", "y", "z"])}"

def main (args : List String) : IO Unit := do
  IO.println s!"closures {closures args.length}"
  IO.println s!"stored {stored (args.length + 1)}"
