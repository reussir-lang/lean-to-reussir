/-!
Calls of a library extern that can panic, at two type arguments, whose
values agree once the type arguments are erased. `getBoth` reads `a[n]!`
and `b[n]!` on two empty arrays at `Option Nat` and `Option String`;
`setBoth` writes `none` at index `n` of two empty arrays with `set!`.
Natively Lean's mono `cse` merges the two `Array.get!Internal` calls
(`lean_array_get`) into one, and the two `Array.set!` calls too, so each
function prints one `index out of bounds` message. Stage 1's search for
such calls (`Mono.erasedMerges`) left out every extern of Lean's library,
on the claim that the observable ones are `@[never_extract]`;
`Array.get!Internal` is not, so lean2rr kept two instances and printed
two messages. Now only the pure total externs (`pureExterns`) are left
out. A bug hunt of the passes (repro c22). At element types that do not
serve each other (`Option (Nat → Nat)` and `Option (String → String)`) the
two reads stay apart: the arrays come from `Array.mkEmpty`, a pure extern
the search leaves out (plan §10, "Merging after erasure").
-/

@[noinline] def getBoth (n : Nat) : Option Nat × Option String :=
  let a : Array (Option Nat) := #[]
  let b : Array (Option String) := #[]
  (a[n]!, b[n]!)

@[noinline] def setBoth (n : Nat) : Array (Option Nat) × Array (Option String) :=
  let a : Array (Option Nat) := #[]
  let b : Array (Option String) := #[]
  (a.set! n none, b.set! n none)

def main (args : List String) : IO Unit := do
  let (x, y) := getBoth args.length
  IO.println (x.isSome, y.isSome)
  let (p, q) := setBoth (args.length + 2)
  IO.println (p.size, q.size)
