/-! Runtime test: a closed term that traces runs once when its value is
boxed (pass `boxed-consts`). `noisy 1.5` is a closed term of `K` and of
`L`, used once, by a constant that is not straight-line (an `if`, a
`match`): lean2rr evaluates such a closed term where it is used instead of
caching it (`uncachedConsts`). Its value goes into a box (an array or list
element). Boxing a constant once calls the constant's function for the
box; for such a closed term that was a second evaluation, and the trace
printed twice (found while writing the pass; `closedLetValue` leaves these
closed terms out). Natively each trace prints once. Only live branches
hold traced closed terms: natively the box of a closed term (its
`_boxed_const`) is computed at startup even in a branch that never runs
(a judged Lean compiler bug, plan §10, "A boxed constant in a branch
that never runs is computed at startup"). -/

@[noinline] def noisy (x : Float) : Float := dbgTrace s!"noisy {x}" fun _ => x * 2.0

@[noinline] def flag (n : Nat) : Bool := n % 2 == 0

def K : Array Float := if flag 4 then #[noisy 1.5, 3.0] else #[]

def L : List Float := match flag 6 with
  | true => [noisy 3.5, 1.0]
  | false => []

def main : IO Unit := do
  IO.println s!"{K} {L}"
