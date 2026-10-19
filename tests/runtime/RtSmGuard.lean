/-! Runtime test: the soundness guard of the optional pass `state-machines`
reached (docs/implementation/control-flow/state-machines.md). A join point
of the state machine of `loop` captures `x : Inf`, a type whose only
constructor needs a value of itself, so it has no finite value and no
placeholder (`zeroFinite`). That field gets no slot and stays in its
variant, so the entry point of `loop`'s state machine is a shared enum,
not an integer (the fallback); the other fields are in slots as usual.
`Inf` has no value, so the `some x` arm never runs; `mkOpt` hides that
from Lean (`@[noinline]`). `jp-small` is off (RtSmGuard.opts): it would
copy the small join points to their jumps, and no state machine would be
left. tests/runtime/sm-slots-check.sh checks that the enum is there. -/

inductive Inf where
  | mk : Inf → Inf

@[noinline] def infDepth (_ : Inf) : Nat := 7

@[noinline] def mkOpt (n : Nat) : Option Inf := if n > 1000000000 then none else none

partial def loop (fuel : Nat) (o : Option Inf) (acc : Nat) : Nat :=
  if fuel == 0 then acc else
  match o with
  | some x =>
    let r := if acc % 4 == 0 then some (acc + 1) else if acc == 77777 then none else some (acc * 3 % 10007)
    match r with
    | none => infDepth x + 1
    | some y => if y == 5 then infDepth x else loop (fuel - 1) o (y + infDepth x)
  | none =>
    let r := if acc % 4 == fuel % 4 then some (acc + fuel) else if acc == 77777 then none else some (acc * 3 % 10007)
    match r with
    | none => acc + 1
    | some y => loop (fuel - 1) (mkOpt y) (y % 10007)

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000
  IO.println s!"loop {n}: {loop n (mkOpt 3) 1}"
  IO.println s!"loop 0: {loop 0 (mkOpt 3) 1}"
  IO.println s!"loop 7: {loop 7 none 4}"
