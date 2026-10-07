/-! Runtime test: fresh-rebuild with a join point outlined in the
alternative. `g` matches `r`, the fresh result of `mk`, and its `bad`
alternative only returns `r`, from an outlined join point (two jumps, one
path that returns another value, a body too big to copy); the field `e` is
used, so the alternative converts it from its box. The rebuilt value
`bad{f}` reads the binder `f` of the match, which the join point's
function must capture: it did not (rrc: "unknown variable"). `h` has the
same shape in a loop, whose join point is a variant of a state machine
(J4). -/

inductive R (α : Type) where
  | bad (x : α)
  | good (n : Nat)
  | none

@[noinline] def mk (n : Nat) : R String :=
  if n % 3 == 0 then .bad s!"bad {n}" else if n % 3 == 1 then .good (n * 2) else .none

@[noinline] def g (n m : Nat) : R String := Id.run do
  let r := mk n
  match r with
  | .bad e =>
    let k ← if e.length > m then
              if n == 9 then return .good 7
              pure (n + 1)
            else pure (n + 2)
    let a1 := k * 3 + n
    let a2 := a1 * a1 % 1000 + k
    let a3 := a2 * a1 % 997 + n
    let a4 := a3 * a2 % 991 + a1
    let a5 := a4 * a3 % 983 + a2
    let a6 := a5 * a4 % 977 + a3
    let a7 := a6 * a5 % 971 + a4
    let a8 := a7 * a6 % 967 + a5
    let a9 := a8 * a7 % 953 + a6
    let b1 := a9 * a8 % 947 + a7
    let b2 := b1 * a9 % 941 + a8
    let b3 := b2 * b1 % 937 + a9
    let b4 := b3 * b2 % 929 + b1
    let b5 := b4 * b3 % 919 + b2
    let b6 := b5 * b4 % 911 + b3
    let b7 := b6 * b5 % 907 + b4
    let b8 := b7 * b6 % 887 + b5
    let b9 := b8 * b7 % 883 + b6
    if b9 % 2 == 0 then return .good b9
    return r
  | .good v => return .good (v + 1)
  | .none => return .good 0

@[noinline] def h (n m fuel : Nat) : R String := Id.run do
  let r := mk n
  match r with
  | .bad e =>
    let k ← if e.length > m then
              if n == 9 then return .good 7
              pure (n + 1)
            else pure (n + 2)
    let a1 := k * 3 + n
    let a2 := a1 * a1 % 1000 + k
    let a3 := a2 * a1 % 997 + n
    let a4 := a3 * a2 % 991 + a1
    let a5 := a4 * a3 % 983 + a2
    let a6 := a5 * a4 % 977 + a3
    let a7 := a6 * a5 % 971 + a4
    let a8 := a7 * a6 % 967 + a5
    let a9 := a8 * a7 % 953 + a6
    let b1 := a9 * a8 % 947 + a7
    let b2 := b1 * a9 % 941 + a8
    let b3 := b2 * b1 % 937 + a9
    let b4 := b3 * b2 % 929 + b1
    let b5 := b4 * b3 % 919 + b2
    let b6 := b5 * b4 % 911 + b3
    let b7 := b6 * b5 % 907 + b4
    let b8 := b7 * b6 % 887 + b5
    let b9 := b8 * b7 % 883 + b6
    match fuel with
    | 0 => return r
    | f + 1 => if b9 % 2 == 0 then return h (n + 3) m f else return r
  | .good v => return .good (v + 1)
  | .none => return .good 0

def show' : R String → String
  | .bad e => s!"bad {e}"
  | .good v => s!"good {v}"
  | .none => "none"

def main (args : List String) : IO Unit := do
  let m := args.length
  for n in [0:16] do
    IO.println s!"{n}: {show' (g n m)} {show' (g n (m + 5))} {show' (h n m 20)} {show' (h n (m + 5) 3)}"
