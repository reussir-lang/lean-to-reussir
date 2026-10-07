/-! Runtime test: float literals whose `Bool` flag Lean's simp replaced by a
discriminant. In `Float.ofScientific m s e` the flag `s` is the constructor
`Bool.true` or `Bool.false`. Inside the alternative `true` of `cases b`,
simp replaces a later `Bool.true` by `b` itself (`Simp.simpCtorDiscr?`), so
`2.5` (`Float.ofScientific 25 true 1`) becomes `Float.ofScientific 25 b 1`;
in the alternative `false`, `3e2` (`Float.ofScientific 3 false 2`) becomes
`Float.ofScientific 3 b 2`. If `Simp.simpJpCases?` then moves such an
alternative into a join point of its own, the flag is that join point's
parameter (`andJp`). Native Lean calls `Float.ofScientific` there at every
iteration; lean2rr folds each of these calls to its bits (`float-lits`).

Every function below has fast-path literals and slow-path literals (an
exponent above 22, or above 10 for `Float32`). The slow path goes through
`Float.Model` with big numbers and allocates: tests/runtime/alloc-check.sh
(RtFloatLitDiscr.alloc) checks that lean2rr's allocations do not grow with
N (a call left in the loop allocates at each iteration). The printed bits
depend on every literal. Argument: N (default 300). -/

-- `match` on a `Bool`, both flags, `Float`.
@[noinline] def stepF (b : Bool) (x : Float) : Float :=
  match b with
  | true => x * 2.5 + 1e-30
  | false => x * 3e2 + 1e30

-- The same for `Float32`.
@[noinline] def stepF32 (b : Bool) (x : Float32) : Float32 :=
  match b with
  | true => x * 0.375 + 1e-12
  | false => x * 7e1 + 1e12

-- One literal in both alternatives: in `true` its flag is `b`, in
-- `false` it stays the constructor `Bool.true`.
@[noinline] def both (b : Bool) (x : Float) : Float :=
  match b with
  | true => x * 0.1 + 1e-25
  | false => x - 0.1 - 1e-25

-- A wildcard alternative. In LCNF it is still the alternative `true`:
-- simp leaves no `.default` beside a single `Bool` alternative.
@[noinline] def wild (b : Bool) (x : Float32) : Float32 :=
  match b with
  | false => x + 3e2 + 1e15
  | _ => x * 0.2 + 1e-15

-- `x && y`: the `else` code is a join point, and both jumps to it pass a
-- variable that is `false` there; the flag of `2e3` and `1e30` is the join
-- point's parameter.
@[noinline] def andJp (x y : Bool) (a : Float) : Float :=
  if x && y then a + 0.5 + 1e-30 else a * 2e3 + 1e30

-- The loops: a `Bool` computed at each iteration (`if c`), and the
-- functions above on both values. The state is an unboxed `Float` or
-- `Float32` parameter, so a loop itself allocates nothing.
@[noinline] def loopF : Nat → Nat → Float → Float
  | 0, _, s => s
  | k + 1, i, s =>
    let b := i % 2 == 0
    let c := i % 3 == 0
    let x := i.toFloat
    let s := s + stepF b x + both c x + andJp b c x
    loopF k (i + 1) (if c then s + 0.25 + 1e-28 else s - 1e2 - 1e28)

@[noinline] def loopF32 : Nat → Nat → Float32 → Float32
  | 0, _, t => t
  | k + 1, i, t =>
    let x := i.toFloat.toFloat32
    loopF32 k (i + 1) (t + stepF32 (i % 3 == 0) x + wild (i % 2 == 0) x)

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 300
  for b in [true, false] do
    IO.println s!"{b} {(stepF b 1.0).toBits} {(stepF32 b 1.0).toBits} {(both b 1.0).toBits} {(wild b 1.0).toBits}"
  for (x, y) in [(true, true), (true, false), (false, true), (false, false)] do
    IO.println s!"{x} {y} {(andJp x y 1.0).toBits}"
  IO.println s!"{n} {(loopF n 0 0).toBits} {(loopF32 n 0 0).toBits}"
