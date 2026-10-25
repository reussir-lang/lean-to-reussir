/-! Runtime test: case splits on `Nat`, which under `--int-backend rcgmp`
are Reussir `match`es on the built-in integer (optimization `int-match`,
Lower/IntMatch): `0` and `n+1` (the `Nat::Succ` arm's binder is the
scrutinee minus one), nested splits of the field fused into one match
(`0`, `1`, `n+2`; `0`, `1`, `2`, `n+3`), chains of literal tests (`0`, `1`,
`5`, `_`; literals from 2^61 on, which are no immediates there) followed by
a default or by `n+1`, a literal tested before `0` and `n+1`, the
scrutinee named in each kind of arm (a literal arm, the `n+1` arm, which
then matches a copy, a default), used after the split, a test whose
result is used twice (not fused), tail recursion through `n+1` (a loop),
and two scrutinees (Ackermann). Inputs are immediates, the edges of
rcgmp's immediates (2^61 - 1, 2^61, 2^61 + 1), and heap values (2^62,
2^63, 2^64, 10^30); some are computed at run time from the number of
arguments, so no split is decided at compile time. Every line must equal
native Lean's, under both representations. -/

def sumTo : Nat → Nat
  | 0 => 0
  | n+1 => (n+1) + sumTo n

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)

def trib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n+3 => trib n + trib (n+1) + trib (n+2)

def ack : Nat → Nat → Nat
  | 0, n => n+1
  | m+1, 0 => ack m 1
  | m+1, n+1 => ack m (ack (m+1) n)

/-- `n+1` with the scrutinee named in the arm. -/
def keepN (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | k+1 => n * k + n

/-- The scrutinee named in a literal arm and in the default. -/
def namedLit (n : Nat) : Nat :=
  match n with
  | 0 => n + 7
  | 3 => n * 100
  | _ => n + 1

/-- Lean tests literals one by one (`Nat.decEq`): one match. -/
def lits (n : Nat) : String :=
  match n with
  | 0 => "zero"
  | 1 => "one"
  | 5 => "five"
  | 2305843009213693951 => "2^61-1"
  | 2305843009213693952 => "2^61"
  | 18446744073709551616 => "2^64"
  | 1000000000000000000000000000000 => "10^30"
  | _ => "other"

/-- A literal tested first, then `0` and `n+1`. -/
def litThenSucc (n : Nat) : Nat :=
  match n with
  | 5 => 500
  | 0 => 1000
  | k+1 => k

/-- `n+3` and literals around it. -/
def pred3 : Nat → Nat
  | 0 => 100
  | 1 => 101
  | 2 => 102
  | n+3 => n

/-- `if`s on `n = 0` and `n == 1` (`Nat.decEq`, `Nat.beq`). -/
def ifs (n : Nat) : Nat :=
  if n = 0 then 10 else if n == 1 then 11 else n - 2

/-- A test whose result is used twice: it stays a test. -/
def twice (n : Nat) : Bool × Nat :=
  let b := n == 4
  (b, if b then 40 else n)

/-- Used after the split. -/
def after (n : Nat) : Nat :=
  let p := match n with
    | 0 => 0
    | k+1 => k
  p + n

/-- Tail recursion through `n+1`: a loop. -/
def loop : Nat → Nat → Nat
  | 0, acc => acc
  | n+1, acc => loop n (acc + n)

/-- A short walk down through `n+1` from a heap value across 2^61. -/
def walk : Nat → Nat → List Nat
  | 0, _ => []
  | k+1, n => match n with
    | 0 => [0]
    | m+1 => n :: walk k m

/-- A default arm beside `0` (`| _ =>` after `| 0 =>`). -/
def zeroOr (n : Nat) : Nat :=
  match n with
  | 0 => 42
  | _ => n * 2

def main (args : List String) : IO Unit := do
  let b := args.length
  let small : List Nat := [b, b + 1, b + 2, b + 3, b + 4, b + 5, b + 6, b + 10]
  let p61 := 2 ^ (61 + b)
  let big : List Nat := [p61 - 1, p61, p61 + 1, 2 ^ (62 + b), 2 ^ (63 + b), 2 ^ (64 + b),
    10 ^ (30 + b), 2 ^ (64 + b) + 1, 10 ^ (30 + b) + 1, 10 ^ (30 + b) - 1]
  let all := small ++ big
  IO.println s!"sumTo {(small.map sumTo)} {sumTo (100 + b)}"
  IO.println s!"fib {small.map fib} {fib (25 + b)}"
  IO.println s!"trib {small.map trib}"
  IO.println s!"ack {ack 2 (3 + b)} {ack 3 (3 + b)} {ack (b + 1) 0}"
  IO.println s!"keepN {all.map keepN}"
  IO.println s!"namedLit {all.map namedLit}"
  IO.println s!"lits {all.map lits}"
  IO.println s!"litThenSucc {all.map litThenSucc}"
  IO.println s!"pred3 {all.map pred3}"
  IO.println s!"ifs {all.map ifs}"
  IO.println s!"twice {all.map twice}"
  IO.println s!"after {all.map after}"
  IO.println s!"loop {loop (1000 + b) 0} {loop (100000 + b) 7}"
  IO.println s!"walk {walk 5 (p61 + 2)} {walk 4 (2 ^ (64 + b))} {walk 3 (b + 1)}"
  IO.println s!"zeroOr {all.map zeroOr}"
