/-! Runtime test: small join points that jump to other small join points
(translation plan §5.6, J1'). lean2rr inlines a small join point at each of
its jumps when its copy, with the join points inlined into it, stays within
a budget.

- `run`: a sequence of `match`es on a two-constructor state, each
  alternative setting the next state to a constant. Lean compiles each
  alternative to a join point that jumps to an alternative of the next
  `match` (either one), so the join points form a chain of siblings, each
  jumped to from both join points of the step before (sinking cannot nest
  them). Every one is small: when only a join point's own body was bounded,
  the first ones held 2^n copies of the last ones (20 steps: out of memory;
  16 steps: 143 MB of .rr).
- `skipWs`: a scanner loop whose per-character code is an outlined join
  point; the join points inlined into it make the self tail call, so the
  loop is one state machine (J4), not mutually recursive. -/

inductive S where
  | a | b

@[noinline] def run (x0 : Nat) : Nat := Id.run do
  let mut s := if x0 % 2 == 0 then S.a else S.b
  let mut x := x0
  match s with
  | .a => x := x + 1; if x % 3 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 0; if x % 5 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 2; if x % 4 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 1; if x % 6 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 3; if x % 5 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 2; if x % 7 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 4; if x % 6 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 3; if x % 8 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 5; if x % 7 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 4; if x % 9 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 6; if x % 8 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 5; if x % 10 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 7; if x % 9 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 6; if x % 11 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 8; if x % 10 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 7; if x % 12 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 9; if x % 11 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 8; if x % 13 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 10; if x % 12 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 9; if x % 14 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 11; if x % 13 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 10; if x % 15 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 12; if x % 14 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 11; if x % 16 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 13; if x % 15 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 12; if x % 17 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 14; if x % 16 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 13; if x % 18 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 15; if x % 17 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 14; if x % 19 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 16; if x % 18 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 15; if x % 20 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 17; if x % 19 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 16; if x % 21 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 18; if x % 20 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 17; if x % 22 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 19; if x % 21 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 18; if x % 23 == 0 then s := .b else s := .a
  match s with
  | .a => x := x + 20; if x % 22 == 0 then s := .a else s := .b
  | .b => x := x * 2 + 19; if x % 24 == 0 then s := .b else s := .a
  match s with
  | .a => return x
  | .b => return x + 1000

@[noinline] partial def skipWs (s : String) (i : String.Pos.Raw) (n : Nat) : Nat :=
  if i.byteIdx < s.utf8ByteSize then
    let c := i.get s
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then skipWs s (i.next s) (n + 1)
    else if c.isAlpha || c.isDigit || c == '_' || c == '\'' then skipWs s (i.next s) n
    else n
  else n

def main : IO Unit := do
  for i in [0:16] do
    IO.println s!"run {i} = {run i}"
  let mut sum := 0
  for i in [0:100000] do
    sum := sum + run i
  IO.println s!"sum = {sum}"
  let s := String.ofList ((List.range 1000000).map fun i =>
    if i % 5 == 0 then ' ' else if i % 7 == 0 then '_' else Char.ofNat (97 + i % 26))
  IO.println s!"skipWs = {skipWs s 0 0}"
  IO.println s!"skipWs stops = {skipWs (s ++ "+" ++ s) 0 0}"
  IO.println s!"skipWs tabs = {skipWs "\t\n\r x1_'y" 0 0}"
