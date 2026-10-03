/-! Runtime test: join-point shapes: a J2 join point with 13 parameters of
mixed layouts (u8, Nat, Bool, Float32, String, u16, Char, Int, Float, closure,
Option, Int8, Unit × Bool) in one value tuple; for loops with
continue/break/early return; nested loops with return; shadowing;
try/catch/finally in loops with return; while with compound conditions; an
Except loop with throw/break/continue.
From the round-7 review, area L (rv7/lowering), check 7 (LwJp1). -/

@[noinline] def manyMut (n : Nat) : IO Unit := do
  let mut a : UInt8 := 1
  let mut b : Nat := 2
  let mut c : Bool := false
  let mut d : Float32 := 1.5
  let mut e : String := ""
  let mut g : UInt16 := 7
  let mut h : Char := 'x'
  let mut i : Int := -3
  let mut j : Float := 2.5
  let mut k : Nat → Nat := id
  let mut l : Option UInt8 := none
  let mut m : Int8 := -1
  let mut o : Unit × Bool := ((), true)
  if n > 3 then
    a := a + 1; b := b + 2^64; c := true; d := d * 2; e := e ++ "x"; g := g - 8; h := 'y'
    i := i - 2^70; j := j / 0; k := (· + n); l := some 4; m := m - 127; o := ((), false)
  else if n == 2 then
    b := 0; e := "two"; k := (· * 2)
  IO.println s!"manyMut {n}: {a} {b} {c} {d} {e} {g} {h} {i} {j} {k 1} {l} {m} {o.2}"

@[noinline] def loopMut (xs : Array Nat) : IO (Nat × String × Float × Bool × UInt8) := do
  let mut s := 0
  let mut str := ""
  let mut f : Float := 0
  let mut flag := false
  let mut cnt : UInt8 := 250
  for x in xs do
    if x == 13 then continue
    if x > 1000 then
      flag := true
      break
    s := s + x
    if x % 3 == 0 then
      str := str.push 'a'
      f := f + x.toFloat / 3
    else if x % 3 == 1 then
      cnt := cnt + 1
      if cnt == 3 then return (s, "early", f, flag, cnt)
    else
      str := str ++ toString x
  return (s, str, f, flag, cnt)

def nestedFind (grid : Array (Array Nat)) (target : Nat) : Option (Nat × Nat) := Id.run do
  for i in [0:grid.size] do
    let row := grid[i]!
    for j in [0:row.size] do
      if row[j]! == target then return some (i, j)
      if row[j]! == 999 then break
  return none

@[noinline] def shadow (n : Nat) : IO Nat := do
  let mut x := 1
  for i in [0:n] do
    let x' := x + i
    let z := x' * 2
    if z > 1000 then
      IO.println s!"shadow big {z}"
    let y := z
    let z := y % 7
    x := x + z
    IO.println s!"shadow {i} {z}"
  for i in [0:n] do
    x := x + i
  return x

@[noinline] def tryLoop (n : Nat) : IO Nat := do
  let mut acc := 0
  for i in [0:n] do
    try
      if i % 3 == 2 then throw (IO.userError s!"e{i}")
      acc := acc + i
      if i == 7 then return acc * 100
    catch e =>
      IO.println s!"caught {e}"
      acc := acc + 1000
    finally
      IO.println s!"finally {i}"
  return acc

@[noinline] def whileLoop (n : Nat) : Nat := Id.run do
  let mut i := 0
  let mut a := 0
  let mut b := 1
  while i < n && (a < 1000000 || b % 2 == 0) do
    if (i % 3 == 0 && a % 5 != 1) || (i % 7 == 2 && b > 3) then
      a := a + b
    else if i % 11 == 0 || (a > 50 && b < 1000) then
      b := b * 2 % 9973
    else
      a := a + 1
      b := b + a % 13
    i := i + 1
  return a * 10000 + b

@[noinline] def exceptLoop (xs : List Int) : Except String Int := do
  let mut acc : Int := 0
  for x in xs do
    if x < -100 then throw s!"too small {x}"
    match x with
    | 0 => continue
    | 1 => acc := acc * 2
    | 2 => acc := acc - 2^65
    | _ => if acc > 10^30 then break else acc := acc + x
  return acc

def main : IO Unit := do
  for n in [0, 2, 5] do manyMut n
  IO.println s!"{← loopMut #[1, 2, 3, 13, 6, 7, 2000, 5]}"
  IO.println s!"{← loopMut #[4, 7, 10, 13, 16, 19, 22]}"
  IO.println s!"{← loopMut #[3, 6, 9]}"
  IO.println s!"{nestedFind #[#[1, 2], #[3, 999, 4], #[5, 4]] 4} {nestedFind #[#[1]] 7}"
  IO.println s!"{← shadow 5}"
  IO.println s!"{← tryLoop 5} {← tryLoop 10}"
  IO.println s!"{whileLoop 100} {whileLoop 100000}"
  IO.println s!"{repr (exceptLoop [1, 3, 0, 2, 5, 1])} {repr (exceptLoop [5, -200])} {repr (exceptLoop [7, 2, 1, 1, 1])}"

