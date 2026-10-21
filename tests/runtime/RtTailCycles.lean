/-! Runtime test: cycles of tail calls between declarations run in constant
stack, as natively, where native Lean's calls are sibling calls. lean2rr
runs such a cycle in one state machine with an entry per declaration
(J4, translation plan §5.6; `lowerGroup`): a tail call between them enters
it, and in it is a self tail call, a loop. As separate functions, two of these cycles used
stack per call (`.pipe`: 1 MiB of stack, one million calls):
- `io`, `ionat`, `except`: a result of several words (`flatten-structs`'
  tuple of `IO (Nat × String)`, of `IO Nat`, of `Except String Nat`): LLVM
  merged the returns into one block, so no call was a sibling call;
- `slots`: two state machines with different numbers of slots: a call needs
  more stack arguments than the caller has.
`three` is a cycle of three declarations, `nat` one with a one-word result
(a sibling call before too). The parameters are `UInt64`, or are passed
on owned: natively the calls are tail calls. -/

-- io: a multi-word result (the tuple of IO (Nat × String))
mutual
@[noinline] partial def ia (i n acc : UInt64) : IO (Nat × String) := do
  if i ≥ n then return (acc.toNat, "a")
  if i % 3 == 0 then return ← ib (i + 1) n (acc + 1)
  if i % 5 == 0 then return ← ia (i + 1) n (acc + 2)
  ib (i + 1) n ((acc * 3) % 1000003)
@[noinline] partial def ib (i n acc : UInt64) : IO (Nat × String) := do
  if i ≥ n then return (acc.toNat + 7, "b")
  if i % 7 == 0 then return ← ia (i + 1) n (acc + 3)
  ia (i + 1) n ((acc * 5) % 1000003)
end

-- ionat: IO loops that return a Nat (the tuple of IO Nat)
mutual
@[noinline] partial def ja (i n acc : UInt64) : IO Nat := do
  if i ≥ n then return acc.toNat
  if i % 250000 == 0 then IO.println s!"ionat at {i}"
  if i % 3 == 0 then jb (i + 1) n (acc + 1)
  else ja (i + 1) n ((acc * 3) % 1000003)
@[noinline] partial def jb (i n acc : UInt64) : IO Nat := do
  if i ≥ n then return acc.toNat + 7
  if i % 7 == 0 then ja (i + 1) n (acc + 3)
  else ja (i + 1) n ((acc * 5) % 1000003)
end

-- except: a multi-word result (the tuple of Except String Nat)
mutual
@[noinline] partial def ea (i n acc : UInt64) : Except String Nat :=
  if i ≥ n then .ok acc.toNat
  else if acc == 1000004 then .error "never"
  else if i % 3 == 0 then eb (i + 1) n (acc + 1)
  else if i % 5 == 0 then ea (i + 1) n (acc + 2)
  else eb (i + 1) n ((acc * 3) % 1000003)
@[noinline] partial def eb (i n acc : UInt64) : Except String Nat :=
  if i ≥ n then .ok (acc.toNat + 7)
  else if i % 7 == 0 then ea (i + 1) n (acc + 3)
  else ea (i + 1) n ((acc * 5) % 1000003)
end

-- three: a cycle of three declarations, results of three words
mutual
@[noinline] partial def ta (i n acc : UInt64) : Option (Nat × Bool) :=
  if i ≥ n then some (acc.toNat, true)
  else if i % 4 == 0 then tb (i + 1) n (acc + 1)
  else tc (i + 1) n ((acc * 3) % 1000003)
@[noinline] partial def tb (i n acc : UInt64) : Option (Nat × Bool) :=
  if i ≥ n then some (acc.toNat, false)
  else if acc == 1000004 then none
  else tc (i + 1) n ((acc * 5) % 1000003)
@[noinline] partial def tc (i n acc : UInt64) : Option (Nat × Bool) :=
  if i ≥ n then some (acc.toNat + 1, true)
  else if i % 3 == 0 then tc (i + 1) n (acc + 2)
  else ta (i + 1) n ((acc * 7) % 1000003)
end

-- nat: a one-word result
mutual
@[noinline] partial def na (i n acc : UInt64) : Nat :=
  if i ≥ n then acc.toNat
  else if i % 3 == 0 then nb (i + 1) n (acc + 1)
  else na (i + 1) n ((acc * 3) % 1000003)
@[noinline] partial def nb (i n acc : UInt64) : Nat :=
  if i ≥ n then acc.toNat + 7
  else na (i + 1) n ((acc * 5) % 1000003)
end

-- slots: two long IO functions (outlined join points, state machines); sa
-- keeps one Nat live across its join points, sb four
mutual
@[noinline] partial def sa (i n : Nat) (acc : Nat) (s : String) : IO (Nat × String) := do
  if i ≥ n then return (acc, s)
  let mut a := acc + 0
  let mut t := s
  if (i + 0) % 7 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 3 + i) % 1000003
  if (i + 1) % 8 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 4 + i) % 1000003
  if (i + 2) % 9 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 5 + i) % 1000003
  if (i + 3) % 10 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 6 + i) % 1000003
  if (i + 4) % 11 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 7 + i) % 1000003
  if (i + 5) % 12 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 8 + i) % 1000003
  if (i + 6) % 13 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 9 + i) % 1000003
  if (i + 7) % 14 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 10 + i) % 1000003
  if (i + 8) % 15 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 11 + i) % 1000003
  if (i + 9) % 16 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 12 + i) % 1000003
  if (i + 10) % 17 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 13 + i) % 1000003
  if (i * 10) % 13 == 10 then
    return ← sb (i + 1) n ((a) % 1000003) (if t.length > 20 then "" else t.push 'x')
  if (i * 10) % 17 == 10 then
    return ← sa (i + 1) n ((a) % 1000003 + 1) t
  if (i + 11) % 18 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 14 + i) % 1000003
  if (i + 12) % 19 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 15 + i) % 1000003
  if (i + 13) % 20 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 16 + i) % 1000003
  if (i + 14) % 21 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 17 + i) % 1000003
  if (i + 15) % 22 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 18 + i) % 1000003
  if (i + 16) % 23 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 19 + i) % 1000003
  if (i + 17) % 24 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 20 + i) % 1000003
  if (i + 18) % 25 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 21 + i) % 1000003
  if (i + 19) % 26 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 22 + i) % 1000003
  if (i + 20) % 27 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 23 + i) % 1000003
  if (i * 20) % 13 == 7 then
    return ← sb (i + 1) n ((a) % 1000003) (if t.length > 20 then "" else t.push 'x')
  if (i * 20) % 17 == 3 then
    return ← sa (i + 1) n ((a) % 1000003 + 1) t
  if (i + 21) % 28 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 24 + i) % 1000003
  if (i + 22) % 29 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 25 + i) % 1000003
  if (i + 23) % 30 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 26 + i) % 1000003
  if (i + 24) % 31 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 27 + i) % 1000003
  if (i + 25) % 32 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 28 + i) % 1000003
  if (i + 26) % 33 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 29 + i) % 1000003
  if (i + 27) % 34 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 30 + i) % 1000003
  if (i + 28) % 35 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 31 + i) % 1000003
  if (i + 29) % 36 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 32 + i) % 1000003
  sb (i + 1) n ((a) % 1000003) t
@[noinline] partial def sb (i n : Nat) (acc : Nat) (s : String) : IO (Nat × String) := do
  if i ≥ n then return (acc, s)
  let mut a := acc + 0
  let mut b := acc + 1
  let mut c := acc + 2
  let mut d := acc + 3
  let mut t := s
  if (i + 0) % 7 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 3 + i) % 1000003
  b := (b * 4 + i) % 1000003
  c := (c * 5 + i) % 1000003
  d := (d * 6 + i) % 1000003
  if (i + 1) % 8 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 4 + i) % 1000003
  b := (b * 5 + i) % 1000003
  c := (c * 6 + i) % 1000003
  d := (d * 7 + i) % 1000003
  if (i + 2) % 9 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 5 + i) % 1000003
  b := (b * 6 + i) % 1000003
  c := (c * 7 + i) % 1000003
  d := (d * 8 + i) % 1000003
  if (i + 3) % 10 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 6 + i) % 1000003
  b := (b * 7 + i) % 1000003
  c := (c * 8 + i) % 1000003
  d := (d * 9 + i) % 1000003
  if (i + 4) % 11 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 7 + i) % 1000003
  b := (b * 8 + i) % 1000003
  c := (c * 9 + i) % 1000003
  d := (d * 10 + i) % 1000003
  if (i + 5) % 12 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 8 + i) % 1000003
  b := (b * 9 + i) % 1000003
  c := (c * 10 + i) % 1000003
  d := (d * 11 + i) % 1000003
  if (i + 6) % 13 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 9 + i) % 1000003
  b := (b * 10 + i) % 1000003
  c := (c * 11 + i) % 1000003
  d := (d * 12 + i) % 1000003
  if (i + 7) % 14 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 10 + i) % 1000003
  b := (b * 11 + i) % 1000003
  c := (c * 12 + i) % 1000003
  d := (d * 13 + i) % 1000003
  if (i + 8) % 15 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 11 + i) % 1000003
  b := (b * 12 + i) % 1000003
  c := (c * 13 + i) % 1000003
  d := (d * 14 + i) % 1000003
  if (i + 9) % 16 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 12 + i) % 1000003
  b := (b * 13 + i) % 1000003
  c := (c * 14 + i) % 1000003
  d := (d * 15 + i) % 1000003
  if (i + 10) % 17 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 13 + i) % 1000003
  b := (b * 14 + i) % 1000003
  c := (c * 15 + i) % 1000003
  d := (d * 16 + i) % 1000003
  if (i * 10) % 13 == 10 then
    return ← sa (i + 1) n ((a + b + c + d) % 1000003) (if t.length > 20 then "" else t.push 'x')
  if (i * 10) % 17 == 10 then
    return ← sb (i + 1) n ((a + b + c + d) % 1000003 + 1) t
  if (i + 11) % 18 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 14 + i) % 1000003
  b := (b * 15 + i) % 1000003
  c := (c * 16 + i) % 1000003
  d := (d * 17 + i) % 1000003
  if (i + 12) % 19 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 15 + i) % 1000003
  b := (b * 16 + i) % 1000003
  c := (c * 17 + i) % 1000003
  d := (d * 18 + i) % 1000003
  if (i + 13) % 20 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 16 + i) % 1000003
  b := (b * 17 + i) % 1000003
  c := (c * 18 + i) % 1000003
  d := (d * 19 + i) % 1000003
  if (i + 14) % 21 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 17 + i) % 1000003
  b := (b * 18 + i) % 1000003
  c := (c * 19 + i) % 1000003
  d := (d * 20 + i) % 1000003
  if (i + 15) % 22 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 18 + i) % 1000003
  b := (b * 19 + i) % 1000003
  c := (c * 20 + i) % 1000003
  d := (d * 21 + i) % 1000003
  if (i + 16) % 23 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 19 + i) % 1000003
  b := (b * 20 + i) % 1000003
  c := (c * 21 + i) % 1000003
  d := (d * 22 + i) % 1000003
  if (i + 17) % 24 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 20 + i) % 1000003
  b := (b * 21 + i) % 1000003
  c := (c * 22 + i) % 1000003
  d := (d * 23 + i) % 1000003
  if (i + 18) % 25 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 21 + i) % 1000003
  b := (b * 22 + i) % 1000003
  c := (c * 23 + i) % 1000003
  d := (d * 24 + i) % 1000003
  if (i + 19) % 26 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 22 + i) % 1000003
  b := (b * 23 + i) % 1000003
  c := (c * 24 + i) % 1000003
  d := (d * 25 + i) % 1000003
  if (i + 20) % 27 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 23 + i) % 1000003
  b := (b * 24 + i) % 1000003
  c := (c * 25 + i) % 1000003
  d := (d * 26 + i) % 1000003
  if (i * 20) % 13 == 7 then
    return ← sa (i + 1) n ((a + b + c + d) % 1000003) (if t.length > 20 then "" else t.push 'x')
  if (i * 20) % 17 == 3 then
    return ← sb (i + 1) n ((a + b + c + d) % 1000003 + 1) t
  if (i + 21) % 28 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 24 + i) % 1000003
  b := (b * 25 + i) % 1000003
  c := (c * 26 + i) % 1000003
  d := (d * 27 + i) % 1000003
  if (i + 22) % 29 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 25 + i) % 1000003
  b := (b * 26 + i) % 1000003
  c := (c * 27 + i) % 1000003
  d := (d * 28 + i) % 1000003
  if (i + 23) % 30 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 26 + i) % 1000003
  b := (b * 27 + i) % 1000003
  c := (c * 28 + i) % 1000003
  d := (d * 29 + i) % 1000003
  if (i + 24) % 31 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 27 + i) % 1000003
  b := (b * 28 + i) % 1000003
  c := (c * 29 + i) % 1000003
  d := (d * 30 + i) % 1000003
  if (i + 25) % 32 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 28 + i) % 1000003
  b := (b * 29 + i) % 1000003
  c := (c * 30 + i) % 1000003
  d := (d * 31 + i) % 1000003
  if (i + 26) % 33 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 29 + i) % 1000003
  b := (b * 30 + i) % 1000003
  c := (c * 31 + i) % 1000003
  d := (d * 32 + i) % 1000003
  if (i + 27) % 34 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 30 + i) % 1000003
  b := (b * 31 + i) % 1000003
  c := (c * 32 + i) % 1000003
  d := (d * 33 + i) % 1000003
  if (i + 28) % 35 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 31 + i) % 1000003
  b := (b * 32 + i) % 1000003
  c := (c * 33 + i) % 1000003
  d := (d * 34 + i) % 1000003
  if (i + 29) % 36 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 32 + i) % 1000003
  b := (b * 33 + i) % 1000003
  c := (c * 34 + i) % 1000003
  d := (d * 35 + i) % 1000003
  sa (i + 1) n ((a + b + c + d) % 1000003) t
end

def main (args : List String) : IO Unit := do
  let mode := args.headD "all"
  let n := ((args.drop 1).head? >>= String.toNat?).getD 2000
  let go (m : String) : IO Unit := do
    match m with
    | "io" => let (a, s) ← ia 0 n.toUInt64 0; IO.println s!"io {a} {s}"
    | "ionat" => IO.println s!"ionat {← ja 0 n.toUInt64 0}"
    | "except" => IO.println s!"except {match ea 0 n.toUInt64 0 with | .ok v => toString v | .error e => e}"
    | "three" => IO.println s!"three {ta 0 n.toUInt64 0}"
    | "nat" => IO.println s!"nat {na 0 n.toUInt64 0}"
    | "slots" => let (a, s) ← sa 0 n 0 ""; IO.println s!"slots {a} {s}"
    | _ => IO.println s!"unknown mode {m}"
  if mode == "all" then
    for m in ["io", "ionat", "except", "three", "nat", "slots"] do go m
  else go mode
