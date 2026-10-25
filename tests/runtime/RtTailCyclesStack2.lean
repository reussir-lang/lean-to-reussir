/-! Runtime test: a deep recursion that is not a tail call but passes a
tail call between two declarations of a cycle of tail calls at every
level, in a cycle with a big declaration. `walk2` calls `step2`
(`step2 (n - 1) .. + 1`, not a tail call), `step2` tail-calls `walk2`,
`walk2` tail-calls `heavy2` (48 live values, 13 parameters), and `heavy2`
tail-calls `step2`. lean2rr runs the cycle in one state machine
(translation plan §5.6), whose frame LLVM sizes for all its arms
(`heavy2`'s). When the tail call of `walk2` in `step2`'s own function
entered it, that frame was on the stack at every level of the recursion,
with `step2`'s: about 450 bytes per level instead of about 47, and 5000
levels overflowed a 1 MiB stack (`.pipe`), where native Lean (its main
stack) passes. Now `walk2` and `step2`, the light declarations of the
cycle, also run in a light state machine of their own (`lowerGroup`),
which their own functions' tail calls of each other enter; its tail calls
of `heavy2` enter the cycle's state machine (`.l2r-debug`: both). From the
review of fix-sm-mutual (2026-10-21; 100000 levels on an 8 MiB stack).
`loop`: a cycle of tail calls with two light declarations (`la`, `lb`)
and a heavy one (`lh`, eight parameters), a million calls on a 1 MiB
stack, entered at each declaration: the light state machine loops, its tail calls of `lh` enter
the cycle's state machine, which then runs the cycle (natively: sibling
calls, constant stack). -/

mutual
@[noinline] partial def walk2 (n : Nat) (acc : UInt64) : Nat :=
  if n == 0 then acc.toNat
  else if acc == 0xFFFFFFFFFFFF then heavy2 n acc 1 2 3 4 5 6 7 8 9 10 11
  else step2 (n - 1) (acc + 1) + 1
@[noinline] partial def step2 (n : Nat) (acc : UInt64) : Nat :=
  walk2 n (acc * 3 + 1)
@[noinline] partial def heavy2 (n : Nat) (acc a b c d e f g h i j k : UInt64) : Nat :=
  let x0 := acc * 3 + a
  let x1 := x0 * 5 + b
  let x2 := x1 * 7 + c
  let x3 := x2 * 9 + d
  let x4 := x3 * 11 + e
  let x5 := x4 * 13 + f
  let x6 := x5 * 15 + g
  let x7 := x6 * 17 + h
  let x8 := x7 * 19 + i
  let x9 := x8 * 21 + j
  let x10 := x9 * 23 + k
  let x11 := x10 * 25 + a
  let x12 := x11 * 27 + b
  let x13 := x12 * 29 + c
  let x14 := x13 * 31 + d
  let x15 := x14 * 33 + e
  let x16 := x15 * 35 + f
  let x17 := x16 * 37 + g
  let x18 := x17 * 39 + h
  let x19 := x18 * 41 + i
  let x20 := x19 * 43 + j
  let x21 := x20 * 45 + k
  let x22 := x21 * 47 + a
  let x23 := x22 * 49 + b
  let x24 := x23 * 51 + c
  let x25 := x24 * 53 + d
  let x26 := x25 * 55 + e
  let x27 := x26 * 57 + f
  let x28 := x27 * 59 + g
  let x29 := x28 * 61 + h
  let x30 := x29 * 63 + i
  let x31 := x30 * 65 + j
  let x32 := x31 * 67 + k
  let x33 := x32 * 69 + a
  let x34 := x33 * 71 + b
  let x35 := x34 * 73 + c
  let x36 := x35 * 75 + d
  let x37 := x36 * 77 + e
  let x38 := x37 * 79 + f
  let x39 := x38 * 81 + g
  let x40 := x39 * 83 + h
  let x41 := x40 * 85 + i
  let x42 := x41 * 87 + j
  let x43 := x42 * 89 + k
  let x44 := x43 * 91 + a
  let x45 := x44 * 93 + b
  let x46 := x45 * 95 + c
  let x47 := x46 * 97 + d
  let s := toString n
  let l := s.length.toUInt64
  let w := walk2 3 l
  step2 (n - 1) (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ x25 ^^^ x26 ^^^ x27 ^^^ x28 ^^^ x29 ^^^ x30 ^^^ x31 ^^^ x32 ^^^ x33 ^^^ x34 ^^^ x35 ^^^ x36 ^^^ x37 ^^^ x38 ^^^ x39 ^^^ x40 ^^^ x41 ^^^ x42 ^^^ x43 ^^^ x44 ^^^ x45 ^^^ x46 ^^^ x47 ^^^ l ^^^ w.toUInt64)
end

-- loop: light `la`, `lb` and heavy `lh` call each other in tail position only (their
-- arguments are `UInt64`s, eight at most, so that natively each call is a sibling call too)
mutual
@[noinline] partial def la (n acc : UInt64) : Nat :=
  if n == 0 then acc.toNat
  else if n % 1000 == 0 then lh n acc 1 2 3 4 5 6
  else lb (n - 1) (acc + 1)
@[noinline] partial def lb (n acc : UInt64) : Nat :=
  la n (acc * 3 % 1000003 + 1)
@[noinline] partial def lh (n acc a b c d e f : UInt64) : Nat :=
  let x0 := acc * 3 + a
  let x1 := x0 * 5 + b
  let x2 := x1 * 7 + c
  let x3 := x2 * 9 + d
  let x4 := x3 * 11 + e
  let x5 := x4 * 13 + f
  let x6 := x5 * 15 + a
  let x7 := x6 * 17 + b
  let x8 := x7 * 19 + c
  let x9 := x8 * 21 + d
  let x10 := x9 * 23 + e
  let x11 := x10 * 25 + f
  let x12 := x11 * 27 + a
  let x13 := x12 * 29 + b
  let x14 := x13 * 31 + c
  let x15 := x14 * 33 + d
  let x16 := x15 * 35 + e
  let x17 := x16 * 37 + f
  let x18 := x17 * 39 + a
  let x19 := x18 * 41 + b
  let x20 := x19 * 43 + c
  let x21 := x20 * 45 + d
  let x22 := x21 * 47 + e
  let x23 := x22 * 49 + f
  lb (n - 1) ((x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ x20 ^^^ x21 ^^^ x22 ^^^ x23) % 1000003)
end

def main (args : List String) : IO Unit := do
  match args with
  | ["loop", m] =>
    let n := m.toNat!.toUInt64
    IO.println s!"loop {la n 0} {lb n 5} {lh n 1 1 2 3 4 5 6}"
  | _ =>
    let n := (args.head? >>= String.toNat?).getD 1000
    IO.println s!"walk2 {walk2 n 0}"
    IO.println s!"heavy2 {heavy2 2 5 1 2 3 4 5 6 7 8 9 10 11}"
