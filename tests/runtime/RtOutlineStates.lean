/-! Runtime test: two long mutually recursive IO functions that lean2rr
outlines into parts and runs as one J4 state machine (translation plan §5.6,
88 variants), calling each other in tail position deep inside their bodies.
They run 300000 steps (`RtOutlineStates.args`; the original default was
2000), so a loop that grew the stack per step would show.
From the round-7 review, area L (rv7/lowering), check 9 (LwOutMut). -/

-- Two mutually recursive IO functions long enough to be outlined, calling each other in tail position deep inside
mutual
@[noinline] partial def fa (i n : Nat) (acc : Nat) (s : String) : IO (Nat × String) := do
  if i ≥ n then return (acc, s)
  let mut a := acc
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
    return ← fb (i + 1) n a (if t.length > 20 then "" else t.push 'x')
  if (i * 10) % 17 == 10 then
    return ← fa (i + 1) n (a + 1) t
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
  if (i * 25) % 13 == 12 then
    return ← fb (i + 1) n a (if t.length > 20 then "" else t.push 'x')
  if (i * 25) % 17 == 8 then
    return ← fa (i + 1) n (a + 1) t
  if (i + 26) % 33 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 29 + i) % 1000003
  if (i + 27) % 34 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 30 + i) % 1000003
  if (i + 28) % 35 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 31 + i) % 1000003
  if (i + 29) % 36 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 32 + i) % 1000003
  if (i + 30) % 37 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 33 + i) % 1000003
  if (i + 31) % 38 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 34 + i) % 1000003
  if (i + 32) % 39 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 35 + i) % 1000003
  if (i + 33) % 40 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 36 + i) % 1000003
  if (i + 34) % 41 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 37 + i) % 1000003
  if (i + 35) % 42 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 38 + i) % 1000003
  if (i + 36) % 43 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 39 + i) % 1000003
  if (i + 37) % 44 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 40 + i) % 1000003
  if (i + 38) % 45 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 41 + i) % 1000003
  if (i + 39) % 46 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 42 + i) % 1000003
  if (i + 40) % 47 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 43 + i) % 1000003
  if (i * 40) % 13 == 1 then
    return ← fb (i + 1) n a (if t.length > 20 then "" else t.push 'x')
  if (i * 40) % 17 == 6 then
    return ← fa (i + 1) n (a + 1) t
  if (i + 41) % 48 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 44 + i) % 1000003
  if (i + 42) % 49 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 45 + i) % 1000003
  if (i + 43) % 50 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 46 + i) % 1000003
  if (i + 44) % 51 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 47 + i) % 1000003
  fb (i + 1) n a t
@[noinline] partial def fb (i n : Nat) (acc : Nat) (s : String) : IO (Nat × String) := do
  if i ≥ n then return (acc, s)
  let mut a := acc
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
    return ← fa (i + 1) n a (if t.length > 20 then "" else t.push 'x')
  if (i * 10) % 17 == 10 then
    return ← fb (i + 1) n (a + 1) t
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
  if (i * 25) % 13 == 12 then
    return ← fa (i + 1) n a (if t.length > 20 then "" else t.push 'x')
  if (i * 25) % 17 == 8 then
    return ← fb (i + 1) n (a + 1) t
  if (i + 26) % 33 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 29 + i) % 1000003
  if (i + 27) % 34 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 30 + i) % 1000003
  if (i + 28) % 35 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 31 + i) % 1000003
  if (i + 29) % 36 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 32 + i) % 1000003
  if (i + 30) % 37 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 33 + i) % 1000003
  if (i + 31) % 38 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 34 + i) % 1000003
  if (i + 32) % 39 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 35 + i) % 1000003
  if (i + 33) % 40 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 36 + i) % 1000003
  if (i + 34) % 41 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 37 + i) % 1000003
  if (i + 35) % 42 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 38 + i) % 1000003
  if (i + 36) % 43 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 39 + i) % 1000003
  if (i + 37) % 44 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 40 + i) % 1000003
  if (i + 38) % 45 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 41 + i) % 1000003
  if (i + 39) % 46 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 42 + i) % 1000003
  if (i + 40) % 47 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 43 + i) % 1000003
  if (i * 40) % 13 == 1 then
    return ← fa (i + 1) n a (if t.length > 20 then "" else t.push 'x')
  if (i * 40) % 17 == 6 then
    return ← fb (i + 1) n (a + 1) t
  if (i + 41) % 48 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 44 + i) % 1000003
  if (i + 42) % 49 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 45 + i) % 1000003
  if (i + 43) % 50 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 46 + i) % 1000003
  if (i + 44) % 51 == 0 then IO.print (if t.length > 100000 then "!" else "")
  a := (a * 47 + i) % 1000003
  fa (i + 1) n a t
end
def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 2000
  let (a, s) ← fa 0 n 0 ""
  IO.println s!"{a} {s}"

