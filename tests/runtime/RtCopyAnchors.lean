/-! Runtime test: functions that `inline-anchors` keeps out of rrc's inliner
for their copies (Emit/CopyAnchors; tests/runtime/inline-anchors-check.sh
checks the .rr under both representations of `Nat` and `Int`). Each case is
a 64-arm `match` on an enumeration, one function under both
representations:
- `sum3`: the arms call three mid-size functions (`p0`, `p1`, `p2`, about
  21 calls each). The copies of each one alone add less than the budget
  (4000), all three together more: the two that add the most are kept out,
  the third is left to the inliner.
- `viaWrap`: the arms call `wrap`, whose own code is a few operations but
  which calls the mid-size `big` once. rrc's inliner works bottom-up: it
  inlines `big` into `wrap` first, and then `wrap` is mid-size. `wrap` is
  kept out (its size counts `big`); `big` (one call) is not.
- `viaBuild`: the arms call `build`, which calls itself (a fresh list cell
  in its self call). rrc's unique-carrying specialization (`-O
  aggressive`) can turn its self calls into calls of a copy, and then
  inlines `build` itself. It is kept out like any other function.
- `viaMid`: the arms call `mid`, which calls `loop` (which calls itself)
  once. With `loop` counted, `mid` would be over the inliner's limit; rrc
  does not inline `loop` into it, so it inlines `mid` at every arm. The
  test whether rrc can inline `mid` leaves `loop` out, and `mid` is kept
  out.
- `fa`, `fb`, `fc`: a cycle of three functions in which `fb`'s arms call
  `fc`. The inliner refuses only a callee that calls itself or calls its
  caller back, so it inlines `fc` into every arm of `fb`; `fc` is kept
  out. -/

inductive CaS where
  | c0
  | c1
  | c2
  | c3
  | c4
  | c5
  | c6
  | c7
  | c8
  | c9
  | c10
  | c11
  | c12
  | c13
  | c14
  | c15
  | c16
  | c17
  | c18
  | c19
  | c20
  | c21
  | c22
  | c23
  | c24
  | c25
  | c26
  | c27
  | c28
  | c29
  | c30
  | c31
  | c32
  | c33
  | c34
  | c35
  | c36
  | c37
  | c38
  | c39
  | c40
  | c41
  | c42
  | c43
  | c44
  | c45
  | c46
  | c47
  | c48
  | c49
  | c50
  | c51
  | c52
  | c53
  | c54
  | c55
  | c56
  | c57
  | c58
  | c59
  | c60
  | c61
  | c62
  | c63
  deriving Inhabited

def sel (i : Nat) : CaS :=
  match i % 5 with
  | 0 => .c0
  | 1 => .c1
  | 2 => .c2
  | 3 => .c31
  | _ => .c63

@[noinline] def p0 (x0 : UInt64) : UInt64 := Id.run do
  let mut x := x0
  if x % 3 == 1 then x := x * 3 + 1 else x := (x >>> 1) ^^^ 1000
  if x % 4 == 1 then x := x * 5 + 2 else x := (x >>> 2) ^^^ 1001
  if x % 5 == 1 then x := x * 7 + 3 else x := (x >>> 3) ^^^ 1002
  if x % 6 == 1 then x := x * 9 + 4 else x := (x >>> 4) ^^^ 1003
  if x % 7 == 1 then x := x * 11 + 5 else x := (x >>> 5) ^^^ 1004
  if x % 8 == 1 then x := x * 13 + 6 else x := (x >>> 1) ^^^ 1005
  if x % 9 == 1 then x := x * 15 + 7 else x := (x >>> 2) ^^^ 1006
  if x % 10 == 1 then x := x * 17 + 8 else x := (x >>> 3) ^^^ 1007
  if x % 11 == 1 then x := x * 19 + 9 else x := (x >>> 4) ^^^ 1008
  if x % 12 == 1 then x := x * 21 + 10 else x := (x >>> 5) ^^^ 1009
  if x % 13 == 1 then x := x * 23 + 11 else x := (x >>> 1) ^^^ 1010
  if x % 14 == 1 then x := x * 25 + 12 else x := (x >>> 2) ^^^ 1011
  return x

@[noinline] def p1 (x0 : UInt64) : UInt64 := Id.run do
  let mut x := x0
  if x % 3 == 1 then x := x * 4 + 1 else x := (x >>> 1) ^^^ 1010
  if x % 4 == 1 then x := x * 6 + 2 else x := (x >>> 2) ^^^ 1011
  if x % 5 == 1 then x := x * 8 + 3 else x := (x >>> 3) ^^^ 1012
  if x % 6 == 1 then x := x * 10 + 4 else x := (x >>> 4) ^^^ 1013
  if x % 7 == 1 then x := x * 12 + 5 else x := (x >>> 5) ^^^ 1014
  if x % 8 == 1 then x := x * 14 + 6 else x := (x >>> 1) ^^^ 1015
  if x % 9 == 1 then x := x * 16 + 7 else x := (x >>> 2) ^^^ 1016
  if x % 10 == 1 then x := x * 18 + 8 else x := (x >>> 3) ^^^ 1017
  if x % 11 == 1 then x := x * 20 + 9 else x := (x >>> 4) ^^^ 1018
  if x % 12 == 1 then x := x * 22 + 10 else x := (x >>> 5) ^^^ 1019
  if x % 13 == 1 then x := x * 24 + 11 else x := (x >>> 1) ^^^ 1020
  if x % 14 == 1 then x := x * 26 + 12 else x := (x >>> 2) ^^^ 1021
  return x

@[noinline] def p2 (x0 : UInt64) : UInt64 := Id.run do
  let mut x := x0
  if x % 3 == 1 then x := x * 5 + 1 else x := (x >>> 1) ^^^ 1020
  if x % 4 == 1 then x := x * 7 + 2 else x := (x >>> 2) ^^^ 1021
  if x % 5 == 1 then x := x * 9 + 3 else x := (x >>> 3) ^^^ 1022
  if x % 6 == 1 then x := x * 11 + 4 else x := (x >>> 4) ^^^ 1023
  if x % 7 == 1 then x := x * 13 + 5 else x := (x >>> 5) ^^^ 1024
  if x % 8 == 1 then x := x * 15 + 6 else x := (x >>> 1) ^^^ 1025
  if x % 9 == 1 then x := x * 17 + 7 else x := (x >>> 2) ^^^ 1026
  if x % 10 == 1 then x := x * 19 + 8 else x := (x >>> 3) ^^^ 1027
  if x % 11 == 1 then x := x * 21 + 9 else x := (x >>> 4) ^^^ 1028
  if x % 12 == 1 then x := x * 23 + 10 else x := (x >>> 5) ^^^ 1029
  if x % 13 == 1 then x := x * 25 + 11 else x := (x >>> 1) ^^^ 1030
  if x % 14 == 1 then x := x * 27 + 12 else x := (x >>> 2) ^^^ 1031
  return x

@[noinline] def big (x0 : UInt64) : UInt64 := Id.run do
  let mut x := x0
  if x % 3 == 1 then x := x * 6 + 1 else x := (x >>> 1) ^^^ 1030
  if x % 4 == 1 then x := x * 8 + 2 else x := (x >>> 2) ^^^ 1031
  if x % 5 == 1 then x := x * 10 + 3 else x := (x >>> 3) ^^^ 1032
  if x % 6 == 1 then x := x * 12 + 4 else x := (x >>> 4) ^^^ 1033
  if x % 7 == 1 then x := x * 14 + 5 else x := (x >>> 5) ^^^ 1034
  if x % 8 == 1 then x := x * 16 + 6 else x := (x >>> 1) ^^^ 1035
  if x % 9 == 1 then x := x * 18 + 7 else x := (x >>> 2) ^^^ 1036
  if x % 10 == 1 then x := x * 20 + 8 else x := (x >>> 3) ^^^ 1037
  if x % 11 == 1 then x := x * 22 + 9 else x := (x >>> 4) ^^^ 1038
  if x % 12 == 1 then x := x * 24 + 10 else x := (x >>> 5) ^^^ 1039
  if x % 13 == 1 then x := x * 26 + 11 else x := (x >>> 1) ^^^ 1040
  if x % 14 == 1 then x := x * 28 + 12 else x := (x >>> 2) ^^^ 1041
  return x

@[noinline] def wrap (x : UInt64) : UInt64 := big (x + 1) + 2

@[noinline] def build (n : Nat) (acc : List UInt64) : List UInt64 :=
  match n with
  | 0 => acc
  | k+1 =>
    let a := k.toUInt64
    let b := if a % 3 == 1 then a * 7 + 1 else (a >>> 2) ^^^ 99
    let c := if b % 5 == 2 then b * 11 + 3 else (b >>> 3) ^^^ 1234
    let d := if c % 7 == 3 then c * 13 + 5 else (c >>> 1) ^^^ 4321
    let e := if d % 9 == 4 then d * 17 + 7 else (d >>> 4) ^^^ 777
    let f := if e % 11 == 5 then e * 19 + 9 else (e >>> 2) ^^^ 555
    let g := if f % 13 == 6 then f * 23 + 11 else (f >>> 3) ^^^ 333
    build k (g :: acc)

@[noinline] def loop (n : Nat) (x0 : UInt64) : UInt64 :=
  match n with
  | 0 => x0
  | k+1 => Id.run do
    let mut x := x0
    if x % 3 == 1 then x := x * 3 + 1 else x := (x >>> 1) ^^^ 3000
    if x % 4 == 1 then x := x * 5 + 2 else x := (x >>> 2) ^^^ 3001
    if x % 5 == 1 then x := x * 7 + 3 else x := (x >>> 3) ^^^ 3002
    if x % 6 == 1 then x := x * 9 + 4 else x := (x >>> 4) ^^^ 3003
    if x % 7 == 1 then x := x * 11 + 5 else x := (x >>> 5) ^^^ 3004
    if x % 8 == 1 then x := x * 13 + 6 else x := (x >>> 1) ^^^ 3005
    if x % 9 == 1 then x := x * 15 + 7 else x := (x >>> 2) ^^^ 3006
    if x % 10 == 1 then x := x * 17 + 8 else x := (x >>> 3) ^^^ 3007
    if x % 11 == 1 then x := x * 19 + 9 else x := (x >>> 4) ^^^ 3008
    if x % 12 == 1 then x := x * 21 + 10 else x := (x >>> 5) ^^^ 3009
    if x % 13 == 1 then x := x * 23 + 11 else x := (x >>> 1) ^^^ 3010
    if x % 14 == 1 then x := x * 25 + 12 else x := (x >>> 2) ^^^ 3011
    if x % 15 == 1 then x := x * 27 + 13 else x := (x >>> 3) ^^^ 3012
    if x % 16 == 1 then x := x * 29 + 14 else x := (x >>> 4) ^^^ 3013
    return loop k x

@[noinline] def mid (x0 : UInt64) : UInt64 := Id.run do
  let mut x := x0
  if x % 5 == 2 then x := x * 5 + 7 else x := (x >>> 1) ^^^ 2000
  if x % 6 == 2 then x := x * 7 + 8 else x := (x >>> 2) ^^^ 2001
  if x % 7 == 2 then x := x * 9 + 9 else x := (x >>> 3) ^^^ 2002
  if x % 8 == 2 then x := x * 11 + 10 else x := (x >>> 4) ^^^ 2003
  if x % 9 == 2 then x := x * 13 + 11 else x := (x >>> 1) ^^^ 2004
  if x % 10 == 2 then x := x * 15 + 12 else x := (x >>> 2) ^^^ 2005
  return loop 3 x

mutual
@[noinline] partial def fa (n : Nat) (x : UInt64) : UInt64 :=
  if n == 0 then x else fb (n - 1) (sel (n + 7)) x + 1
@[noinline] partial def fb (n : Nat) (s : CaS) (x : UInt64) : UInt64 :=
  match s with
  | .c0 => fc n (x + 0) + 0
  | .c1 => fc n (x + 1) + 1
  | .c2 => fc n (x + 2) + 2
  | .c3 => fc n (x + 3) + 3
  | .c4 => fc n (x + 4) + 4
  | .c5 => fc n (x + 5) + 5
  | .c6 => fc n (x + 6) + 6
  | .c7 => fc n (x + 7) + 7
  | .c8 => fc n (x + 8) + 8
  | .c9 => fc n (x + 9) + 9
  | .c10 => fc n (x + 10) + 10
  | .c11 => fc n (x + 11) + 11
  | .c12 => fc n (x + 12) + 12
  | .c13 => fc n (x + 13) + 13
  | .c14 => fc n (x + 14) + 14
  | .c15 => fc n (x + 15) + 15
  | .c16 => fc n (x + 16) + 16
  | .c17 => fc n (x + 17) + 17
  | .c18 => fc n (x + 18) + 18
  | .c19 => fc n (x + 19) + 19
  | .c20 => fc n (x + 20) + 20
  | .c21 => fc n (x + 21) + 21
  | .c22 => fc n (x + 22) + 22
  | .c23 => fc n (x + 23) + 23
  | .c24 => fc n (x + 24) + 24
  | .c25 => fc n (x + 25) + 25
  | .c26 => fc n (x + 26) + 26
  | .c27 => fc n (x + 27) + 27
  | .c28 => fc n (x + 28) + 28
  | .c29 => fc n (x + 29) + 29
  | .c30 => fc n (x + 30) + 30
  | .c31 => fc n (x + 31) + 31
  | .c32 => fc n (x + 32) + 32
  | .c33 => fc n (x + 33) + 33
  | .c34 => fc n (x + 34) + 34
  | .c35 => fc n (x + 35) + 35
  | .c36 => fc n (x + 36) + 36
  | .c37 => fc n (x + 37) + 37
  | .c38 => fc n (x + 38) + 38
  | .c39 => fc n (x + 39) + 39
  | .c40 => fc n (x + 40) + 40
  | .c41 => fc n (x + 41) + 41
  | .c42 => fc n (x + 42) + 42
  | .c43 => fc n (x + 43) + 43
  | .c44 => fc n (x + 44) + 44
  | .c45 => fc n (x + 45) + 45
  | .c46 => fc n (x + 46) + 46
  | .c47 => fc n (x + 47) + 47
  | .c48 => fc n (x + 48) + 48
  | .c49 => fc n (x + 49) + 49
  | .c50 => fc n (x + 50) + 50
  | .c51 => fc n (x + 51) + 51
  | .c52 => fc n (x + 52) + 52
  | .c53 => fc n (x + 53) + 53
  | .c54 => fc n (x + 54) + 54
  | .c55 => fc n (x + 55) + 55
  | .c56 => fc n (x + 56) + 56
  | .c57 => fc n (x + 57) + 57
  | .c58 => fc n (x + 58) + 58
  | .c59 => fc n (x + 59) + 59
  | .c60 => fc n (x + 60) + 60
  | .c61 => fc n (x + 61) + 61
  | .c62 => fc n (x + 62) + 62
  | .c63 => fc n (x + 63) + 63
@[noinline] partial def fc (n : Nat) (x0 : UInt64) : UInt64 := Id.run do
  let mut x := x0
  if x % 3 == 1 then x := x * 3 + 1 else x := (x >>> 1) ^^^ 1000
  if x % 4 == 1 then x := x * 5 + 2 else x := (x >>> 2) ^^^ 1001
  if x % 5 == 1 then x := x * 7 + 3 else x := (x >>> 3) ^^^ 1002
  if x % 6 == 1 then x := x * 9 + 4 else x := (x >>> 4) ^^^ 1003
  if x % 7 == 1 then x := x * 11 + 5 else x := (x >>> 5) ^^^ 1004
  if x % 8 == 1 then x := x * 13 + 6 else x := (x >>> 1) ^^^ 1005
  if x % 9 == 1 then x := x * 15 + 7 else x := (x >>> 2) ^^^ 1006
  if x % 10 == 1 then x := x * 17 + 8 else x := (x >>> 3) ^^^ 1007
  if x % 11 == 1 then x := x * 19 + 9 else x := (x >>> 4) ^^^ 1008
  if x % 12 == 1 then x := x * 21 + 10 else x := (x >>> 5) ^^^ 1009
  if x % 13 == 1 then x := x * 23 + 11 else x := (x >>> 1) ^^^ 1010
  return fa n x
end

@[noinline] def sum3 (s : CaS) (x : UInt64) : UInt64 :=
  match s with
  | .c0 => p0 (x + 0)
  | .c1 => p1 (x + 1)
  | .c2 => p2 (x + 2)
  | .c3 => p0 (x + 3)
  | .c4 => p1 (x + 4)
  | .c5 => p2 (x + 5)
  | .c6 => p0 (x + 6)
  | .c7 => p1 (x + 7)
  | .c8 => p2 (x + 8)
  | .c9 => p0 (x + 9)
  | .c10 => p1 (x + 10)
  | .c11 => p2 (x + 11)
  | .c12 => p0 (x + 12)
  | .c13 => p1 (x + 13)
  | .c14 => p2 (x + 14)
  | .c15 => p0 (x + 15)
  | .c16 => p1 (x + 16)
  | .c17 => p2 (x + 17)
  | .c18 => p0 (x + 18)
  | .c19 => p1 (x + 19)
  | .c20 => p2 (x + 20)
  | .c21 => p0 (x + 21)
  | .c22 => p1 (x + 22)
  | .c23 => p2 (x + 23)
  | .c24 => p0 (x + 24)
  | .c25 => p1 (x + 25)
  | .c26 => p2 (x + 26)
  | .c27 => p0 (x + 27)
  | .c28 => p1 (x + 28)
  | .c29 => p2 (x + 29)
  | .c30 => p0 (x + 30)
  | .c31 => p1 (x + 31)
  | .c32 => p2 (x + 32)
  | .c33 => p0 (x + 33)
  | .c34 => p1 (x + 34)
  | .c35 => p2 (x + 35)
  | .c36 => p0 (x + 36)
  | .c37 => p1 (x + 37)
  | .c38 => p2 (x + 38)
  | .c39 => p0 (x + 39)
  | .c40 => p1 (x + 40)
  | .c41 => p2 (x + 41)
  | .c42 => p0 (x + 42)
  | .c43 => p1 (x + 43)
  | .c44 => p2 (x + 44)
  | .c45 => p0 (x + 45)
  | .c46 => p1 (x + 46)
  | .c47 => p2 (x + 47)
  | .c48 => p0 (x + 48)
  | .c49 => p1 (x + 49)
  | .c50 => p2 (x + 50)
  | .c51 => p0 (x + 51)
  | .c52 => p1 (x + 52)
  | .c53 => p2 (x + 53)
  | .c54 => p0 (x + 54)
  | .c55 => p1 (x + 55)
  | .c56 => p2 (x + 56)
  | .c57 => p0 (x + 57)
  | .c58 => p1 (x + 58)
  | .c59 => p2 (x + 59)
  | .c60 => p0 (x + 60)
  | .c61 => p1 (x + 61)
  | .c62 => p2 (x + 62)
  | .c63 => p0 (x + 63)

@[noinline] def viaWrap (s : CaS) (x : UInt64) : UInt64 :=
  match s with
  | .c0 => wrap (x + 0)
  | .c1 => wrap (x + 1)
  | .c2 => wrap (x + 2)
  | .c3 => wrap (x + 3)
  | .c4 => wrap (x + 4)
  | .c5 => wrap (x + 5)
  | .c6 => wrap (x + 6)
  | .c7 => wrap (x + 7)
  | .c8 => wrap (x + 8)
  | .c9 => wrap (x + 9)
  | .c10 => wrap (x + 10)
  | .c11 => wrap (x + 11)
  | .c12 => wrap (x + 12)
  | .c13 => wrap (x + 13)
  | .c14 => wrap (x + 14)
  | .c15 => wrap (x + 15)
  | .c16 => wrap (x + 16)
  | .c17 => wrap (x + 17)
  | .c18 => wrap (x + 18)
  | .c19 => wrap (x + 19)
  | .c20 => wrap (x + 20)
  | .c21 => wrap (x + 21)
  | .c22 => wrap (x + 22)
  | .c23 => wrap (x + 23)
  | .c24 => wrap (x + 24)
  | .c25 => wrap (x + 25)
  | .c26 => wrap (x + 26)
  | .c27 => wrap (x + 27)
  | .c28 => wrap (x + 28)
  | .c29 => wrap (x + 29)
  | .c30 => wrap (x + 30)
  | .c31 => wrap (x + 31)
  | .c32 => wrap (x + 32)
  | .c33 => wrap (x + 33)
  | .c34 => wrap (x + 34)
  | .c35 => wrap (x + 35)
  | .c36 => wrap (x + 36)
  | .c37 => wrap (x + 37)
  | .c38 => wrap (x + 38)
  | .c39 => wrap (x + 39)
  | .c40 => wrap (x + 40)
  | .c41 => wrap (x + 41)
  | .c42 => wrap (x + 42)
  | .c43 => wrap (x + 43)
  | .c44 => wrap (x + 44)
  | .c45 => wrap (x + 45)
  | .c46 => wrap (x + 46)
  | .c47 => wrap (x + 47)
  | .c48 => wrap (x + 48)
  | .c49 => wrap (x + 49)
  | .c50 => wrap (x + 50)
  | .c51 => wrap (x + 51)
  | .c52 => wrap (x + 52)
  | .c53 => wrap (x + 53)
  | .c54 => wrap (x + 54)
  | .c55 => wrap (x + 55)
  | .c56 => wrap (x + 56)
  | .c57 => wrap (x + 57)
  | .c58 => wrap (x + 58)
  | .c59 => wrap (x + 59)
  | .c60 => wrap (x + 60)
  | .c61 => wrap (x + 61)
  | .c62 => wrap (x + 62)
  | .c63 => wrap (x + 63)

@[noinline] def viaBuild (s : CaS) (x : Nat) : List UInt64 :=
  match s with
  | .c0 => build (x + 0) []
  | .c1 => build (x + 1) []
  | .c2 => build (x + 2) []
  | .c3 => build (x + 3) []
  | .c4 => build (x + 4) []
  | .c5 => build (x + 5) []
  | .c6 => build (x + 6) []
  | .c7 => build (x + 7) []
  | .c8 => build (x + 8) []
  | .c9 => build (x + 0) []
  | .c10 => build (x + 1) []
  | .c11 => build (x + 2) []
  | .c12 => build (x + 3) []
  | .c13 => build (x + 4) []
  | .c14 => build (x + 5) []
  | .c15 => build (x + 6) []
  | .c16 => build (x + 7) []
  | .c17 => build (x + 8) []
  | .c18 => build (x + 0) []
  | .c19 => build (x + 1) []
  | .c20 => build (x + 2) []
  | .c21 => build (x + 3) []
  | .c22 => build (x + 4) []
  | .c23 => build (x + 5) []
  | .c24 => build (x + 6) []
  | .c25 => build (x + 7) []
  | .c26 => build (x + 8) []
  | .c27 => build (x + 0) []
  | .c28 => build (x + 1) []
  | .c29 => build (x + 2) []
  | .c30 => build (x + 3) []
  | .c31 => build (x + 4) []
  | .c32 => build (x + 5) []
  | .c33 => build (x + 6) []
  | .c34 => build (x + 7) []
  | .c35 => build (x + 8) []
  | .c36 => build (x + 0) []
  | .c37 => build (x + 1) []
  | .c38 => build (x + 2) []
  | .c39 => build (x + 3) []
  | .c40 => build (x + 4) []
  | .c41 => build (x + 5) []
  | .c42 => build (x + 6) []
  | .c43 => build (x + 7) []
  | .c44 => build (x + 8) []
  | .c45 => build (x + 0) []
  | .c46 => build (x + 1) []
  | .c47 => build (x + 2) []
  | .c48 => build (x + 3) []
  | .c49 => build (x + 4) []
  | .c50 => build (x + 5) []
  | .c51 => build (x + 6) []
  | .c52 => build (x + 7) []
  | .c53 => build (x + 8) []
  | .c54 => build (x + 0) []
  | .c55 => build (x + 1) []
  | .c56 => build (x + 2) []
  | .c57 => build (x + 3) []
  | .c58 => build (x + 4) []
  | .c59 => build (x + 5) []
  | .c60 => build (x + 6) []
  | .c61 => build (x + 7) []
  | .c62 => build (x + 8) []
  | .c63 => build (x + 0) []

@[noinline] def viaMid (s : CaS) (x : UInt64) : UInt64 :=
  match s with
  | .c0 => mid (x + 0)
  | .c1 => mid (x + 1)
  | .c2 => mid (x + 2)
  | .c3 => mid (x + 3)
  | .c4 => mid (x + 4)
  | .c5 => mid (x + 5)
  | .c6 => mid (x + 6)
  | .c7 => mid (x + 7)
  | .c8 => mid (x + 8)
  | .c9 => mid (x + 9)
  | .c10 => mid (x + 10)
  | .c11 => mid (x + 11)
  | .c12 => mid (x + 12)
  | .c13 => mid (x + 13)
  | .c14 => mid (x + 14)
  | .c15 => mid (x + 15)
  | .c16 => mid (x + 16)
  | .c17 => mid (x + 17)
  | .c18 => mid (x + 18)
  | .c19 => mid (x + 19)
  | .c20 => mid (x + 20)
  | .c21 => mid (x + 21)
  | .c22 => mid (x + 22)
  | .c23 => mid (x + 23)
  | .c24 => mid (x + 24)
  | .c25 => mid (x + 25)
  | .c26 => mid (x + 26)
  | .c27 => mid (x + 27)
  | .c28 => mid (x + 28)
  | .c29 => mid (x + 29)
  | .c30 => mid (x + 30)
  | .c31 => mid (x + 31)
  | .c32 => mid (x + 32)
  | .c33 => mid (x + 33)
  | .c34 => mid (x + 34)
  | .c35 => mid (x + 35)
  | .c36 => mid (x + 36)
  | .c37 => mid (x + 37)
  | .c38 => mid (x + 38)
  | .c39 => mid (x + 39)
  | .c40 => mid (x + 40)
  | .c41 => mid (x + 41)
  | .c42 => mid (x + 42)
  | .c43 => mid (x + 43)
  | .c44 => mid (x + 44)
  | .c45 => mid (x + 45)
  | .c46 => mid (x + 46)
  | .c47 => mid (x + 47)
  | .c48 => mid (x + 48)
  | .c49 => mid (x + 49)
  | .c50 => mid (x + 50)
  | .c51 => mid (x + 51)
  | .c52 => mid (x + 52)
  | .c53 => mid (x + 53)
  | .c54 => mid (x + 54)
  | .c55 => mid (x + 55)
  | .c56 => mid (x + 56)
  | .c57 => mid (x + 57)
  | .c58 => mid (x + 58)
  | .c59 => mid (x + 59)
  | .c60 => mid (x + 60)
  | .c61 => mid (x + 61)
  | .c62 => mid (x + 62)
  | .c63 => mid (x + 63)

def main : IO Unit := do
  let mut a : UInt64 := 0
  let mut b : UInt64 := 0
  let mut c : Nat := 0
  for i in [0:50] do
    a := a + sum3 (sel i) i.toUInt64
    b := b ^^^ viaWrap (sel (i + 1)) (i * 7).toUInt64
    c := c + ((viaBuild (sel (i + 2)) (i % 4)).foldl (· + ·) 0).toNat
  IO.println s!"sum3 {a}"
  IO.println s!"viaWrap {b}"
  IO.println s!"viaBuild {c}"
  let mut d : UInt64 := 0
  let mut e : UInt64 := 0
  for i in [0:50] do
    d := d + viaMid (sel (i + 3)) i.toUInt64
    e := e ^^^ fa (i % 4) (i * 3).toUInt64
  IO.println s!"viaMid {d}"
  IO.println s!"cycle {e}"
