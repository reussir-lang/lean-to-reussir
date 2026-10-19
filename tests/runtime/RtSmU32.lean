/-! Runtime test: a state machine with more than 256 variants, whose entry
point is a `u32` (optional pass `state-machines`; up to 256 variants it is
a `u8`). `big` dispatches on 260 cases; each case computes an `Option`
through a compound condition, which makes a join point with two jumps, and
continues the loop from it, so each case is one outlined join point and one
variant of `big`'s state machine (261 with the entry). `mkFn`, a small
state machine whose result is a function (eta-expanded by Lean), keeps a
`u8` entry point. `jp-small` is off (RtSmU32.opts): it would copy the small
join points to their jumps, and no state machine would be left. The cases
are generated (one block per `k` in 0..259, the same five lines with the
numbers changed). tests/runtime/sm-slots-check.sh checks the entry points'
types and the arms of the matches. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- A loop whose dispatch has one join point per case: more than 256 variants. -/
partial def big (n : Nat) (i : Nat) (acc : Nat) : Nat :=
  if i ≥ n then acc else
  let c := (i * 7 + acc) % 260
  if c == 0 then
    let r := if acc % 4 == 0 then some (acc + 0) else if acc == 77777777 then none else some (acc * 3 % 1000003 + 0)
    match r with
    | none => acc + i * 1
    | some y => big n (i + 1) (y % 1000003)
  else if c == 1 then
    let r := if acc % 4 == 1 then some (acc + 1) else if acc == 77777778 then none else some (acc * 3 % 1000003 + 1)
    match r with
    | none => acc + i * 2
    | some y => big n (i + 1) (y % 1000003)
  else if c == 2 then
    let r := if acc % 4 == 2 then some (acc + 2) else if acc == 77777779 then none else some (acc * 3 % 1000003 + 2)
    match r with
    | none => acc + i * 3
    | some y => big n (i + 1) (y % 1000003)
  else if c == 3 then
    let r := if acc % 4 == 3 then some (acc + 3) else if acc == 77777780 then none else some (acc * 3 % 1000003 + 3)
    match r with
    | none => acc + i * 4
    | some y => big n (i + 1) (y % 1000003)
  else if c == 4 then
    let r := if acc % 4 == 0 then some (acc + 4) else if acc == 77777781 then none else some (acc * 3 % 1000003 + 4)
    match r with
    | none => acc + i * 5
    | some y => big n (i + 1) (y % 1000003)
  else if c == 5 then
    let r := if acc % 4 == 1 then some (acc + 5) else if acc == 77777782 then none else some (acc * 3 % 1000003 + 5)
    match r with
    | none => acc + i * 6
    | some y => big n (i + 1) (y % 1000003)
  else if c == 6 then
    let r := if acc % 4 == 2 then some (acc + 6) else if acc == 77777783 then none else some (acc * 3 % 1000003 + 6)
    match r with
    | none => acc + i * 7
    | some y => big n (i + 1) (y % 1000003)
  else if c == 7 then
    let r := if acc % 4 == 3 then some (acc + 7) else if acc == 77777784 then none else some (acc * 3 % 1000003 + 7)
    match r with
    | none => acc + i * 8
    | some y => big n (i + 1) (y % 1000003)
  else if c == 8 then
    let r := if acc % 4 == 0 then some (acc + 8) else if acc == 77777785 then none else some (acc * 3 % 1000003 + 8)
    match r with
    | none => acc + i * 9
    | some y => big n (i + 1) (y % 1000003)
  else if c == 9 then
    let r := if acc % 4 == 1 then some (acc + 9) else if acc == 77777786 then none else some (acc * 3 % 1000003 + 9)
    match r with
    | none => acc + i * 10
    | some y => big n (i + 1) (y % 1000003)
  else if c == 10 then
    let r := if acc % 4 == 2 then some (acc + 10) else if acc == 77777787 then none else some (acc * 3 % 1000003 + 10)
    match r with
    | none => acc + i * 11
    | some y => big n (i + 1) (y % 1000003)
  else if c == 11 then
    let r := if acc % 4 == 3 then some (acc + 11) else if acc == 77777788 then none else some (acc * 3 % 1000003 + 11)
    match r with
    | none => acc + i * 12
    | some y => big n (i + 1) (y % 1000003)
  else if c == 12 then
    let r := if acc % 4 == 0 then some (acc + 12) else if acc == 77777789 then none else some (acc * 3 % 1000003 + 12)
    match r with
    | none => acc + i * 13
    | some y => big n (i + 1) (y % 1000003)
  else if c == 13 then
    let r := if acc % 4 == 1 then some (acc + 13) else if acc == 77777790 then none else some (acc * 3 % 1000003 + 13)
    match r with
    | none => acc + i * 14
    | some y => big n (i + 1) (y % 1000003)
  else if c == 14 then
    let r := if acc % 4 == 2 then some (acc + 14) else if acc == 77777791 then none else some (acc * 3 % 1000003 + 14)
    match r with
    | none => acc + i * 15
    | some y => big n (i + 1) (y % 1000003)
  else if c == 15 then
    let r := if acc % 4 == 3 then some (acc + 15) else if acc == 77777792 then none else some (acc * 3 % 1000003 + 15)
    match r with
    | none => acc + i * 16
    | some y => big n (i + 1) (y % 1000003)
  else if c == 16 then
    let r := if acc % 4 == 0 then some (acc + 16) else if acc == 77777793 then none else some (acc * 3 % 1000003 + 16)
    match r with
    | none => acc + i * 17
    | some y => big n (i + 1) (y % 1000003)
  else if c == 17 then
    let r := if acc % 4 == 1 then some (acc + 17) else if acc == 77777794 then none else some (acc * 3 % 1000003 + 17)
    match r with
    | none => acc + i * 18
    | some y => big n (i + 1) (y % 1000003)
  else if c == 18 then
    let r := if acc % 4 == 2 then some (acc + 18) else if acc == 77777795 then none else some (acc * 3 % 1000003 + 18)
    match r with
    | none => acc + i * 19
    | some y => big n (i + 1) (y % 1000003)
  else if c == 19 then
    let r := if acc % 4 == 3 then some (acc + 19) else if acc == 77777796 then none else some (acc * 3 % 1000003 + 19)
    match r with
    | none => acc + i * 20
    | some y => big n (i + 1) (y % 1000003)
  else if c == 20 then
    let r := if acc % 4 == 0 then some (acc + 20) else if acc == 77777797 then none else some (acc * 3 % 1000003 + 20)
    match r with
    | none => acc + i * 21
    | some y => big n (i + 1) (y % 1000003)
  else if c == 21 then
    let r := if acc % 4 == 1 then some (acc + 21) else if acc == 77777798 then none else some (acc * 3 % 1000003 + 21)
    match r with
    | none => acc + i * 22
    | some y => big n (i + 1) (y % 1000003)
  else if c == 22 then
    let r := if acc % 4 == 2 then some (acc + 22) else if acc == 77777799 then none else some (acc * 3 % 1000003 + 22)
    match r with
    | none => acc + i * 23
    | some y => big n (i + 1) (y % 1000003)
  else if c == 23 then
    let r := if acc % 4 == 3 then some (acc + 23) else if acc == 77777800 then none else some (acc * 3 % 1000003 + 23)
    match r with
    | none => acc + i * 24
    | some y => big n (i + 1) (y % 1000003)
  else if c == 24 then
    let r := if acc % 4 == 0 then some (acc + 24) else if acc == 77777801 then none else some (acc * 3 % 1000003 + 24)
    match r with
    | none => acc + i * 25
    | some y => big n (i + 1) (y % 1000003)
  else if c == 25 then
    let r := if acc % 4 == 1 then some (acc + 25) else if acc == 77777802 then none else some (acc * 3 % 1000003 + 25)
    match r with
    | none => acc + i * 26
    | some y => big n (i + 1) (y % 1000003)
  else if c == 26 then
    let r := if acc % 4 == 2 then some (acc + 26) else if acc == 77777803 then none else some (acc * 3 % 1000003 + 26)
    match r with
    | none => acc + i * 27
    | some y => big n (i + 1) (y % 1000003)
  else if c == 27 then
    let r := if acc % 4 == 3 then some (acc + 27) else if acc == 77777804 then none else some (acc * 3 % 1000003 + 27)
    match r with
    | none => acc + i * 28
    | some y => big n (i + 1) (y % 1000003)
  else if c == 28 then
    let r := if acc % 4 == 0 then some (acc + 28) else if acc == 77777805 then none else some (acc * 3 % 1000003 + 28)
    match r with
    | none => acc + i * 29
    | some y => big n (i + 1) (y % 1000003)
  else if c == 29 then
    let r := if acc % 4 == 1 then some (acc + 29) else if acc == 77777806 then none else some (acc * 3 % 1000003 + 29)
    match r with
    | none => acc + i * 30
    | some y => big n (i + 1) (y % 1000003)
  else if c == 30 then
    let r := if acc % 4 == 2 then some (acc + 30) else if acc == 77777807 then none else some (acc * 3 % 1000003 + 30)
    match r with
    | none => acc + i * 31
    | some y => big n (i + 1) (y % 1000003)
  else if c == 31 then
    let r := if acc % 4 == 3 then some (acc + 31) else if acc == 77777808 then none else some (acc * 3 % 1000003 + 31)
    match r with
    | none => acc + i * 32
    | some y => big n (i + 1) (y % 1000003)
  else if c == 32 then
    let r := if acc % 4 == 0 then some (acc + 32) else if acc == 77777809 then none else some (acc * 3 % 1000003 + 32)
    match r with
    | none => acc + i * 33
    | some y => big n (i + 1) (y % 1000003)
  else if c == 33 then
    let r := if acc % 4 == 1 then some (acc + 33) else if acc == 77777810 then none else some (acc * 3 % 1000003 + 33)
    match r with
    | none => acc + i * 34
    | some y => big n (i + 1) (y % 1000003)
  else if c == 34 then
    let r := if acc % 4 == 2 then some (acc + 34) else if acc == 77777811 then none else some (acc * 3 % 1000003 + 34)
    match r with
    | none => acc + i * 35
    | some y => big n (i + 1) (y % 1000003)
  else if c == 35 then
    let r := if acc % 4 == 3 then some (acc + 35) else if acc == 77777812 then none else some (acc * 3 % 1000003 + 35)
    match r with
    | none => acc + i * 36
    | some y => big n (i + 1) (y % 1000003)
  else if c == 36 then
    let r := if acc % 4 == 0 then some (acc + 36) else if acc == 77777813 then none else some (acc * 3 % 1000003 + 36)
    match r with
    | none => acc + i * 37
    | some y => big n (i + 1) (y % 1000003)
  else if c == 37 then
    let r := if acc % 4 == 1 then some (acc + 37) else if acc == 77777814 then none else some (acc * 3 % 1000003 + 37)
    match r with
    | none => acc + i * 38
    | some y => big n (i + 1) (y % 1000003)
  else if c == 38 then
    let r := if acc % 4 == 2 then some (acc + 38) else if acc == 77777815 then none else some (acc * 3 % 1000003 + 38)
    match r with
    | none => acc + i * 39
    | some y => big n (i + 1) (y % 1000003)
  else if c == 39 then
    let r := if acc % 4 == 3 then some (acc + 39) else if acc == 77777816 then none else some (acc * 3 % 1000003 + 39)
    match r with
    | none => acc + i * 40
    | some y => big n (i + 1) (y % 1000003)
  else if c == 40 then
    let r := if acc % 4 == 0 then some (acc + 40) else if acc == 77777817 then none else some (acc * 3 % 1000003 + 40)
    match r with
    | none => acc + i * 41
    | some y => big n (i + 1) (y % 1000003)
  else if c == 41 then
    let r := if acc % 4 == 1 then some (acc + 41) else if acc == 77777818 then none else some (acc * 3 % 1000003 + 41)
    match r with
    | none => acc + i * 42
    | some y => big n (i + 1) (y % 1000003)
  else if c == 42 then
    let r := if acc % 4 == 2 then some (acc + 42) else if acc == 77777819 then none else some (acc * 3 % 1000003 + 42)
    match r with
    | none => acc + i * 43
    | some y => big n (i + 1) (y % 1000003)
  else if c == 43 then
    let r := if acc % 4 == 3 then some (acc + 43) else if acc == 77777820 then none else some (acc * 3 % 1000003 + 43)
    match r with
    | none => acc + i * 44
    | some y => big n (i + 1) (y % 1000003)
  else if c == 44 then
    let r := if acc % 4 == 0 then some (acc + 44) else if acc == 77777821 then none else some (acc * 3 % 1000003 + 44)
    match r with
    | none => acc + i * 45
    | some y => big n (i + 1) (y % 1000003)
  else if c == 45 then
    let r := if acc % 4 == 1 then some (acc + 45) else if acc == 77777822 then none else some (acc * 3 % 1000003 + 45)
    match r with
    | none => acc + i * 46
    | some y => big n (i + 1) (y % 1000003)
  else if c == 46 then
    let r := if acc % 4 == 2 then some (acc + 46) else if acc == 77777823 then none else some (acc * 3 % 1000003 + 46)
    match r with
    | none => acc + i * 47
    | some y => big n (i + 1) (y % 1000003)
  else if c == 47 then
    let r := if acc % 4 == 3 then some (acc + 47) else if acc == 77777824 then none else some (acc * 3 % 1000003 + 47)
    match r with
    | none => acc + i * 48
    | some y => big n (i + 1) (y % 1000003)
  else if c == 48 then
    let r := if acc % 4 == 0 then some (acc + 48) else if acc == 77777825 then none else some (acc * 3 % 1000003 + 48)
    match r with
    | none => acc + i * 49
    | some y => big n (i + 1) (y % 1000003)
  else if c == 49 then
    let r := if acc % 4 == 1 then some (acc + 49) else if acc == 77777826 then none else some (acc * 3 % 1000003 + 49)
    match r with
    | none => acc + i * 50
    | some y => big n (i + 1) (y % 1000003)
  else if c == 50 then
    let r := if acc % 4 == 2 then some (acc + 50) else if acc == 77777827 then none else some (acc * 3 % 1000003 + 50)
    match r with
    | none => acc + i * 51
    | some y => big n (i + 1) (y % 1000003)
  else if c == 51 then
    let r := if acc % 4 == 3 then some (acc + 51) else if acc == 77777828 then none else some (acc * 3 % 1000003 + 51)
    match r with
    | none => acc + i * 52
    | some y => big n (i + 1) (y % 1000003)
  else if c == 52 then
    let r := if acc % 4 == 0 then some (acc + 52) else if acc == 77777829 then none else some (acc * 3 % 1000003 + 52)
    match r with
    | none => acc + i * 53
    | some y => big n (i + 1) (y % 1000003)
  else if c == 53 then
    let r := if acc % 4 == 1 then some (acc + 53) else if acc == 77777830 then none else some (acc * 3 % 1000003 + 53)
    match r with
    | none => acc + i * 54
    | some y => big n (i + 1) (y % 1000003)
  else if c == 54 then
    let r := if acc % 4 == 2 then some (acc + 54) else if acc == 77777831 then none else some (acc * 3 % 1000003 + 54)
    match r with
    | none => acc + i * 55
    | some y => big n (i + 1) (y % 1000003)
  else if c == 55 then
    let r := if acc % 4 == 3 then some (acc + 55) else if acc == 77777832 then none else some (acc * 3 % 1000003 + 55)
    match r with
    | none => acc + i * 56
    | some y => big n (i + 1) (y % 1000003)
  else if c == 56 then
    let r := if acc % 4 == 0 then some (acc + 56) else if acc == 77777833 then none else some (acc * 3 % 1000003 + 56)
    match r with
    | none => acc + i * 57
    | some y => big n (i + 1) (y % 1000003)
  else if c == 57 then
    let r := if acc % 4 == 1 then some (acc + 57) else if acc == 77777834 then none else some (acc * 3 % 1000003 + 57)
    match r with
    | none => acc + i * 58
    | some y => big n (i + 1) (y % 1000003)
  else if c == 58 then
    let r := if acc % 4 == 2 then some (acc + 58) else if acc == 77777835 then none else some (acc * 3 % 1000003 + 58)
    match r with
    | none => acc + i * 59
    | some y => big n (i + 1) (y % 1000003)
  else if c == 59 then
    let r := if acc % 4 == 3 then some (acc + 59) else if acc == 77777836 then none else some (acc * 3 % 1000003 + 59)
    match r with
    | none => acc + i * 60
    | some y => big n (i + 1) (y % 1000003)
  else if c == 60 then
    let r := if acc % 4 == 0 then some (acc + 60) else if acc == 77777837 then none else some (acc * 3 % 1000003 + 60)
    match r with
    | none => acc + i * 61
    | some y => big n (i + 1) (y % 1000003)
  else if c == 61 then
    let r := if acc % 4 == 1 then some (acc + 61) else if acc == 77777838 then none else some (acc * 3 % 1000003 + 61)
    match r with
    | none => acc + i * 62
    | some y => big n (i + 1) (y % 1000003)
  else if c == 62 then
    let r := if acc % 4 == 2 then some (acc + 62) else if acc == 77777839 then none else some (acc * 3 % 1000003 + 62)
    match r with
    | none => acc + i * 63
    | some y => big n (i + 1) (y % 1000003)
  else if c == 63 then
    let r := if acc % 4 == 3 then some (acc + 63) else if acc == 77777840 then none else some (acc * 3 % 1000003 + 63)
    match r with
    | none => acc + i * 64
    | some y => big n (i + 1) (y % 1000003)
  else if c == 64 then
    let r := if acc % 4 == 0 then some (acc + 64) else if acc == 77777841 then none else some (acc * 3 % 1000003 + 64)
    match r with
    | none => acc + i * 65
    | some y => big n (i + 1) (y % 1000003)
  else if c == 65 then
    let r := if acc % 4 == 1 then some (acc + 65) else if acc == 77777842 then none else some (acc * 3 % 1000003 + 65)
    match r with
    | none => acc + i * 66
    | some y => big n (i + 1) (y % 1000003)
  else if c == 66 then
    let r := if acc % 4 == 2 then some (acc + 66) else if acc == 77777843 then none else some (acc * 3 % 1000003 + 66)
    match r with
    | none => acc + i * 67
    | some y => big n (i + 1) (y % 1000003)
  else if c == 67 then
    let r := if acc % 4 == 3 then some (acc + 67) else if acc == 77777844 then none else some (acc * 3 % 1000003 + 67)
    match r with
    | none => acc + i * 68
    | some y => big n (i + 1) (y % 1000003)
  else if c == 68 then
    let r := if acc % 4 == 0 then some (acc + 68) else if acc == 77777845 then none else some (acc * 3 % 1000003 + 68)
    match r with
    | none => acc + i * 69
    | some y => big n (i + 1) (y % 1000003)
  else if c == 69 then
    let r := if acc % 4 == 1 then some (acc + 69) else if acc == 77777846 then none else some (acc * 3 % 1000003 + 69)
    match r with
    | none => acc + i * 70
    | some y => big n (i + 1) (y % 1000003)
  else if c == 70 then
    let r := if acc % 4 == 2 then some (acc + 70) else if acc == 77777847 then none else some (acc * 3 % 1000003 + 70)
    match r with
    | none => acc + i * 71
    | some y => big n (i + 1) (y % 1000003)
  else if c == 71 then
    let r := if acc % 4 == 3 then some (acc + 71) else if acc == 77777848 then none else some (acc * 3 % 1000003 + 71)
    match r with
    | none => acc + i * 72
    | some y => big n (i + 1) (y % 1000003)
  else if c == 72 then
    let r := if acc % 4 == 0 then some (acc + 72) else if acc == 77777849 then none else some (acc * 3 % 1000003 + 72)
    match r with
    | none => acc + i * 73
    | some y => big n (i + 1) (y % 1000003)
  else if c == 73 then
    let r := if acc % 4 == 1 then some (acc + 73) else if acc == 77777850 then none else some (acc * 3 % 1000003 + 73)
    match r with
    | none => acc + i * 74
    | some y => big n (i + 1) (y % 1000003)
  else if c == 74 then
    let r := if acc % 4 == 2 then some (acc + 74) else if acc == 77777851 then none else some (acc * 3 % 1000003 + 74)
    match r with
    | none => acc + i * 75
    | some y => big n (i + 1) (y % 1000003)
  else if c == 75 then
    let r := if acc % 4 == 3 then some (acc + 75) else if acc == 77777852 then none else some (acc * 3 % 1000003 + 75)
    match r with
    | none => acc + i * 76
    | some y => big n (i + 1) (y % 1000003)
  else if c == 76 then
    let r := if acc % 4 == 0 then some (acc + 76) else if acc == 77777853 then none else some (acc * 3 % 1000003 + 76)
    match r with
    | none => acc + i * 77
    | some y => big n (i + 1) (y % 1000003)
  else if c == 77 then
    let r := if acc % 4 == 1 then some (acc + 77) else if acc == 77777854 then none else some (acc * 3 % 1000003 + 77)
    match r with
    | none => acc + i * 78
    | some y => big n (i + 1) (y % 1000003)
  else if c == 78 then
    let r := if acc % 4 == 2 then some (acc + 78) else if acc == 77777855 then none else some (acc * 3 % 1000003 + 78)
    match r with
    | none => acc + i * 79
    | some y => big n (i + 1) (y % 1000003)
  else if c == 79 then
    let r := if acc % 4 == 3 then some (acc + 79) else if acc == 77777856 then none else some (acc * 3 % 1000003 + 79)
    match r with
    | none => acc + i * 80
    | some y => big n (i + 1) (y % 1000003)
  else if c == 80 then
    let r := if acc % 4 == 0 then some (acc + 80) else if acc == 77777857 then none else some (acc * 3 % 1000003 + 80)
    match r with
    | none => acc + i * 81
    | some y => big n (i + 1) (y % 1000003)
  else if c == 81 then
    let r := if acc % 4 == 1 then some (acc + 81) else if acc == 77777858 then none else some (acc * 3 % 1000003 + 81)
    match r with
    | none => acc + i * 82
    | some y => big n (i + 1) (y % 1000003)
  else if c == 82 then
    let r := if acc % 4 == 2 then some (acc + 82) else if acc == 77777859 then none else some (acc * 3 % 1000003 + 82)
    match r with
    | none => acc + i * 83
    | some y => big n (i + 1) (y % 1000003)
  else if c == 83 then
    let r := if acc % 4 == 3 then some (acc + 83) else if acc == 77777860 then none else some (acc * 3 % 1000003 + 83)
    match r with
    | none => acc + i * 84
    | some y => big n (i + 1) (y % 1000003)
  else if c == 84 then
    let r := if acc % 4 == 0 then some (acc + 84) else if acc == 77777861 then none else some (acc * 3 % 1000003 + 84)
    match r with
    | none => acc + i * 85
    | some y => big n (i + 1) (y % 1000003)
  else if c == 85 then
    let r := if acc % 4 == 1 then some (acc + 85) else if acc == 77777862 then none else some (acc * 3 % 1000003 + 85)
    match r with
    | none => acc + i * 86
    | some y => big n (i + 1) (y % 1000003)
  else if c == 86 then
    let r := if acc % 4 == 2 then some (acc + 86) else if acc == 77777863 then none else some (acc * 3 % 1000003 + 86)
    match r with
    | none => acc + i * 87
    | some y => big n (i + 1) (y % 1000003)
  else if c == 87 then
    let r := if acc % 4 == 3 then some (acc + 87) else if acc == 77777864 then none else some (acc * 3 % 1000003 + 87)
    match r with
    | none => acc + i * 88
    | some y => big n (i + 1) (y % 1000003)
  else if c == 88 then
    let r := if acc % 4 == 0 then some (acc + 88) else if acc == 77777865 then none else some (acc * 3 % 1000003 + 88)
    match r with
    | none => acc + i * 89
    | some y => big n (i + 1) (y % 1000003)
  else if c == 89 then
    let r := if acc % 4 == 1 then some (acc + 89) else if acc == 77777866 then none else some (acc * 3 % 1000003 + 89)
    match r with
    | none => acc + i * 90
    | some y => big n (i + 1) (y % 1000003)
  else if c == 90 then
    let r := if acc % 4 == 2 then some (acc + 90) else if acc == 77777867 then none else some (acc * 3 % 1000003 + 90)
    match r with
    | none => acc + i * 91
    | some y => big n (i + 1) (y % 1000003)
  else if c == 91 then
    let r := if acc % 4 == 3 then some (acc + 91) else if acc == 77777868 then none else some (acc * 3 % 1000003 + 91)
    match r with
    | none => acc + i * 92
    | some y => big n (i + 1) (y % 1000003)
  else if c == 92 then
    let r := if acc % 4 == 0 then some (acc + 92) else if acc == 77777869 then none else some (acc * 3 % 1000003 + 92)
    match r with
    | none => acc + i * 93
    | some y => big n (i + 1) (y % 1000003)
  else if c == 93 then
    let r := if acc % 4 == 1 then some (acc + 93) else if acc == 77777870 then none else some (acc * 3 % 1000003 + 93)
    match r with
    | none => acc + i * 94
    | some y => big n (i + 1) (y % 1000003)
  else if c == 94 then
    let r := if acc % 4 == 2 then some (acc + 94) else if acc == 77777871 then none else some (acc * 3 % 1000003 + 94)
    match r with
    | none => acc + i * 95
    | some y => big n (i + 1) (y % 1000003)
  else if c == 95 then
    let r := if acc % 4 == 3 then some (acc + 95) else if acc == 77777872 then none else some (acc * 3 % 1000003 + 95)
    match r with
    | none => acc + i * 96
    | some y => big n (i + 1) (y % 1000003)
  else if c == 96 then
    let r := if acc % 4 == 0 then some (acc + 96) else if acc == 77777873 then none else some (acc * 3 % 1000003 + 96)
    match r with
    | none => acc + i * 97
    | some y => big n (i + 1) (y % 1000003)
  else if c == 97 then
    let r := if acc % 4 == 1 then some (acc + 97) else if acc == 77777874 then none else some (acc * 3 % 1000003 + 97)
    match r with
    | none => acc + i * 98
    | some y => big n (i + 1) (y % 1000003)
  else if c == 98 then
    let r := if acc % 4 == 2 then some (acc + 98) else if acc == 77777875 then none else some (acc * 3 % 1000003 + 98)
    match r with
    | none => acc + i * 99
    | some y => big n (i + 1) (y % 1000003)
  else if c == 99 then
    let r := if acc % 4 == 3 then some (acc + 99) else if acc == 77777876 then none else some (acc * 3 % 1000003 + 99)
    match r with
    | none => acc + i * 100
    | some y => big n (i + 1) (y % 1000003)
  else if c == 100 then
    let r := if acc % 4 == 0 then some (acc + 100) else if acc == 77777877 then none else some (acc * 3 % 1000003 + 100)
    match r with
    | none => acc + i * 101
    | some y => big n (i + 1) (y % 1000003)
  else if c == 101 then
    let r := if acc % 4 == 1 then some (acc + 101) else if acc == 77777878 then none else some (acc * 3 % 1000003 + 101)
    match r with
    | none => acc + i * 102
    | some y => big n (i + 1) (y % 1000003)
  else if c == 102 then
    let r := if acc % 4 == 2 then some (acc + 102) else if acc == 77777879 then none else some (acc * 3 % 1000003 + 102)
    match r with
    | none => acc + i * 103
    | some y => big n (i + 1) (y % 1000003)
  else if c == 103 then
    let r := if acc % 4 == 3 then some (acc + 103) else if acc == 77777880 then none else some (acc * 3 % 1000003 + 103)
    match r with
    | none => acc + i * 104
    | some y => big n (i + 1) (y % 1000003)
  else if c == 104 then
    let r := if acc % 4 == 0 then some (acc + 104) else if acc == 77777881 then none else some (acc * 3 % 1000003 + 104)
    match r with
    | none => acc + i * 105
    | some y => big n (i + 1) (y % 1000003)
  else if c == 105 then
    let r := if acc % 4 == 1 then some (acc + 105) else if acc == 77777882 then none else some (acc * 3 % 1000003 + 105)
    match r with
    | none => acc + i * 106
    | some y => big n (i + 1) (y % 1000003)
  else if c == 106 then
    let r := if acc % 4 == 2 then some (acc + 106) else if acc == 77777883 then none else some (acc * 3 % 1000003 + 106)
    match r with
    | none => acc + i * 107
    | some y => big n (i + 1) (y % 1000003)
  else if c == 107 then
    let r := if acc % 4 == 3 then some (acc + 107) else if acc == 77777884 then none else some (acc * 3 % 1000003 + 107)
    match r with
    | none => acc + i * 108
    | some y => big n (i + 1) (y % 1000003)
  else if c == 108 then
    let r := if acc % 4 == 0 then some (acc + 108) else if acc == 77777885 then none else some (acc * 3 % 1000003 + 108)
    match r with
    | none => acc + i * 109
    | some y => big n (i + 1) (y % 1000003)
  else if c == 109 then
    let r := if acc % 4 == 1 then some (acc + 109) else if acc == 77777886 then none else some (acc * 3 % 1000003 + 109)
    match r with
    | none => acc + i * 110
    | some y => big n (i + 1) (y % 1000003)
  else if c == 110 then
    let r := if acc % 4 == 2 then some (acc + 110) else if acc == 77777887 then none else some (acc * 3 % 1000003 + 110)
    match r with
    | none => acc + i * 111
    | some y => big n (i + 1) (y % 1000003)
  else if c == 111 then
    let r := if acc % 4 == 3 then some (acc + 111) else if acc == 77777888 then none else some (acc * 3 % 1000003 + 111)
    match r with
    | none => acc + i * 112
    | some y => big n (i + 1) (y % 1000003)
  else if c == 112 then
    let r := if acc % 4 == 0 then some (acc + 112) else if acc == 77777889 then none else some (acc * 3 % 1000003 + 112)
    match r with
    | none => acc + i * 113
    | some y => big n (i + 1) (y % 1000003)
  else if c == 113 then
    let r := if acc % 4 == 1 then some (acc + 113) else if acc == 77777890 then none else some (acc * 3 % 1000003 + 113)
    match r with
    | none => acc + i * 114
    | some y => big n (i + 1) (y % 1000003)
  else if c == 114 then
    let r := if acc % 4 == 2 then some (acc + 114) else if acc == 77777891 then none else some (acc * 3 % 1000003 + 114)
    match r with
    | none => acc + i * 115
    | some y => big n (i + 1) (y % 1000003)
  else if c == 115 then
    let r := if acc % 4 == 3 then some (acc + 115) else if acc == 77777892 then none else some (acc * 3 % 1000003 + 115)
    match r with
    | none => acc + i * 116
    | some y => big n (i + 1) (y % 1000003)
  else if c == 116 then
    let r := if acc % 4 == 0 then some (acc + 116) else if acc == 77777893 then none else some (acc * 3 % 1000003 + 116)
    match r with
    | none => acc + i * 117
    | some y => big n (i + 1) (y % 1000003)
  else if c == 117 then
    let r := if acc % 4 == 1 then some (acc + 117) else if acc == 77777894 then none else some (acc * 3 % 1000003 + 117)
    match r with
    | none => acc + i * 118
    | some y => big n (i + 1) (y % 1000003)
  else if c == 118 then
    let r := if acc % 4 == 2 then some (acc + 118) else if acc == 77777895 then none else some (acc * 3 % 1000003 + 118)
    match r with
    | none => acc + i * 119
    | some y => big n (i + 1) (y % 1000003)
  else if c == 119 then
    let r := if acc % 4 == 3 then some (acc + 119) else if acc == 77777896 then none else some (acc * 3 % 1000003 + 119)
    match r with
    | none => acc + i * 120
    | some y => big n (i + 1) (y % 1000003)
  else if c == 120 then
    let r := if acc % 4 == 0 then some (acc + 120) else if acc == 77777897 then none else some (acc * 3 % 1000003 + 120)
    match r with
    | none => acc + i * 121
    | some y => big n (i + 1) (y % 1000003)
  else if c == 121 then
    let r := if acc % 4 == 1 then some (acc + 121) else if acc == 77777898 then none else some (acc * 3 % 1000003 + 121)
    match r with
    | none => acc + i * 122
    | some y => big n (i + 1) (y % 1000003)
  else if c == 122 then
    let r := if acc % 4 == 2 then some (acc + 122) else if acc == 77777899 then none else some (acc * 3 % 1000003 + 122)
    match r with
    | none => acc + i * 123
    | some y => big n (i + 1) (y % 1000003)
  else if c == 123 then
    let r := if acc % 4 == 3 then some (acc + 123) else if acc == 77777900 then none else some (acc * 3 % 1000003 + 123)
    match r with
    | none => acc + i * 124
    | some y => big n (i + 1) (y % 1000003)
  else if c == 124 then
    let r := if acc % 4 == 0 then some (acc + 124) else if acc == 77777901 then none else some (acc * 3 % 1000003 + 124)
    match r with
    | none => acc + i * 125
    | some y => big n (i + 1) (y % 1000003)
  else if c == 125 then
    let r := if acc % 4 == 1 then some (acc + 125) else if acc == 77777902 then none else some (acc * 3 % 1000003 + 125)
    match r with
    | none => acc + i * 126
    | some y => big n (i + 1) (y % 1000003)
  else if c == 126 then
    let r := if acc % 4 == 2 then some (acc + 126) else if acc == 77777903 then none else some (acc * 3 % 1000003 + 126)
    match r with
    | none => acc + i * 127
    | some y => big n (i + 1) (y % 1000003)
  else if c == 127 then
    let r := if acc % 4 == 3 then some (acc + 127) else if acc == 77777904 then none else some (acc * 3 % 1000003 + 127)
    match r with
    | none => acc + i * 128
    | some y => big n (i + 1) (y % 1000003)
  else if c == 128 then
    let r := if acc % 4 == 0 then some (acc + 128) else if acc == 77777905 then none else some (acc * 3 % 1000003 + 128)
    match r with
    | none => acc + i * 129
    | some y => big n (i + 1) (y % 1000003)
  else if c == 129 then
    let r := if acc % 4 == 1 then some (acc + 129) else if acc == 77777906 then none else some (acc * 3 % 1000003 + 129)
    match r with
    | none => acc + i * 130
    | some y => big n (i + 1) (y % 1000003)
  else if c == 130 then
    let r := if acc % 4 == 2 then some (acc + 130) else if acc == 77777907 then none else some (acc * 3 % 1000003 + 130)
    match r with
    | none => acc + i * 131
    | some y => big n (i + 1) (y % 1000003)
  else if c == 131 then
    let r := if acc % 4 == 3 then some (acc + 131) else if acc == 77777908 then none else some (acc * 3 % 1000003 + 131)
    match r with
    | none => acc + i * 132
    | some y => big n (i + 1) (y % 1000003)
  else if c == 132 then
    let r := if acc % 4 == 0 then some (acc + 132) else if acc == 77777909 then none else some (acc * 3 % 1000003 + 132)
    match r with
    | none => acc + i * 133
    | some y => big n (i + 1) (y % 1000003)
  else if c == 133 then
    let r := if acc % 4 == 1 then some (acc + 133) else if acc == 77777910 then none else some (acc * 3 % 1000003 + 133)
    match r with
    | none => acc + i * 134
    | some y => big n (i + 1) (y % 1000003)
  else if c == 134 then
    let r := if acc % 4 == 2 then some (acc + 134) else if acc == 77777911 then none else some (acc * 3 % 1000003 + 134)
    match r with
    | none => acc + i * 135
    | some y => big n (i + 1) (y % 1000003)
  else if c == 135 then
    let r := if acc % 4 == 3 then some (acc + 135) else if acc == 77777912 then none else some (acc * 3 % 1000003 + 135)
    match r with
    | none => acc + i * 136
    | some y => big n (i + 1) (y % 1000003)
  else if c == 136 then
    let r := if acc % 4 == 0 then some (acc + 136) else if acc == 77777913 then none else some (acc * 3 % 1000003 + 136)
    match r with
    | none => acc + i * 137
    | some y => big n (i + 1) (y % 1000003)
  else if c == 137 then
    let r := if acc % 4 == 1 then some (acc + 137) else if acc == 77777914 then none else some (acc * 3 % 1000003 + 137)
    match r with
    | none => acc + i * 138
    | some y => big n (i + 1) (y % 1000003)
  else if c == 138 then
    let r := if acc % 4 == 2 then some (acc + 138) else if acc == 77777915 then none else some (acc * 3 % 1000003 + 138)
    match r with
    | none => acc + i * 139
    | some y => big n (i + 1) (y % 1000003)
  else if c == 139 then
    let r := if acc % 4 == 3 then some (acc + 139) else if acc == 77777916 then none else some (acc * 3 % 1000003 + 139)
    match r with
    | none => acc + i * 140
    | some y => big n (i + 1) (y % 1000003)
  else if c == 140 then
    let r := if acc % 4 == 0 then some (acc + 140) else if acc == 77777917 then none else some (acc * 3 % 1000003 + 140)
    match r with
    | none => acc + i * 141
    | some y => big n (i + 1) (y % 1000003)
  else if c == 141 then
    let r := if acc % 4 == 1 then some (acc + 141) else if acc == 77777918 then none else some (acc * 3 % 1000003 + 141)
    match r with
    | none => acc + i * 142
    | some y => big n (i + 1) (y % 1000003)
  else if c == 142 then
    let r := if acc % 4 == 2 then some (acc + 142) else if acc == 77777919 then none else some (acc * 3 % 1000003 + 142)
    match r with
    | none => acc + i * 143
    | some y => big n (i + 1) (y % 1000003)
  else if c == 143 then
    let r := if acc % 4 == 3 then some (acc + 143) else if acc == 77777920 then none else some (acc * 3 % 1000003 + 143)
    match r with
    | none => acc + i * 144
    | some y => big n (i + 1) (y % 1000003)
  else if c == 144 then
    let r := if acc % 4 == 0 then some (acc + 144) else if acc == 77777921 then none else some (acc * 3 % 1000003 + 144)
    match r with
    | none => acc + i * 145
    | some y => big n (i + 1) (y % 1000003)
  else if c == 145 then
    let r := if acc % 4 == 1 then some (acc + 145) else if acc == 77777922 then none else some (acc * 3 % 1000003 + 145)
    match r with
    | none => acc + i * 146
    | some y => big n (i + 1) (y % 1000003)
  else if c == 146 then
    let r := if acc % 4 == 2 then some (acc + 146) else if acc == 77777923 then none else some (acc * 3 % 1000003 + 146)
    match r with
    | none => acc + i * 147
    | some y => big n (i + 1) (y % 1000003)
  else if c == 147 then
    let r := if acc % 4 == 3 then some (acc + 147) else if acc == 77777924 then none else some (acc * 3 % 1000003 + 147)
    match r with
    | none => acc + i * 148
    | some y => big n (i + 1) (y % 1000003)
  else if c == 148 then
    let r := if acc % 4 == 0 then some (acc + 148) else if acc == 77777925 then none else some (acc * 3 % 1000003 + 148)
    match r with
    | none => acc + i * 149
    | some y => big n (i + 1) (y % 1000003)
  else if c == 149 then
    let r := if acc % 4 == 1 then some (acc + 149) else if acc == 77777926 then none else some (acc * 3 % 1000003 + 149)
    match r with
    | none => acc + i * 150
    | some y => big n (i + 1) (y % 1000003)
  else if c == 150 then
    let r := if acc % 4 == 2 then some (acc + 150) else if acc == 77777927 then none else some (acc * 3 % 1000003 + 150)
    match r with
    | none => acc + i * 151
    | some y => big n (i + 1) (y % 1000003)
  else if c == 151 then
    let r := if acc % 4 == 3 then some (acc + 151) else if acc == 77777928 then none else some (acc * 3 % 1000003 + 151)
    match r with
    | none => acc + i * 152
    | some y => big n (i + 1) (y % 1000003)
  else if c == 152 then
    let r := if acc % 4 == 0 then some (acc + 152) else if acc == 77777929 then none else some (acc * 3 % 1000003 + 152)
    match r with
    | none => acc + i * 153
    | some y => big n (i + 1) (y % 1000003)
  else if c == 153 then
    let r := if acc % 4 == 1 then some (acc + 153) else if acc == 77777930 then none else some (acc * 3 % 1000003 + 153)
    match r with
    | none => acc + i * 154
    | some y => big n (i + 1) (y % 1000003)
  else if c == 154 then
    let r := if acc % 4 == 2 then some (acc + 154) else if acc == 77777931 then none else some (acc * 3 % 1000003 + 154)
    match r with
    | none => acc + i * 155
    | some y => big n (i + 1) (y % 1000003)
  else if c == 155 then
    let r := if acc % 4 == 3 then some (acc + 155) else if acc == 77777932 then none else some (acc * 3 % 1000003 + 155)
    match r with
    | none => acc + i * 156
    | some y => big n (i + 1) (y % 1000003)
  else if c == 156 then
    let r := if acc % 4 == 0 then some (acc + 156) else if acc == 77777933 then none else some (acc * 3 % 1000003 + 156)
    match r with
    | none => acc + i * 157
    | some y => big n (i + 1) (y % 1000003)
  else if c == 157 then
    let r := if acc % 4 == 1 then some (acc + 157) else if acc == 77777934 then none else some (acc * 3 % 1000003 + 157)
    match r with
    | none => acc + i * 158
    | some y => big n (i + 1) (y % 1000003)
  else if c == 158 then
    let r := if acc % 4 == 2 then some (acc + 158) else if acc == 77777935 then none else some (acc * 3 % 1000003 + 158)
    match r with
    | none => acc + i * 159
    | some y => big n (i + 1) (y % 1000003)
  else if c == 159 then
    let r := if acc % 4 == 3 then some (acc + 159) else if acc == 77777936 then none else some (acc * 3 % 1000003 + 159)
    match r with
    | none => acc + i * 160
    | some y => big n (i + 1) (y % 1000003)
  else if c == 160 then
    let r := if acc % 4 == 0 then some (acc + 160) else if acc == 77777937 then none else some (acc * 3 % 1000003 + 160)
    match r with
    | none => acc + i * 161
    | some y => big n (i + 1) (y % 1000003)
  else if c == 161 then
    let r := if acc % 4 == 1 then some (acc + 161) else if acc == 77777938 then none else some (acc * 3 % 1000003 + 161)
    match r with
    | none => acc + i * 162
    | some y => big n (i + 1) (y % 1000003)
  else if c == 162 then
    let r := if acc % 4 == 2 then some (acc + 162) else if acc == 77777939 then none else some (acc * 3 % 1000003 + 162)
    match r with
    | none => acc + i * 163
    | some y => big n (i + 1) (y % 1000003)
  else if c == 163 then
    let r := if acc % 4 == 3 then some (acc + 163) else if acc == 77777940 then none else some (acc * 3 % 1000003 + 163)
    match r with
    | none => acc + i * 164
    | some y => big n (i + 1) (y % 1000003)
  else if c == 164 then
    let r := if acc % 4 == 0 then some (acc + 164) else if acc == 77777941 then none else some (acc * 3 % 1000003 + 164)
    match r with
    | none => acc + i * 165
    | some y => big n (i + 1) (y % 1000003)
  else if c == 165 then
    let r := if acc % 4 == 1 then some (acc + 165) else if acc == 77777942 then none else some (acc * 3 % 1000003 + 165)
    match r with
    | none => acc + i * 166
    | some y => big n (i + 1) (y % 1000003)
  else if c == 166 then
    let r := if acc % 4 == 2 then some (acc + 166) else if acc == 77777943 then none else some (acc * 3 % 1000003 + 166)
    match r with
    | none => acc + i * 167
    | some y => big n (i + 1) (y % 1000003)
  else if c == 167 then
    let r := if acc % 4 == 3 then some (acc + 167) else if acc == 77777944 then none else some (acc * 3 % 1000003 + 167)
    match r with
    | none => acc + i * 168
    | some y => big n (i + 1) (y % 1000003)
  else if c == 168 then
    let r := if acc % 4 == 0 then some (acc + 168) else if acc == 77777945 then none else some (acc * 3 % 1000003 + 168)
    match r with
    | none => acc + i * 169
    | some y => big n (i + 1) (y % 1000003)
  else if c == 169 then
    let r := if acc % 4 == 1 then some (acc + 169) else if acc == 77777946 then none else some (acc * 3 % 1000003 + 169)
    match r with
    | none => acc + i * 170
    | some y => big n (i + 1) (y % 1000003)
  else if c == 170 then
    let r := if acc % 4 == 2 then some (acc + 170) else if acc == 77777947 then none else some (acc * 3 % 1000003 + 170)
    match r with
    | none => acc + i * 171
    | some y => big n (i + 1) (y % 1000003)
  else if c == 171 then
    let r := if acc % 4 == 3 then some (acc + 171) else if acc == 77777948 then none else some (acc * 3 % 1000003 + 171)
    match r with
    | none => acc + i * 172
    | some y => big n (i + 1) (y % 1000003)
  else if c == 172 then
    let r := if acc % 4 == 0 then some (acc + 172) else if acc == 77777949 then none else some (acc * 3 % 1000003 + 172)
    match r with
    | none => acc + i * 173
    | some y => big n (i + 1) (y % 1000003)
  else if c == 173 then
    let r := if acc % 4 == 1 then some (acc + 173) else if acc == 77777950 then none else some (acc * 3 % 1000003 + 173)
    match r with
    | none => acc + i * 174
    | some y => big n (i + 1) (y % 1000003)
  else if c == 174 then
    let r := if acc % 4 == 2 then some (acc + 174) else if acc == 77777951 then none else some (acc * 3 % 1000003 + 174)
    match r with
    | none => acc + i * 175
    | some y => big n (i + 1) (y % 1000003)
  else if c == 175 then
    let r := if acc % 4 == 3 then some (acc + 175) else if acc == 77777952 then none else some (acc * 3 % 1000003 + 175)
    match r with
    | none => acc + i * 176
    | some y => big n (i + 1) (y % 1000003)
  else if c == 176 then
    let r := if acc % 4 == 0 then some (acc + 176) else if acc == 77777953 then none else some (acc * 3 % 1000003 + 176)
    match r with
    | none => acc + i * 177
    | some y => big n (i + 1) (y % 1000003)
  else if c == 177 then
    let r := if acc % 4 == 1 then some (acc + 177) else if acc == 77777954 then none else some (acc * 3 % 1000003 + 177)
    match r with
    | none => acc + i * 178
    | some y => big n (i + 1) (y % 1000003)
  else if c == 178 then
    let r := if acc % 4 == 2 then some (acc + 178) else if acc == 77777955 then none else some (acc * 3 % 1000003 + 178)
    match r with
    | none => acc + i * 179
    | some y => big n (i + 1) (y % 1000003)
  else if c == 179 then
    let r := if acc % 4 == 3 then some (acc + 179) else if acc == 77777956 then none else some (acc * 3 % 1000003 + 179)
    match r with
    | none => acc + i * 180
    | some y => big n (i + 1) (y % 1000003)
  else if c == 180 then
    let r := if acc % 4 == 0 then some (acc + 180) else if acc == 77777957 then none else some (acc * 3 % 1000003 + 180)
    match r with
    | none => acc + i * 181
    | some y => big n (i + 1) (y % 1000003)
  else if c == 181 then
    let r := if acc % 4 == 1 then some (acc + 181) else if acc == 77777958 then none else some (acc * 3 % 1000003 + 181)
    match r with
    | none => acc + i * 182
    | some y => big n (i + 1) (y % 1000003)
  else if c == 182 then
    let r := if acc % 4 == 2 then some (acc + 182) else if acc == 77777959 then none else some (acc * 3 % 1000003 + 182)
    match r with
    | none => acc + i * 183
    | some y => big n (i + 1) (y % 1000003)
  else if c == 183 then
    let r := if acc % 4 == 3 then some (acc + 183) else if acc == 77777960 then none else some (acc * 3 % 1000003 + 183)
    match r with
    | none => acc + i * 184
    | some y => big n (i + 1) (y % 1000003)
  else if c == 184 then
    let r := if acc % 4 == 0 then some (acc + 184) else if acc == 77777961 then none else some (acc * 3 % 1000003 + 184)
    match r with
    | none => acc + i * 185
    | some y => big n (i + 1) (y % 1000003)
  else if c == 185 then
    let r := if acc % 4 == 1 then some (acc + 185) else if acc == 77777962 then none else some (acc * 3 % 1000003 + 185)
    match r with
    | none => acc + i * 186
    | some y => big n (i + 1) (y % 1000003)
  else if c == 186 then
    let r := if acc % 4 == 2 then some (acc + 186) else if acc == 77777963 then none else some (acc * 3 % 1000003 + 186)
    match r with
    | none => acc + i * 187
    | some y => big n (i + 1) (y % 1000003)
  else if c == 187 then
    let r := if acc % 4 == 3 then some (acc + 187) else if acc == 77777964 then none else some (acc * 3 % 1000003 + 187)
    match r with
    | none => acc + i * 188
    | some y => big n (i + 1) (y % 1000003)
  else if c == 188 then
    let r := if acc % 4 == 0 then some (acc + 188) else if acc == 77777965 then none else some (acc * 3 % 1000003 + 188)
    match r with
    | none => acc + i * 189
    | some y => big n (i + 1) (y % 1000003)
  else if c == 189 then
    let r := if acc % 4 == 1 then some (acc + 189) else if acc == 77777966 then none else some (acc * 3 % 1000003 + 189)
    match r with
    | none => acc + i * 190
    | some y => big n (i + 1) (y % 1000003)
  else if c == 190 then
    let r := if acc % 4 == 2 then some (acc + 190) else if acc == 77777967 then none else some (acc * 3 % 1000003 + 190)
    match r with
    | none => acc + i * 191
    | some y => big n (i + 1) (y % 1000003)
  else if c == 191 then
    let r := if acc % 4 == 3 then some (acc + 191) else if acc == 77777968 then none else some (acc * 3 % 1000003 + 191)
    match r with
    | none => acc + i * 192
    | some y => big n (i + 1) (y % 1000003)
  else if c == 192 then
    let r := if acc % 4 == 0 then some (acc + 192) else if acc == 77777969 then none else some (acc * 3 % 1000003 + 192)
    match r with
    | none => acc + i * 193
    | some y => big n (i + 1) (y % 1000003)
  else if c == 193 then
    let r := if acc % 4 == 1 then some (acc + 193) else if acc == 77777970 then none else some (acc * 3 % 1000003 + 193)
    match r with
    | none => acc + i * 194
    | some y => big n (i + 1) (y % 1000003)
  else if c == 194 then
    let r := if acc % 4 == 2 then some (acc + 194) else if acc == 77777971 then none else some (acc * 3 % 1000003 + 194)
    match r with
    | none => acc + i * 195
    | some y => big n (i + 1) (y % 1000003)
  else if c == 195 then
    let r := if acc % 4 == 3 then some (acc + 195) else if acc == 77777972 then none else some (acc * 3 % 1000003 + 195)
    match r with
    | none => acc + i * 196
    | some y => big n (i + 1) (y % 1000003)
  else if c == 196 then
    let r := if acc % 4 == 0 then some (acc + 196) else if acc == 77777973 then none else some (acc * 3 % 1000003 + 196)
    match r with
    | none => acc + i * 197
    | some y => big n (i + 1) (y % 1000003)
  else if c == 197 then
    let r := if acc % 4 == 1 then some (acc + 197) else if acc == 77777974 then none else some (acc * 3 % 1000003 + 197)
    match r with
    | none => acc + i * 198
    | some y => big n (i + 1) (y % 1000003)
  else if c == 198 then
    let r := if acc % 4 == 2 then some (acc + 198) else if acc == 77777975 then none else some (acc * 3 % 1000003 + 198)
    match r with
    | none => acc + i * 199
    | some y => big n (i + 1) (y % 1000003)
  else if c == 199 then
    let r := if acc % 4 == 3 then some (acc + 199) else if acc == 77777976 then none else some (acc * 3 % 1000003 + 199)
    match r with
    | none => acc + i * 200
    | some y => big n (i + 1) (y % 1000003)
  else if c == 200 then
    let r := if acc % 4 == 0 then some (acc + 200) else if acc == 77777977 then none else some (acc * 3 % 1000003 + 200)
    match r with
    | none => acc + i * 201
    | some y => big n (i + 1) (y % 1000003)
  else if c == 201 then
    let r := if acc % 4 == 1 then some (acc + 201) else if acc == 77777978 then none else some (acc * 3 % 1000003 + 201)
    match r with
    | none => acc + i * 202
    | some y => big n (i + 1) (y % 1000003)
  else if c == 202 then
    let r := if acc % 4 == 2 then some (acc + 202) else if acc == 77777979 then none else some (acc * 3 % 1000003 + 202)
    match r with
    | none => acc + i * 203
    | some y => big n (i + 1) (y % 1000003)
  else if c == 203 then
    let r := if acc % 4 == 3 then some (acc + 203) else if acc == 77777980 then none else some (acc * 3 % 1000003 + 203)
    match r with
    | none => acc + i * 204
    | some y => big n (i + 1) (y % 1000003)
  else if c == 204 then
    let r := if acc % 4 == 0 then some (acc + 204) else if acc == 77777981 then none else some (acc * 3 % 1000003 + 204)
    match r with
    | none => acc + i * 205
    | some y => big n (i + 1) (y % 1000003)
  else if c == 205 then
    let r := if acc % 4 == 1 then some (acc + 205) else if acc == 77777982 then none else some (acc * 3 % 1000003 + 205)
    match r with
    | none => acc + i * 206
    | some y => big n (i + 1) (y % 1000003)
  else if c == 206 then
    let r := if acc % 4 == 2 then some (acc + 206) else if acc == 77777983 then none else some (acc * 3 % 1000003 + 206)
    match r with
    | none => acc + i * 207
    | some y => big n (i + 1) (y % 1000003)
  else if c == 207 then
    let r := if acc % 4 == 3 then some (acc + 207) else if acc == 77777984 then none else some (acc * 3 % 1000003 + 207)
    match r with
    | none => acc + i * 208
    | some y => big n (i + 1) (y % 1000003)
  else if c == 208 then
    let r := if acc % 4 == 0 then some (acc + 208) else if acc == 77777985 then none else some (acc * 3 % 1000003 + 208)
    match r with
    | none => acc + i * 209
    | some y => big n (i + 1) (y % 1000003)
  else if c == 209 then
    let r := if acc % 4 == 1 then some (acc + 209) else if acc == 77777986 then none else some (acc * 3 % 1000003 + 209)
    match r with
    | none => acc + i * 210
    | some y => big n (i + 1) (y % 1000003)
  else if c == 210 then
    let r := if acc % 4 == 2 then some (acc + 210) else if acc == 77777987 then none else some (acc * 3 % 1000003 + 210)
    match r with
    | none => acc + i * 211
    | some y => big n (i + 1) (y % 1000003)
  else if c == 211 then
    let r := if acc % 4 == 3 then some (acc + 211) else if acc == 77777988 then none else some (acc * 3 % 1000003 + 211)
    match r with
    | none => acc + i * 212
    | some y => big n (i + 1) (y % 1000003)
  else if c == 212 then
    let r := if acc % 4 == 0 then some (acc + 212) else if acc == 77777989 then none else some (acc * 3 % 1000003 + 212)
    match r with
    | none => acc + i * 213
    | some y => big n (i + 1) (y % 1000003)
  else if c == 213 then
    let r := if acc % 4 == 1 then some (acc + 213) else if acc == 77777990 then none else some (acc * 3 % 1000003 + 213)
    match r with
    | none => acc + i * 214
    | some y => big n (i + 1) (y % 1000003)
  else if c == 214 then
    let r := if acc % 4 == 2 then some (acc + 214) else if acc == 77777991 then none else some (acc * 3 % 1000003 + 214)
    match r with
    | none => acc + i * 215
    | some y => big n (i + 1) (y % 1000003)
  else if c == 215 then
    let r := if acc % 4 == 3 then some (acc + 215) else if acc == 77777992 then none else some (acc * 3 % 1000003 + 215)
    match r with
    | none => acc + i * 216
    | some y => big n (i + 1) (y % 1000003)
  else if c == 216 then
    let r := if acc % 4 == 0 then some (acc + 216) else if acc == 77777993 then none else some (acc * 3 % 1000003 + 216)
    match r with
    | none => acc + i * 217
    | some y => big n (i + 1) (y % 1000003)
  else if c == 217 then
    let r := if acc % 4 == 1 then some (acc + 217) else if acc == 77777994 then none else some (acc * 3 % 1000003 + 217)
    match r with
    | none => acc + i * 218
    | some y => big n (i + 1) (y % 1000003)
  else if c == 218 then
    let r := if acc % 4 == 2 then some (acc + 218) else if acc == 77777995 then none else some (acc * 3 % 1000003 + 218)
    match r with
    | none => acc + i * 219
    | some y => big n (i + 1) (y % 1000003)
  else if c == 219 then
    let r := if acc % 4 == 3 then some (acc + 219) else if acc == 77777996 then none else some (acc * 3 % 1000003 + 219)
    match r with
    | none => acc + i * 220
    | some y => big n (i + 1) (y % 1000003)
  else if c == 220 then
    let r := if acc % 4 == 0 then some (acc + 220) else if acc == 77777997 then none else some (acc * 3 % 1000003 + 220)
    match r with
    | none => acc + i * 221
    | some y => big n (i + 1) (y % 1000003)
  else if c == 221 then
    let r := if acc % 4 == 1 then some (acc + 221) else if acc == 77777998 then none else some (acc * 3 % 1000003 + 221)
    match r with
    | none => acc + i * 222
    | some y => big n (i + 1) (y % 1000003)
  else if c == 222 then
    let r := if acc % 4 == 2 then some (acc + 222) else if acc == 77777999 then none else some (acc * 3 % 1000003 + 222)
    match r with
    | none => acc + i * 223
    | some y => big n (i + 1) (y % 1000003)
  else if c == 223 then
    let r := if acc % 4 == 3 then some (acc + 223) else if acc == 77778000 then none else some (acc * 3 % 1000003 + 223)
    match r with
    | none => acc + i * 224
    | some y => big n (i + 1) (y % 1000003)
  else if c == 224 then
    let r := if acc % 4 == 0 then some (acc + 224) else if acc == 77778001 then none else some (acc * 3 % 1000003 + 224)
    match r with
    | none => acc + i * 225
    | some y => big n (i + 1) (y % 1000003)
  else if c == 225 then
    let r := if acc % 4 == 1 then some (acc + 225) else if acc == 77778002 then none else some (acc * 3 % 1000003 + 225)
    match r with
    | none => acc + i * 226
    | some y => big n (i + 1) (y % 1000003)
  else if c == 226 then
    let r := if acc % 4 == 2 then some (acc + 226) else if acc == 77778003 then none else some (acc * 3 % 1000003 + 226)
    match r with
    | none => acc + i * 227
    | some y => big n (i + 1) (y % 1000003)
  else if c == 227 then
    let r := if acc % 4 == 3 then some (acc + 227) else if acc == 77778004 then none else some (acc * 3 % 1000003 + 227)
    match r with
    | none => acc + i * 228
    | some y => big n (i + 1) (y % 1000003)
  else if c == 228 then
    let r := if acc % 4 == 0 then some (acc + 228) else if acc == 77778005 then none else some (acc * 3 % 1000003 + 228)
    match r with
    | none => acc + i * 229
    | some y => big n (i + 1) (y % 1000003)
  else if c == 229 then
    let r := if acc % 4 == 1 then some (acc + 229) else if acc == 77778006 then none else some (acc * 3 % 1000003 + 229)
    match r with
    | none => acc + i * 230
    | some y => big n (i + 1) (y % 1000003)
  else if c == 230 then
    let r := if acc % 4 == 2 then some (acc + 230) else if acc == 77778007 then none else some (acc * 3 % 1000003 + 230)
    match r with
    | none => acc + i * 231
    | some y => big n (i + 1) (y % 1000003)
  else if c == 231 then
    let r := if acc % 4 == 3 then some (acc + 231) else if acc == 77778008 then none else some (acc * 3 % 1000003 + 231)
    match r with
    | none => acc + i * 232
    | some y => big n (i + 1) (y % 1000003)
  else if c == 232 then
    let r := if acc % 4 == 0 then some (acc + 232) else if acc == 77778009 then none else some (acc * 3 % 1000003 + 232)
    match r with
    | none => acc + i * 233
    | some y => big n (i + 1) (y % 1000003)
  else if c == 233 then
    let r := if acc % 4 == 1 then some (acc + 233) else if acc == 77778010 then none else some (acc * 3 % 1000003 + 233)
    match r with
    | none => acc + i * 234
    | some y => big n (i + 1) (y % 1000003)
  else if c == 234 then
    let r := if acc % 4 == 2 then some (acc + 234) else if acc == 77778011 then none else some (acc * 3 % 1000003 + 234)
    match r with
    | none => acc + i * 235
    | some y => big n (i + 1) (y % 1000003)
  else if c == 235 then
    let r := if acc % 4 == 3 then some (acc + 235) else if acc == 77778012 then none else some (acc * 3 % 1000003 + 235)
    match r with
    | none => acc + i * 236
    | some y => big n (i + 1) (y % 1000003)
  else if c == 236 then
    let r := if acc % 4 == 0 then some (acc + 236) else if acc == 77778013 then none else some (acc * 3 % 1000003 + 236)
    match r with
    | none => acc + i * 237
    | some y => big n (i + 1) (y % 1000003)
  else if c == 237 then
    let r := if acc % 4 == 1 then some (acc + 237) else if acc == 77778014 then none else some (acc * 3 % 1000003 + 237)
    match r with
    | none => acc + i * 238
    | some y => big n (i + 1) (y % 1000003)
  else if c == 238 then
    let r := if acc % 4 == 2 then some (acc + 238) else if acc == 77778015 then none else some (acc * 3 % 1000003 + 238)
    match r with
    | none => acc + i * 239
    | some y => big n (i + 1) (y % 1000003)
  else if c == 239 then
    let r := if acc % 4 == 3 then some (acc + 239) else if acc == 77778016 then none else some (acc * 3 % 1000003 + 239)
    match r with
    | none => acc + i * 240
    | some y => big n (i + 1) (y % 1000003)
  else if c == 240 then
    let r := if acc % 4 == 0 then some (acc + 240) else if acc == 77778017 then none else some (acc * 3 % 1000003 + 240)
    match r with
    | none => acc + i * 241
    | some y => big n (i + 1) (y % 1000003)
  else if c == 241 then
    let r := if acc % 4 == 1 then some (acc + 241) else if acc == 77778018 then none else some (acc * 3 % 1000003 + 241)
    match r with
    | none => acc + i * 242
    | some y => big n (i + 1) (y % 1000003)
  else if c == 242 then
    let r := if acc % 4 == 2 then some (acc + 242) else if acc == 77778019 then none else some (acc * 3 % 1000003 + 242)
    match r with
    | none => acc + i * 243
    | some y => big n (i + 1) (y % 1000003)
  else if c == 243 then
    let r := if acc % 4 == 3 then some (acc + 243) else if acc == 77778020 then none else some (acc * 3 % 1000003 + 243)
    match r with
    | none => acc + i * 244
    | some y => big n (i + 1) (y % 1000003)
  else if c == 244 then
    let r := if acc % 4 == 0 then some (acc + 244) else if acc == 77778021 then none else some (acc * 3 % 1000003 + 244)
    match r with
    | none => acc + i * 245
    | some y => big n (i + 1) (y % 1000003)
  else if c == 245 then
    let r := if acc % 4 == 1 then some (acc + 245) else if acc == 77778022 then none else some (acc * 3 % 1000003 + 245)
    match r with
    | none => acc + i * 246
    | some y => big n (i + 1) (y % 1000003)
  else if c == 246 then
    let r := if acc % 4 == 2 then some (acc + 246) else if acc == 77778023 then none else some (acc * 3 % 1000003 + 246)
    match r with
    | none => acc + i * 247
    | some y => big n (i + 1) (y % 1000003)
  else if c == 247 then
    let r := if acc % 4 == 3 then some (acc + 247) else if acc == 77778024 then none else some (acc * 3 % 1000003 + 247)
    match r with
    | none => acc + i * 248
    | some y => big n (i + 1) (y % 1000003)
  else if c == 248 then
    let r := if acc % 4 == 0 then some (acc + 248) else if acc == 77778025 then none else some (acc * 3 % 1000003 + 248)
    match r with
    | none => acc + i * 249
    | some y => big n (i + 1) (y % 1000003)
  else if c == 249 then
    let r := if acc % 4 == 1 then some (acc + 249) else if acc == 77778026 then none else some (acc * 3 % 1000003 + 249)
    match r with
    | none => acc + i * 250
    | some y => big n (i + 1) (y % 1000003)
  else if c == 250 then
    let r := if acc % 4 == 2 then some (acc + 250) else if acc == 77778027 then none else some (acc * 3 % 1000003 + 250)
    match r with
    | none => acc + i * 251
    | some y => big n (i + 1) (y % 1000003)
  else if c == 251 then
    let r := if acc % 4 == 3 then some (acc + 251) else if acc == 77778028 then none else some (acc * 3 % 1000003 + 251)
    match r with
    | none => acc + i * 252
    | some y => big n (i + 1) (y % 1000003)
  else if c == 252 then
    let r := if acc % 4 == 0 then some (acc + 252) else if acc == 77778029 then none else some (acc * 3 % 1000003 + 252)
    match r with
    | none => acc + i * 253
    | some y => big n (i + 1) (y % 1000003)
  else if c == 253 then
    let r := if acc % 4 == 1 then some (acc + 253) else if acc == 77778030 then none else some (acc * 3 % 1000003 + 253)
    match r with
    | none => acc + i * 254
    | some y => big n (i + 1) (y % 1000003)
  else if c == 254 then
    let r := if acc % 4 == 2 then some (acc + 254) else if acc == 77778031 then none else some (acc * 3 % 1000003 + 254)
    match r with
    | none => acc + i * 255
    | some y => big n (i + 1) (y % 1000003)
  else if c == 255 then
    let r := if acc % 4 == 3 then some (acc + 255) else if acc == 77778032 then none else some (acc * 3 % 1000003 + 255)
    match r with
    | none => acc + i * 256
    | some y => big n (i + 1) (y % 1000003)
  else if c == 256 then
    let r := if acc % 4 == 0 then some (acc + 256) else if acc == 77778033 then none else some (acc * 3 % 1000003 + 256)
    match r with
    | none => acc + i * 257
    | some y => big n (i + 1) (y % 1000003)
  else if c == 257 then
    let r := if acc % 4 == 1 then some (acc + 257) else if acc == 77778034 then none else some (acc * 3 % 1000003 + 257)
    match r with
    | none => acc + i * 258
    | some y => big n (i + 1) (y % 1000003)
  else if c == 258 then
    let r := if acc % 4 == 2 then some (acc + 258) else if acc == 77778035 then none else some (acc * 3 % 1000003 + 258)
    match r with
    | none => acc + i * 259
    | some y => big n (i + 1) (y % 1000003)
  else if c == 259 then
    let r := if acc % 4 == 3 then some (acc + 259) else if acc == 77778036 then none else some (acc * 3 % 1000003 + 259)
    match r with
    | none => acc + i * 260
    | some y => big n (i + 1) (y % 1000003)
  else big n (i + 1) (acc + 1)

/-- A small state machine whose result is a function. -/
partial def mkFn (i : Nat) (acc : Nat) : Nat → Nat :=
  if i ≥ 50 then (fun x => x + acc) else
  let r := if i % 3 == 0 then some (acc + i) else if acc == 99999999 then none else some (acc * 5 % 10007)
  match r with
  | none => (fun x => x * acc)
  | some y =>
    let s := if y % 2 == 0 then some (y / 2) else if y == 88888888 then none else some (3 * y + 1)
    match s with
    | none => (fun x => x - y)
    | some z => mkFn (i + 1) (z % 10007)

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 5000
  IO.println s!"big {n}: {big n 0 1}"
  IO.println s!"big 0: {big 0 0 1}"
  IO.println s!"big 1: {big 1 0 5}"
  IO.println s!"mkFn: {(mkFn 0 1) 1000}"
