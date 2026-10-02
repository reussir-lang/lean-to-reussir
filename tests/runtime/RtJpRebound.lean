/-! Runtime test: an outlined join point declared inside a `match`
alternative that binds the matched variable again, jumping to an outlined
join point declared before the match that uses that variable (round 6
IO6-14, every `Std.Http` program). The outer join point's jumps pass the
variable under its name before the match; the inner join point must capture
it under that name too. lean2rr outlines both (translation plan §5.6, J3:
some paths return directly, and the bodies are too large to duplicate) and
sinks the inner one into the alternative.
- `f`: the alternative of a constructor without fields uses the matched
  value, which is bound again to that constructor there
  (`nullary-scrutinee`);
- `g`: a value of a type that depends on another argument (statically
  unknown, so boxed) is matched, and bound again to its converted value. -/

inductive Dir where
  | recv | send

@[noinline] def h (x y : Nat) : Nat := (x * 31 + y) % 1000003
@[noinline] def dirNum : Dir → Nat
  | .recv => 1
  | .send => 2

def f (d : Dir) (n : Nat) : Nat := Id.run do
  let mut acc := n
  match d with
  | .recv =>
    if n % 7 == 0 then return 0
    let mut t := n + dirNum d
    if n % 3 == 0 then
      if n % 5 == 0 then return 1
      t := t + 1
    t := h (h (h (h (h (h (h (h (h t 3) 6) 9) 12) 15) 18) 21) 24) 27
    t := h (h (h (h (h (h (h (h (h t 30) 33) 36) 39) 42) 45) 48) 51) 54
    t := h (h (h (h (h (h (h (h (h t 57) 60) 63) 66) 69) 72) 75) 78) 81
    t := h (h (h (h (h (h (h (h (h t 84) 87) 90) 93) 96) 99) 102) 105) 108
    t := h (h (h (h (h (h (h (h (h t 111) 114) 117) 120) 123) 126) 129) 132) 135
    acc := t + dirNum d
  | .send =>
    acc := acc + 2
  acc := h (h (h (h (h (h (h (h (h acc 7) 14) 21) 28) 35) 42) 49) 56) 63
  acc := h (h (h (h (h (h (h (h (h acc 70) 77) 84) 91) 98) 105) 112) 119) 126
  acc := h (h (h (h (h (h (h (h (h acc 133) 140) 147) 154) 161) 168) 175) 182) 189
  acc := h (h (h (h (h (h (h (h (h acc 196) 203) 210) 217) 224) 231) 238) 245) 252
  acc := h (h (h (h (h (h (h (h (h acc 259) 266) 273) 280) 287) 294) 301) 308) 315
  return acc + dirNum d

def Payload : Dir → Type
  | .recv => Nat × Nat
  | .send => String

@[noinline] def payloadNum : (d : Dir) → Payload d → Nat
  | .recv, (a, b) => a * 2 + b
  | .send, s => s.length

def g (d : Dir) (p : Payload d) (n : Nat) : Nat := Id.run do
  let mut acc := n
  match d, p with
  | .recv, (a, b) =>
    if n % 7 == 0 then return a
    let mut t := n + b
    if n % 3 == 0 then
      if n % 5 == 0 then return 1
      t := t + 1
    t := h (h (h (h (h (h (h (h (h t 5) 10) 15) 20) 25) 30) 35) 40) 45
    t := h (h (h (h (h (h (h (h (h t 50) 55) 60) 65) 70) 75) 80) 85) 90
    t := h (h (h (h (h (h (h (h (h t 95) 100) 105) 110) 115) 120) 125) 130) 135
    t := h (h (h (h (h (h (h (h (h t 140) 145) 150) 155) 160) 165) 170) 175) 180
    t := h (h (h (h (h (h (h (h (h t 185) 190) 195) 200) 205) 210) 215) 220) 225
    acc := t
  | .send, s =>
    acc := acc + s.length
  acc := h (h (h (h (h (h (h (h (h acc 11) 22) 33) 44) 55) 66) 77) 88) 99
  acc := h (h (h (h (h (h (h (h (h acc 110) 121) 132) 143) 154) 165) 176) 187) 198
  acc := h (h (h (h (h (h (h (h (h acc 209) 220) 231) 242) 253) 264) 275) 286) 297
  acc := h (h (h (h (h (h (h (h (h acc 308) 319) 330) 341) 352) 363) 374) 385) 396
  acc := h (h (h (h (h (h (h (h (h acc 407) 418) 429) 440) 451) 462) 473) 484) 495
  return acc + payloadNum d p

def main : IO Unit := do
  for n in [0:40] do
    IO.println s!"{n}: {f .recv n} {f .send n} {g .recv (n, n + 1) n} {g .send (toString n) n}"
