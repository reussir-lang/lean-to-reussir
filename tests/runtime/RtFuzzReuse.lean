/-! Runtime test: a randomly generated data program (fuzzer output, fixed
seed): random 6-10-variant inductives with 0-6 fields of 15 kinds, stepped
20000 times between variants (in-place reuse across layouts), plus
`Array.modify` loops.
From the round-6 adversarial reviewers, area types (adv6/types), fuzzer
genreuse.py, program Ty6Rnd1. -/

-- Random multi-variant inductive with mixed scalar/object fields, stepped in place (seed 1)
inductive V where
  | v0 (f0 : Int) (f1 : Option UInt8) (f2 : Option UInt8) (f3 : UInt16)
  | v1 (f0 : UInt16) (f1 : Nat)
  | v2 (f0 : Nat) (f1 : Nat) (f2 : Int8) (f3 : Bool) (f4 : Option UInt8) (f5 : UInt64)
  | v3
  | v4 (f0 : UInt8) (f1 : UInt8 × Float) (f2 : Int)
  | v5 (f0 : Bool) (f1 : Char) (f2 : Option UInt8)
  | v6 (f0 : UInt8) (f1 : USize) (f2 : Nat) (f3 : Float) (f4 : USize) (f5 : Option UInt8)

@[noinline] def V.sig : V → Nat
  | .v0 f0 f1 f2 f3 => 0 + ((f0 + 2500).toNat) * 3 + ((f1.getD 1).toNat) * 4 + ((f2.getD 1).toNat) * 5 + (f3.toNat) * 6
  | .v1 f0 f1 => 1000 + (f0.toNat) * 3 + (f1) * 4
  | .v2 f0 f1 f2 f3 f4 f5 => 2000 + (f0) * 3 + (f1) * 4 + ((f2.toInt + 128).toNat) * 5 + ((if f3 then 7 else 3)) * 6 + ((f4.getD 1).toNat) * 7 + ((f5 % 1000003).toNat) * 8
  | .v3 => 3000 + 0
  | .v4 f0 f1 f2 => 4000 + (f0.toNat) * 3 + ((f1.1.toNat + f1.2.toUInt64.toNat)) * 4 + ((f2 + 2500).toNat) * 5
  | .v5 f0 f1 f2 => 5000 + ((if f0 then 7 else 3)) * 3 + (f1.toNat) * 4 + ((f2.getD 1).toNat) * 5
  | .v6 f0 f1 f2 f3 f4 f5 => 6000 + (f0.toNat) * 3 + (f1.toNat) * 4 + (f2) * 5 + ((f3 * 8.0).toUInt64.toNat) * 6 + (f4.toNat) * 7 + ((f5.getD 1).toNat) * 8

@[noinline] def V.step (x : V) (salt : Nat) : V :=
  let h := (x.sig * 31 + salt) % 1000000007
  match x with
  | .v0 _ _ _ _ => .v1 (let h := h + 0; (h % 65521).toUInt16) (let h := h + 7; h % 100000)
  | .v1 _ _ => .v4 (let h := h + 0; (h % 251).toUInt8) (let h := h + 7; ((h % 200).toUInt8, (h % 77).toFloat)) (let h := h + 14; Int.ofNat (h % 5000) - 2500)
  | .v2 _ _ _ _ _ _ => .v0 (let h := h + 0; Int.ofNat (h % 5000) - 2500) (let h := h + 7; (if h % 2 == 0 then some (h % 200).toUInt8 else none)) (let h := h + 14; (if h % 2 == 0 then some (h % 200).toUInt8 else none)) (let h := h + 21; (h % 65521).toUInt16)
  | .v3 => .v2 (let h := h + 0; h % 100000) (let h := h + 7; h % 100000) (let h := h + 14; Int8.ofInt (Int.ofNat (h % 200) - 100)) (let h := h + 21; (h % 3 == 1)) (let h := h + 28; (if h % 2 == 0 then some (h % 200).toUInt8 else none)) (let h := h + 35; h.toUInt64 * 2654435761)
  | .v4 _ _ _ => .v0 (let h := h + 0; Int.ofNat (h % 5000) - 2500) (let h := h + 7; (if h % 2 == 0 then some (h % 200).toUInt8 else none)) (let h := h + 14; (if h % 2 == 0 then some (h % 200).toUInt8 else none)) (let h := h + 21; (h % 65521).toUInt16)
  | .v5 _ _ _ => .v0 (let h := h + 0; Int.ofNat (h % 5000) - 2500) (let h := h + 7; (if h % 2 == 0 then some (h % 200).toUInt8 else none)) (let h := h + 14; (if h % 2 == 0 then some (h % 200).toUInt8 else none)) (let h := h + 21; (h % 65521).toUInt16)
  | .v6 _ _ _ _ _ _ => .v0 (let h := h + 0; Int.ofNat (h % 5000) - 2500) (let h := h + 7; (if h % 2 == 0 then some (h % 200).toUInt8 else none)) (let h := h + 14; (if h % 2 == 0 then some (h % 200).toUInt8 else none)) (let h := h + 21; (h % 65521).toUInt16)

@[noinline] def run (n : Nat) (x : V) (acc : Nat) : Nat × V :=
  match n with
  | 0 => (acc, x)
  | n + 1 => let y := x.step n; run n y ((acc * 7 + y.sig) % 1000000007)

@[noinline] def runArr (n : Nat) (xs : Array V) : Array V := Id.run do
  let mut xs := xs
  for i in [0:n] do
    let j := i % xs.size
    xs := xs.modify j (fun v => v.step i)
  return xs

def main (args : List String) : IO Unit := do
  let k := args.length
  let x0 : V := .v0 (let h := 0 + k; Int.ofNat (h % 5000) - 2500) (let h := 11 + k; (if h % 2 == 0 then some (h % 200).toUInt8 else none)) (let h := 22 + k; (if h % 2 == 0 then some (h % 200).toUInt8 else none)) (let h := 33 + k; (h % 65521).toUInt16)
  let (acc0, fin0) := run (20000 + k) x0 0
  IO.println s!"0 {acc0} {fin0.sig}"
  let x1 : V := .v1 (let h := 1 + k; (h % 65521).toUInt16) (let h := 12 + k; h % 100000)
  let (acc1, fin1) := run (20000 + k) x1 0
  IO.println s!"1 {acc1} {fin1.sig}"
  let x2 : V := .v2 (let h := 2 + k; h % 100000) (let h := 13 + k; h % 100000) (let h := 24 + k; Int8.ofInt (Int.ofNat (h % 200) - 100)) (let h := 35 + k; (h % 3 == 1)) (let h := 46 + k; (if h % 2 == 0 then some (h % 200).toUInt8 else none)) (let h := 57 + k; h.toUInt64 * 2654435761)
  let (acc2, fin2) := run (20000 + k) x2 0
  IO.println s!"2 {acc2} {fin2.sig}"
  let x3 : V := .v3
  let (acc3, fin3) := run (20000 + k) x3 0
  IO.println s!"3 {acc3} {fin3.sig}"
  let x4 : V := .v4 (let h := 4 + k; (h % 251).toUInt8) (let h := 15 + k; ((h % 200).toUInt8, (h % 77).toFloat)) (let h := 26 + k; Int.ofNat (h % 5000) - 2500)
  let (acc4, fin4) := run (20000 + k) x4 0
  IO.println s!"4 {acc4} {fin4.sig}"
  let x5 : V := .v5 (let h := 5 + k; (h % 3 == 1)) (let h := 16 + k; Char.ofNat (h % 50 + 65)) (let h := 27 + k; (if h % 2 == 0 then some (h % 200).toUInt8 else none))
  let (acc5, fin5) := run (20000 + k) x5 0
  IO.println s!"5 {acc5} {fin5.sig}"
  let x6 : V := .v6 (let h := 6 + k; (h % 251).toUInt8) (let h := 17 + k; (h % 99991).toUSize) (let h := 28 + k; h % 100000) (let h := 39 + k; (h % 1000).toFloat / 8.0) (let h := 50 + k; (h % 99991).toUSize) (let h := 61 + k; (if h % 2 == 0 then some (h % 200).toUInt8 else none))
  let (acc6, fin6) := run (20000 + k) x6 0
  IO.println s!"6 {acc6} {fin6.sig}"
  let arr := runArr 5000 #[x0, x1, x2, x3, x4, x5, x6]
  IO.println s!"arr {arr.map V.sig}"

