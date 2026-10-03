/-! Runtime test: string fuzzing with fixed LCG seeds. DFuzzStr: 20000 random
string operations over a pool of shared versions (push, append, Pos set/
modify/extract, drop/dropEnd, replace, splitOn + intercalate, UTF-8 round
trip, reverse, pushn, trimAscii, take/takeEnd, join, map). DStrSearch: 1500
random strings over {a, b, é, €, 😀, space} with random patterns: splitOn,
replace, contains, startsWith/endsWith, find, takeWhile/dropWhile,
Slice.split, trimAscii, revFind?, dropEnd, toUpper/capitalize/decapitalize.
From the round-7 review, area D (rv7/rtdata), checks DFuzzStr and
DStrSearch. -/

namespace DFuzzStr
-- from rv7/rtdata/DFuzzStr.lean
-- Random sequences of string operations over a pool of shared versions.
def cps : Array Nat := #[0x41, 0x61, 0x20, 0x7F, 0x80, 0x7FF, 0x800, 0x20AC, 0xFFFD, 0x10000, 0x1F600, 0x10FFFF, 0xE9, 0x0A]

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

structure St where
  seed : UInt64
  pool : Array String

def rnd (st : St) (n : Nat) : Nat × St :=
  let s := lcg st.seed
  (((s >>> 33).toNat % (max n 1)), { st with seed := s })

def digest (p : Array String) : UInt64 :=
  p.foldl (fun h s => mixHash (mixHash h (hash s)) s.length.toUInt64) 17

def step (st : St) : St := Id.run do
  let (op, st) := rnd st 16
  let (i, st) := rnd st st.pool.size
  let (j, st) := rnd st st.pool.size
  let (k, st) := rnd st (st.pool.size)
  let (c, st) := rnd st cps.size
  let (p, st) := rnd st 40
  let (q, st) := rnd st 40
  let s := st.pool[i]!
  let t := st.pool[j]!
  let ch := Char.ofNat cps[c]!
  let r : String := match op with
    | 0 => s.push ch
    | 1 => s ++ t
    | 2 => String.Pos.Raw.set s ⟨p⟩ ch
    | 3 => String.Pos.Raw.extract s ⟨p⟩ ⟨q⟩
    | 4 => (s.drop p).copy
    | 5 => (s.dropEnd p).copy
    | 6 => s.replace "a" "€"
    | 7 => "|".intercalate (s.splitOn " ")
    | 8 => match String.fromUTF8? (s.toUTF8.push 0x41) with | some x => x | none => "bad"
    | 9 => String.Pos.Raw.modify s ⟨p⟩ Char.toUpper
    | 10 => String.ofList s.toList.reverse
    | 11 => s.pushn ch (p % 5)
    | 12 => s.trimAscii.copy
    | 13 => (s.take q).copy ++ (t.takeEnd p).copy
    | 14 => String.join [s, t, s]
    | _ => s.map (fun x => if x == 'A' then 'Z' else x)
  let r := if r.length > 300 then (r.take 50).copy else r
  { st with pool := st.pool.set! k r }

def main : IO Unit := do
  let mut st : St := { seed := 12345, pool := #["", "a", "abc a", "é€😀", " x y ", "AaA", "€uro", "\x00z"] }
  for n in [0:20000] do
    st := step st
    if n % 500 == 0 then
      IO.println s!"{n} {digest st.pool} {st.pool.map String.length}"
  for s in st.pool do
    IO.println s!"{s.toUTF8.toList}"
end DFuzzStr

namespace DStrSearch
-- from rv7/rtdata/DStrSearch.lean
-- Searching and splitting random strings over a small alphabet with
-- multi-byte characters, with random patterns.
def alpha : Array Char := #['a', 'b', 'é', '€', '😀', ' ', 'a', 'b']

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def rstr (seed : UInt64) (n : Nat) : String × UInt64 := Id.run do
  let mut s := seed
  let mut r := ""
  for _ in [0:n] do
    s := lcg s
    r := r.push alpha[((s >>> 33) % alpha.size.toUInt64).toNat]!
  return (r, s)

def main : IO Unit := do
  let mut seed : UInt64 := 99
  let mut h : UInt64 := 0
  for k in [0:1500] do
    let (s, s1) := rstr seed (k % 13)
    let (p, s2) := rstr s1 (k % 4)
    seed := s2
    let parts := s.splitOn p
    let rep := s.replace p "<>"
    let c := s.contains p
    let sw := s.startsWith p
    let ew := s.endsWith p
    let f := (s.find p).offset.byteIdx
    let tw := (s.takeWhile (· != 'é')).copy
    let dw := (s.dropWhile (· == 'a')).copy
    let sp := (s.toSlice.split ' ').toList.map (·.copy)
    let tr := s.trimAscii.copy
    let r := (s.revFind? (· == (Char.ofNat 98))).map (·.offset.byteIdx)
    let line := s!"{k} [{s}] [{p}] {parts} {rep} {c} {sw} {ew} {f} {tw} {dw} {sp} [{tr}] {r} {s.length} {(s.dropEnd 1).copy} {s.toUpper} {s.capitalize} {s.decapitalize}"
    h := mixHash h (hash line)
    if k % 10 == 0 then IO.println line
  IO.println s!"h {h}"
end DStrSearch

def main : IO Unit := do
  IO.println "=== DFuzzStr"
  DFuzzStr.main
  IO.println "=== DStrSearch"
  DStrSearch.main
