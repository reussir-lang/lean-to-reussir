/-! Runtime test: `String.Pos.Raw` sweep. `get`/`get?`/`next`/`prev`/
`isValid`/`atEnd`/`set` (1-, 3- and 4-byte characters)/`modify`/
`offsetOfPos` at every byte position (+3 past the end, and at 2^63-1, 2^63,
2^64-1, 2^64, 2^100), and `extract` over all position pairs below 2^63, of 22
strings mixing 1..4-byte characters, NUL and U+10FFFF (generated with a
fixed LCG seed).
From the round-7 review, area D (rv7/rtdata), check DStrPos. -/

-- String.Pos.Raw operations at every byte position (valid, mid-character,
-- past the end, huge) of strings mixing 1..4-byte characters.
def cps : List Nat := [0x41, 0x7F, 0x80, 0x7FF, 0x800, 0xD7FF, 0xE000, 0xFFFD, 0xFFFF, 0x10000, 0x10FFFF, 0, 0x20AC, 0x1F600]

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def mkStr (seed : UInt64) (n : Nat) : String := Id.run do
  let mut s := seed
  let mut r := ""
  for _ in [0:n] do
    s := lcg s
    let i := (s >>> 33).toNat % cps.length
    r := r.push (Char.ofNat (cps.getD i 65))
  return r

def showC (c : Char) : String := toString c.toNat

def showO (o : Option Char) : String := match o with | some c => showC c | none => "none"

def bytesOf (s : String) : String := toString s.toUTF8.toList

def main : IO Unit := do
  let mut strs : Array String := #["", "a", "é", "€", "😀", "aé€😀b", "\x00", "a\x00b", "€€", "😀😀x"]
  for k in [0:12] do
    strs := strs.push (mkStr (k.toUInt64 * 977 + 3) (k % 7 + 1))
  let big : List Nat := [2^63 - 1, 2^63, 2^64 - 1, 2^64, 2^100]
  for s in strs do
    IO.println s!"== {bytesOf s} len {s.length} size {s.utf8ByteSize}"
    let n := s.utf8ByteSize
    let ps := (List.range (n + 3)) ++ big
    for p in ps do
      let q : String.Pos.Raw := ⟨p⟩
      let line := s!"{p}: get {showC (q.get s)} get? {showO (q.get? s)} next {(q.next s).byteIdx} prev {(q.prev s).byteIdx} valid {q.isValid s} atEnd {q.atEnd s}"
      IO.println line
      IO.println s!"   setZ {bytesOf (q.set s 'Z')} setE {bytesOf (q.set s '€')} setS {bytesOf (q.set s '😀')} mod {bytesOf (q.modify s Char.toUpper)}"
      IO.println s!"   lenZ {(q.set s 'Z').length} lenS {(q.set s '😀').length} off {String.Pos.Raw.offsetOfPos s q}"
      for e in ps do
        let r := if p < 2^63 && e < 2^63 then q.extract s ⟨e⟩ else "skip"
        IO.print s!" {r.utf8ByteSize}/{r.length}"
      IO.println ""

