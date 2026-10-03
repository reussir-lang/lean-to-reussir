import Std.Data.ByteSlice

/-! Runtime test: string externs called directly over many strings and
offsets. DInternal: every `String.Internal.*` (trim with non-ASCII/VT/FF
spaces, drop/dropRight/offsetOfPos/nextWhile/get/next/atEnd at 12 counts
including 2^63, 2^64 and 2^70, posOf/contains/any/pushn per character, foldl,
isPrefixOf, intercalate, append, extract) and `Substring.Raw.Internal.*` on
odd bounds (start > stop, mid-character, past the end), `Pos.Raw.Internal`
sub/min. DSlice: `String.Slice` hash, `<`, `compare`, `==` over 176 slices,
`ByteSlice` `==` over 120 slices with clamped bounds.
From the round-7 review, area D (rv7/rtdata), checks DInternal and DSlice. -/

namespace DInternal
-- from rv7/rtdata/DInternal.lean
-- The String.Internal.* / Substring.Raw.Internal.* / Pos.Raw.Internal.*
-- externs, called directly (the prelude hand-writes the String.Internal ones;
-- natively they are exported Lean definitions).
open String.Internal in
def strs : List String := ["", " ", "a", " a ", "\t\n\r a b \r\n\t", "\x0B a \x0C", " x ", "　y　", "   ", "é", "aé€😀b", " é ", "😀😀", "x\x00y", "abc", "ABC", "élan", "€uro"]

def chars : List Char := ['a', 'é', '€', '😀', ' ', '\x00', 'z', 'b']

def nums : List Nat := [0, 1, 2, 3, 4, 5, 7, 100, 2^63 - 1, 2^63, 2^64, 2^70]

def bs (s : String) : String := toString s.toUTF8.toList

def main : IO Unit := do
  for s in strs do
    IO.println s!"== {bs s}"
    IO.println s!" trim {bs (String.Internal.trim s)} {(String.Internal.trim s).length} cap {bs (String.Internal.capitalize s)} front {(String.Internal.front s).toNat} empty {String.Internal.isEmpty s} len {String.Internal.length s}"
    for n in nums do
      let d := String.Internal.drop s n
      let r := String.Internal.dropRight s n
      IO.println s!" n={n} drop {bs d}/{d.length} dropRight {bs r}/{r.length} off {String.Internal.offsetOfPos s ⟨n⟩} nw {(String.Internal.nextWhile s (· == ' ') ⟨n⟩).byteIdx} nw2 {(String.Internal.nextWhile s (fun c => c != 'b') ⟨n⟩).byteIdx} atEnd {String.Internal.atEnd s ⟨n⟩} get {(String.Internal.get s ⟨n⟩).toNat} next {(String.Internal.next s ⟨n⟩).byteIdx}"
    for c in chars do
      IO.println s!" c={c.toNat} posOf {(String.Internal.posOf s c).byteIdx} contains {String.Internal.contains s c} any {String.Internal.any s (· == c)} pushn0 {bs (String.Internal.pushn s c 0)} pushn3 {bs (String.Internal.pushn s c 3)} {(String.Internal.pushn s c 3).length}"
    let f := String.Internal.foldl (fun acc ch => acc.push ch |>.push '|') "" s
    IO.println s!" foldl {bs f} {f.length}"
    for t in strs do
      if String.Internal.isPrefixOf t s then IO.print s!" pre:{bs t}"
    IO.println ""
    IO.println s!" icat {bs (String.Internal.intercalate s [])} {bs (String.Internal.intercalate s ["x"])} {bs (String.Internal.intercalate s ["x", "", "é"])} app {bs (String.Internal.append s s)} {(String.Internal.append s s).length}"
    -- extract with positions below 2^63
    for b in [0, 1, 2, 3, 5, 100] do
      for e in [0, 1, 2, 4, 6, 100, 2^63 - 1] do
        let x := String.Internal.extract s ⟨b⟩ ⟨e⟩
        IO.print s!" {x.utf8ByteSize}/{x.length}"
    IO.println ""
    -- substrings with odd bounds
    for b in [0, 1, 2, 3, 5, 100] do
      for e in [0, 1, 2, 4, 6, 100] do
        let ss : Substring.Raw := ⟨s, ⟨b⟩, ⟨e⟩⟩
        let t := Substring.Raw.Internal.toString ss
        let d := Substring.Raw.Internal.drop ss 1
        let tw := Substring.Raw.Internal.takeWhile ss (· != ' ')
        let ex := Substring.Raw.Internal.extract ss ⟨1⟩ ⟨3⟩
        IO.println s!"  [{b},{e}] str {bs t} drop {d.startPos.byteIdx},{d.stopPos.byteIdx} front {(Substring.Raw.Internal.front ss).toNat} tw {tw.startPos.byteIdx},{tw.stopPos.byteIdx} ex {ex.startPos.byteIdx},{ex.stopPos.byteIdx} all {Substring.Raw.Internal.all ss (· != 'é')} empty {Substring.Raw.Internal.isEmpty ss} get1 {(Substring.Raw.Internal.get ss ⟨1⟩).toNat} prev2 {(Substring.Raw.Internal.prev ss ⟨2⟩).byteIdx} beq {Substring.Raw.Internal.beq ss ⟨s, ⟨0⟩, ⟨e⟩⟩}"
  for a in nums do
    for b in nums do
      IO.print s!" {(String.Pos.Raw.Internal.sub ⟨a⟩ ⟨b⟩).byteIdx}/{(String.Pos.Raw.Internal.min ⟨a⟩ ⟨b⟩).byteIdx}"
  IO.println ""
end DInternal

namespace DSlice
-- from rv7/rtdata/DSlice.lean
-- String.Slice hash / < / compare and ByteSlice == at many offsets.
def strs : List String := ["", "a", "ab", "abc", "aé€😀b", "é", "😀😀x", "zzz", "a\x00b", "abd", "abcabcabcabcabcabcabc"]

def main : IO Unit := do
  let mut sl : Array String.Slice := #[]
  for s in strs do
    for d in [0, 1, 2, 3] do
      for t in [0, 1, 2, 5] do
        sl := sl.push ((s.toSlice.drop d).dropEnd t)
  IO.println s!"{sl.size} slices"
  for x in sl do
    IO.println s!"{x.copy.toUTF8.toList} h={hash x} sh={hash x.copy} start={x.startInclusive.offset.byteIdx} end={x.endExclusive.offset.byteIdx}"
  let mut lt := 0
  let mut acc : UInt64 := 7
  for x in sl do
    for y in sl do
      let a := decide (x < y)
      let b := decide (x.copy < y.copy)
      if a != b then IO.println s!"LT MISMATCH {x.copy} {y.copy}"
      if a then lt := lt + 1
      acc := mixHash acc (if a then 1 else 2)
      acc := mixHash acc (match compare x y with | .lt => 3 | .eq => 4 | .gt => 5)
      acc := mixHash acc (if x == y then 6 else 8)
  IO.println s!"lt {lt} acc {acc}"
  -- ByteSlice equality
  let arrs : List ByteArray := [ByteArray.mk #[], ByteArray.mk #[1, 2, 3, 1, 2, 3], ByteArray.mk #[1, 2, 3, 4], ByteArray.mk #[0, 1, 2, 3, 1, 2]]
  let mut bsl : Array ByteSlice := #[]
  for a in arrs do
    for st in [0, 1, 2, 3, 7] do
      for sp in [0, 2, 3, 4, 6, 9] do
        bsl := bsl.push (a.toByteSlice st sp)
  let mut eqs := 0
  let mut h : UInt64 := 1
  for x in bsl do
    for y in bsl do
      let e := x == y
      if e != (x.toByteArray == y.toByteArray) then IO.println s!"BEQ MISMATCH {x.toByteArray.toList} {y.toByteArray.toList}"
      if e then eqs := eqs + 1
      h := mixHash h (if e then 11 else 13)
  IO.println s!"bslices {bsl.size} eqs {eqs} h {h}"
  for x in bsl do
    IO.print s!" {x.start},{x.stop},{x.size}:{x.toByteArray.toList}"
  IO.println ""
end DSlice

def main : IO Unit := do
  IO.println "=== DInternal"
  DInternal.main
  IO.println "=== DSlice"
  DSlice.main
