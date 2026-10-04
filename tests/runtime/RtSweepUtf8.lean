/-! Runtime test: UTF-8 sweep. DUtf8: 4000 byte arrays from a fixed LCG,
biased to lead/continuation/invalid bytes, through `validateUTF8`,
`String.fromUTF8?`,
`ByteArray.hash`, `String.hash` and lengths; well-formed boundary code points;
the `fromUTF8!` panic. T30Utf8: 32 hand-picked sequences (overlong forms,
surrogates, > U+10FFFF, truncated, stray continuation bytes, NUL), raw
positions inside multi-byte characters, `Substring.Raw` and
`String.Legacy.Iterator` with mid-character bounds.
From the round-7 review, area D (rv7/rtdata, check DUtf8), and the round-6
adversarial reviewers, area stdlib (adv6/stdlib, T30Utf8).
The review's program also ran the lossy decoder `lean_decode_lossy_utf8`
through an `@[extern "lean_decode_lossy_utf8"] opaque` of its own. An
extern of the program is never bound to Lean's runtime (translation plan
§5.8, "Externs of the program"), so that declaration is refused, and Lean's
own declaration of it (`Lean.decodeLossyUTF8`) is private to `Lean.Shell`:
no program reaches the function, and this test no longer prints it. -/

namespace DUtf8
-- from rv7/rtdata/DUtf8.lean
-- UTF-8 validation, strict decoding, hashing of random byte arrays.

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def special : Array UInt8 := #[0x00, 0x41, 0x7F, 0x80, 0x8F, 0x9F, 0xA0, 0xBF, 0xC0, 0xC1, 0xC2, 0xDF, 0xE0, 0xE1, 0xED, 0xEE, 0xEF, 0xF0, 0xF1, 0xF4, 0xF5, 0xF7, 0xF8, 0xFB, 0xFC, 0xFE, 0xFF]

def mkBytes (seed : UInt64) (n : Nat) : ByteArray := Id.run do
  let mut s := seed
  let mut b := ByteArray.empty
  for _ in [0:n] do
    s := lcg s
    let r := (s >>> 33)
    let byte : UInt8 := if r % 3 == 0 then (r >>> 8).toUInt8 else special[((r >>> 8) % special.size.toUInt64).toNat]!
    b := b.push byte
  return b

def main : IO Unit := do
  let mut valid := 0
  for k in [0:4000] do
    let b := mkBytes (k.toUInt64 * 7919 + 1) (k % 13)
    let v := b.validateUTF8
    let line := s!"{k} {b.toList} v={v} h={b.hash}"
    match String.fromUTF8? b with
    | some s =>
      valid := valid + 1
      IO.println (line ++ s!" ok {s.length} {s.toList.map Char.toNat} {hash s} {s.utf8ByteSize}")
    | none => IO.println (line ++ " none")
  IO.println s!"valid {valid}"
  -- some well-formed multi-byte sequences built from code points
  for c in [0x7F, 0x80, 0x7FF, 0x800, 0xFFFF, 0x10000, 0x10FFFF, 0xD7FF, 0xE000] do
    let s := String.singleton (Char.ofNat c)
    IO.println s!"{c} {s.toUTF8.toList} {s.toUTF8.validateUTF8} {(String.fromUTF8? s.toUTF8).map (·.toList.map Char.toNat)}"
  let bad := ByteArray.mk #[0x61, 0xC0, 0x80, 0x62]
  IO.println s!"bang {(String.fromUTF8! bad).length}"
end DUtf8

namespace T30Utf8
-- from adv6/stdlib/T30Utf8.lean
def P (n : Nat) : String.Pos.Raw := ⟨n⟩

def showOpt : Option String → String
  | some s => s!"ok[{s.quote}]"
  | none => "none"

def main (args : List String) : IO Unit := do
  let k := (args.head?.bind String.toNat?).getD 0
  let seqs : List (List UInt8) := [[0x41], [0xC0, 0x80], [0xC1, 0xBF], [0xC2, 0x80], [0xDF, 0xBF], [0xE0, 0x80, 0x80], [0xE0, 0x9F, 0xBF], [0xE0, 0xA0, 0x80],
    [0xED, 0x9F, 0xBF], [0xED, 0xA0, 0x80], [0xED, 0xBF, 0xBF], [0xEE, 0x80, 0x80], [0xEF, 0xBF, 0xBF], [0xF0, 0x80, 0x80, 0x80], [0xF0, 0x8F, 0xBF, 0xBF], [0xF0, 0x90, 0x80, 0x80],
    [0xF4, 0x8F, 0xBF, 0xBF], [0xF4, 0x90, 0x80, 0x80], [0xF5, 0x80, 0x80, 0x80], [0xF8, 0x88, 0x80, 0x80, 0x80], [0xFF], [0xFE], [0x80], [0xBF], [0xE6, 0x97], [0xE6, 0x97, 0xA5, 0x80],
    [0x00], [0x00, 0x00, 0x41], [0xC2], [0xF0, 0x9F, 0x98], [0x61, 0xE6, 0x97, 0xA5, 0x62], [0xE6, 0x41, 0xA5]]
  for sq in seqs do
    let b : ByteArray := ⟨sq.toArray.push (UInt8.ofNat k) |>.pop⟩
    IO.println s!"u {sq} valid={String.validateUTF8 b} from={showOpt (String.fromUTF8? b)}"
  -- positions inside multibyte chars
  let s := "a日本🎉b"
  for i in [0:13] do
    IO.println s!"p {i} get={(P i).get s |>.toNat} get?={((P i).get? s).map Char.toNat} next={(P i).next s} prev={(P i).prev s} atEnd={(P i).atEnd s} valid={(P i).isValid s}"
  -- set/modify at mid-char positions
  IO.println s!"m {(P 2).set s 'X'} {(P 1).set s 'X'} {(P 4).set s '€'} {(P 8).set s 'Y'} {(P 13).set s 'Z'} {(P 1).modify s Char.toUpper} {(P 0).modify s Char.toUpper}"
  IO.println s!"e {String.Pos.Raw.extract s (P 1) (P 4)} {String.Pos.Raw.extract s (P 2) (P 7)} {String.Pos.Raw.extract s (P 0) (P 3)} {String.Pos.Raw.extract s (P 4) (P 12)} {String.Pos.Raw.extract s (P 8) (P 9)} {String.Pos.Raw.extract s (P 0) (P 100)}"
  -- substring with mid-char bounds
  let sub : Substring.Raw := ⟨s, P 2, P 9⟩
  IO.println s!"sb {sub.toString} {sub.bsize} {sub.isEmpty} {sub.front} {sub.toString.length} {(sub.drop 1).toString} {sub.takeWhile (fun _ => true) |>.toString}"
  -- legacy iterator at mid-char
  let it : String.Legacy.Iterator := ⟨s, P 2⟩
  IO.println s!"it {it.curr.toNat} {it.next.pos} {it.prev.pos} {it.atEnd} {it.hasNext} {it.remainingToString}"
  -- utf8 encode/decode of chars
  let cs : List Char := ['\x00', 'a', '\x7f', Char.ofNat 0x80, Char.ofNat 0x7ff, Char.ofNat 0x800, Char.ofNat 0xffff, Char.ofNat 0x10000, Char.ofNat 0x10ffff]
  IO.println s!"enc {cs.map (fun c => (String.singleton c).toUTF8.toList)} {cs.map Char.utf8Size}"
  IO.println s!"dec {cs.map (fun c => (String.fromUTF8? (String.singleton c).toUTF8).map (·.length))}"
  IO.println s!"len {(String.ofList cs).length} {(String.ofList cs).utf8ByteSize} {(String.ofList cs).toUTF8.size}"
end T30Utf8

def main : IO Unit := do
  IO.println "=== DUtf8"
  DUtf8.main
  IO.println "=== T30Utf8"
  T30Utf8.main []
