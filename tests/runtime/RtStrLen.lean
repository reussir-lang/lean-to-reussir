/-! Runtime test: `String.length` after every way of building or changing a
string (the runtime keeps the character count, like Lean's `m_length`):
pushes and appends of every UTF-8 width on unique and shared strings,
`set`/`modify`/`map` replacing characters of one width by another (in place,
copied, out of range, inside a character), slices, trimming, case mapping,
byte-array round trips, number formatting, file contents and
command-line arguments, short and long strings. -/

def widths : List Char := ['a', 'é', '€', '𝄞']

def report (tag : String) (s : String) : IO Unit :=
  IO.println s!"{tag}: {repr s} length {s.length} bytes {s.utf8ByteSize} chars {s.toList.length}"

def main (args : List String) : IO Unit := do
  for a in args do report "arg" a
  -- pushes of every width, onto unique and shared strings
  let mut u := ""
  for c in widths ++ widths.reverse do
    u := u.push c
    report "push" u
  let shared := u
  let v := shared.push 'x'
  report "pushShared" v
  report "pushSharedOrig" shared
  -- appends: unique/shared, empty sides, multi-byte
  report "append" (u ++ "日本" ++ "" ++ u)
  report "appendEmpty" ("" ++ "" ++ "")
  report "appendShared" (shared ++ shared)
  -- set/modify: every width over every width, at a boundary, inside a
  -- character, past the end; the original stays intact
  for o in widths do
    for n in widths do
      let base := "x" ++ String.singleton o ++ "y" ++ String.singleton o
      report s!"set {o}->{n}" ((String.Pos.Raw.mk 1).set base n)
      report s!"setInside {o}->{n}" ((String.Pos.Raw.mk 2).set base n)
      report s!"setEnd {o}->{n}" ((String.Pos.Raw.mk 99).set base n)
      report s!"modify {o}->{n}" ((String.Pos.Raw.mk 1).modify base (fun _ => n))
      report s!"base {o}" base
  -- map changing widths in both directions, case mapping
  let mixed := "aébc€d𝄞e ÀÉÎ straße ǆ"
  report "mapWide" (mixed.map (fun c => if c.toNat < 128 then '𝄞' else 'a'))
  report "mapNarrow" (mixed.map (fun c => if c.toNat < 128 then c else 'z'))
  report "upper" mixed.toUpper
  report "lower" mixed.toLower
  report "capitalize" "élan".capitalize
  report "capitalize2" "abc".capitalize
  report "decapitalize" "ABC".decapitalize
  -- slices, trimming, splitting, replacing
  report "drop" (mixed.drop 3).copy
  report "take" (mixed.take 5).copy
  report "dropEnd" (mixed.dropEnd 4).copy
  report "extract" ((String.Pos.Raw.mk 1).extract mixed (String.Pos.Raw.mk 9))
  report "extractInside" ((String.Pos.Raw.mk 2).extract mixed (String.Pos.Raw.mk 9))
  report "trim" "  \t é € \n ".trimAscii.copy
  report "trimAll" "   ".trimAscii.copy
  for piece in mixed.splitOn " " do report "split" piece
  report "replace" (mixed.replace "é" "eee")
  report "pushn" ("é".pushn '€' 5)
  report "intercalate" (", ".intercalate ["é", "€", "𝄞"])
  report "join" (String.join ["é", "€", "𝄞"])
  report "ofList" (String.ofList ['x', 'é', '日', '𝄞'])
  report "singleton" (String.singleton '𝄞')
  report "reverse" (String.ofList mixed.toList.reverse)
  -- byte arrays: round trip, lossy decoding
  report "utf8" (String.fromUTF8! mixed.toUTF8)
  let shared2 := mixed
  report "utf8Shared" (String.fromUTF8! shared2.toUTF8)
  report "utf8Orig" shared2
  -- numbers
  for n in [0, 9, 127, 128, 1000, 18446744073709551615, 18446744073709551616] do
    report "nat" (toString n)
  report "int" (toString (-42 : Int))
  report "float" (toString (3.25 : Float))
  -- short (<= 16 bytes) and long strings
  report "short" "é€𝄞abcdefgh"
  let long := String.ofList (List.replicate 1000 'é') ++ String.ofList (List.replicate 37 'a')
  IO.println s!"long length {long.length} bytes {long.utf8ByteSize}"
  -- a buffer filled until it is long enough (quadratic if length scans)
  let mut out := ""
  let mut i := 0
  while out.length < 200000 do
    out := out ++ toString i ++ "é"
    i := i + 1
  IO.println s!"fill {i} {out.length} {out.utf8ByteSize}"
  -- file contents
  let path := "RtStrLen.tmp"
  IO.FS.writeFile path (mixed ++ "\n" ++ mixed)
  let back ← IO.FS.readFile path
  report "file" back
  let ls ← IO.FS.lines path
  for l in ls do report "line" l
  IO.FS.removeFile path
