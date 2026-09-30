/-! Runtime test: `String`/`Char` externs: UTF-8 byte positions (valid,
inside a character, past the end, huge), `get`/`next`/`prev`/`extract`/
`set`, comparisons, hashing, conversions, and the library functions built on
them (`splitOn`, `trim`, `replace`, case mapping, `toNat?`, `quote`). -/

def strs (k : Nat) : List String :=
  ["", "a", "abc", "héllo", "日本語テキスト", "𝔸𝔹ℂ emoji 😀!", "a\u0000b", "  padded \t\n", "line1\nline2\r\nline3",
   "ÀÉÎÕÜ àéîõü ß", "x".pushn 'y' k, "Ωmega", "\"quoted\" \\ back"]

def rawPos (i : Nat) : String.Pos.Raw := ⟨i⟩

def main (args : List String) : IO Unit := do
  let k := args.length + 3
  for s in strs k do
    IO.println s!"{repr s}: length {s.length} bytes {s.utf8ByteSize} hash {hash s} isEmpty {s.isEmpty}"
    let n := s.utf8ByteSize
    for i in [0, 1, 2, 3, 4, 5, 7, n - 1, n, n + 1, 9223372036854775807, 9223372036854775808, 18446744073709551615, 18446744073709551616] do
      let p := rawPos i
      IO.println s!"  pos {i}: get {repr (p.get s)} get? {repr (p.get? s)} next {(p.next s).byteIdx} prev {(p.prev s).byteIdx} valid {p.isValid s} atEnd {p.atEnd s} byte {if h : i < n then s.getUTF8Byte (rawPos i) h else 0}"
      -- Native `lean_string_utf8_extract` returns its borrowed argument
      -- without a reference for positions >= 2^63 (a use-after-free), so
      -- those are not tested.
      if i < 9223372036854775808 then
        for j in [0, 2, 4, n, n + 3] do
          IO.println s!"    extract {i} {j}: {repr ((rawPos i).extract s (rawPos j))}"
      IO.println s!"    set {repr ((rawPos i).set s 'Z')} set2 {repr ((rawPos i).set s 'é')} modify {repr ((rawPos i).modify s Char.toUpper)}"
    IO.println s!"  toList {s.toList} ofList {String.ofList s.toList == s} data {s.toList.length}"
    IO.println s!"  upper {s.toUpper} lower {s.toLower} capitalize {s.capitalize} decapitalize {s.decapitalize}"
    IO.println s!"  trim {repr s.trimAscii.copy} trimLeft {repr s.trimAsciiStart.copy} trimRight {repr s.trimAsciiEnd.copy}"
    IO.println s!"  drop2 {repr (s.drop 2).copy} take2 {repr (s.take 2).copy} dropEnd2 {repr (s.dropEnd 2).copy} takeEnd2 {repr (s.takeEnd 2).copy}"
    IO.println s!"  splitOn space {s.splitOn " "} splitOn l {s.splitOn "l"} split e {(s.split 'e').toList.map (·.copy)}"
    IO.println s!"  contains o {s.contains 'o'} any digit {s.any Char.isDigit} all alpha {s.all Char.isAlpha} startsWith ab {s.startsWith "ab"} endsWith 3 {s.endsWith "3"}"
    IO.println s!"  replace l L {s.replace "l" "L"} replace empty {s.replace "" "-"} quote {s.quote} reverse {String.ofList s.toList.reverse}"
    IO.println s!"  push {s.push 'é'} append {s ++ "∀" ++ s} front {repr s.front} back {repr s.back} pushn {s.pushn '*' 3}"
    IO.println s!"  toNat? {s.toNat?} toInt? {s.toInt?} isNat {s.isNat} utf8 {s.toUTF8.size} {s.toUTF8.toList.take 6} fromUTF8 {String.fromUTF8? s.toUTF8}"
    IO.println s!"  foldl {s.foldl (fun n c => n + c.toNat) 0} map {s.map Char.toUpper} intercalate {", ".intercalate [s, s]} join {String.join [s, "|", s]}"
    IO.println s!"  offset {(s.toList.length)} find {(s.find ' ').offset.byteIdx} posOf {(s.toRawSubstring.posOf 'l').byteIdx} revPosOf {repr (s.revFind? 'l' |>.map (·.offset.byteIdx))}"
    for t in strs k do
      IO.println s!"  vs {repr t}: == {s == t} < {decide (s < t)} compare {repr (compare s t)} isPrefixOf {s.isPrefixOf t}"
  for n in ["0", "123", "-45", "+7", "12a", "", "18446744073709551616", "007", "1_000"] do
    IO.println s!"parse {repr n}: {n.toNat?} {n.toInt?} {n.toNat!} {n.isInt}"
  for c in ['a', 'Z', '0', ' ', '\n', 'é', 'ß', '日', '😀', '\x00', '\x7f'] do
    IO.println s!"char {repr c} {c.toNat} isAlpha {c.isAlpha} isDigit {c.isDigit} isAlphanum {c.isAlphanum} isWhitespace {c.isWhitespace} isUpper {c.isUpper} isLower {c.isLower} toUpper {c.toUpper} toLower {c.toLower} utf8Size {c.utf8Size} quote {c.quote}"
  IO.println s!"Char.ofNat {repr (Char.ofNat 55296)} {repr (Char.ofNat 1114112)} {repr (Char.ofNat 65)} {repr (Char.ofNat 128512)}"
  let big := (List.range 2000).foldl (fun acc i => acc ++ toString i) ""
  IO.println s!"big {big.length} {hash big} {big.take 30 |>.copy} {(big.drop 5000).copy.length}"
  let lines := "a,b,,c\nd,e\n\nf".splitOn "\n" |>.map (·.splitOn ",")
  IO.println s!"csv {lines}"
  IO.println s!"String.mk {String.ofList ['x', 'é', '日']} {"abc" ++ "def" |>.length}"
  IO.println s!"singleton {String.singleton 'q'} {"".front} {"".back}"
