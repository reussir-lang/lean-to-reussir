/-
lean2rr classic corpus: `strings` (written for this corpus).

String building (`push`, `++`, interpolation, `intercalate`), `toString` of
`Nat`/`Int`/`Float`, `splitOn`, `toNat?`/`toInt?`, UTF-8 multi-byte
characters, `length` (characters) versus `utf8ByteSize` (bytes), `Char`
operations, slices and positions, and the runtime string hash.

Size argument n (default 1000000): the number of records built into one big
string, which is then split and parsed back. The fixed edge cases printed
after the summary lines do not depend on n.
-/

def words : Array String :=
  #["alpha", "βήτα", "gamma", "中文字", "naïve", "😀ok", "Ωmega", "é", "tab\there", "plain"]

/-- One record: `index|word|negated multiple|float|` -/
def record (i : Nat) : String :=
  let w := words[i % words.size]!
  let f : Float := (i.toFloat) / 8.0
  s!"{i}|{w}|{-(i : Int) * 7}|{f}|"

/-- Build all records with explicit pushes and appends into one string. -/
def buildAll (n : Nat) : String := Id.run do
  let mut s := ""
  for i in [0:n] do
    s := s ++ record i
    s := s.push '\n'
  return s

structure Stats where
  lines : Nat := 0
  natSum : Nat := 0
  intSum : Int := 0
  wordHits : Nat := 0
  floatHits : Nat := 0
  bad : Nat := 0
  chars : Nat := 0
  bytes : Nat := 0
deriving Repr

def parseAll (s : String) : Stats := Id.run do
  let mut st : Stats := {}
  for line in s.splitOn "\n" do
    if line.isEmpty then continue
    let fields := line.splitOn "|"
    match fields with
    | [a, w, b, f, ""] =>
      match a.toNat?, b.toInt? with
      | some i, some k =>
        st := { st with lines := st.lines + 1, natSum := st.natSum + i, intSum := st.intSum + k,
                        chars := st.chars + line.length, bytes := st.bytes + line.utf8ByteSize }
        if w == words[i % words.size]! then st := { st with wordHits := st.wordHits + 1 }
        if f == toString ((i.toFloat) / 8.0) then st := { st with floatHits := st.floatHits + 1 }
      | _, _ => st := { st with bad := st.bad + 1 }
    | _ => st := { st with bad := st.bad + 1 }
  return st

/-- ASCII rot13 by `Char` arithmetic; everything else unchanged. -/
def rot13 (c : Char) : Char :=
  if 'a' ≤ c && c ≤ 'z' then Char.ofNat ((c.toNat - 'a'.toNat + 13) % 26 + 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'Z' then Char.ofNat ((c.toNat - 'A'.toNat + 13) % 26 + 'A'.toNat)
  else c

structure CharStats where
  digits : Nat := 0
  alpha : Nat := 0
  space : Nat := 0
  upper : Nat := 0
  nonAscii : Nat := 0
  codeSum : Nat := 0
  utf8Sum : Nat := 0

def charStats (s : String) : CharStats :=
  s.foldl (init := {}) fun st c =>
    { digits := st.digits + (if c.isDigit then 1 else 0)
      alpha := st.alpha + (if c.isAlpha then 1 else 0)
      space := st.space + (if c.isWhitespace then 1 else 0)
      upper := st.upper + (if c.isUpper then 1 else 0)
      nonAscii := st.nonAscii + (if c.toNat ≥ 128 then 1 else 0)
      codeSum := st.codeSum + c.toNat
      utf8Sum := st.utf8Sum + c.utf8Size }

/-- Byte offsets of every character, walking with `String.Pos`. -/
def offsets (s : String) : List Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut p := s.startPos
  for _ in [0:s.utf8ByteSize + 1] do
    match p.next? with
    | some q =>
      out := out.push p.offset.byteIdx
      p := q
    | none => break
  return out.toList

def showOpt {α : Type} [ToString α] : Option α → String
  | some a => s!"some {a}"
  | none => "none"

def main (args : List String) : IO UInt32 := do
  let n := (args.head?.bind String.toNat?).getD 1000000

  -- Build, measure, split and parse back.
  let big := buildAll n
  let st := parseAll big
  IO.println s!"built: length={big.length} bytes={big.utf8ByteSize} hash={big.hash}"
  IO.println s!"parsed: lines={st.lines} natSum={st.natSum} intSum={st.intSum} words={st.wordHits} floats={st.floatHits} bad={st.bad} chars={st.chars} bytes={st.bytes}"
  let cs := charStats big
  IO.println s!"chars: digits={cs.digits} alpha={cs.alpha} space={cs.space} upper={cs.upper} nonAscii={cs.nonAscii} codeSum={cs.codeSum} utf8Sum={cs.utf8Sum}"
  -- `String.map` rewrites a non-ASCII character by copying the whole string
  -- (Lean's `lean_string_utf8_set`), so the multi-byte text is kept small and
  -- the size-dependent text is ASCII.
  let sample := buildAll (min n 300)
  let up := sample.toUpper
  let rot := sample.map rot13
  let back := rot.map rot13
  let ascii := String.join ((List.range (n / 4)).map fun i => s!"The Quick Brown Fox {i}; ")
  let asciiRot := ascii.map rot13
  IO.println s!"maps: upperHash={up.hash} rotHash={rot.hash} rot13 twice {if back == sample then "ok" else "FAIL"} lowerEq {if up.toLower == sample.toLower then "ok" else "FAIL"} ascii={ascii.length} rot={asciiRot.hash} upper={ascii.toUpper.hash} lower={ascii.toLower.hash} rot13 twice {if asciiRot.map rot13 == ascii then "ok" else "FAIL"}"
  let joined := ",".intercalate ((List.range (n / 10)).map toString)
  let parts := joined.splitOn ","
  let total := parts.foldl (fun acc p => acc + p.toNat?.getD 0) 0
  IO.println s!"join/split: parts={parts.length} sum={total} length={joined.length}"

  -- Fixed edge cases.
  let u := "héllo wörld 中文 😀"
  IO.println s!"utf8: length={u.length} bytes={u.utf8ByteSize} sizes={u.toList.map Char.utf8Size} offsets={offsets u} codes={u.toList.map Char.toNat}"
  IO.println s!"slices: take3={(u.take 3).toString} drop6={(u.drop 6).toString} takeEnd1={(u.takeEnd 1).toString} dropEnd2={(u.dropEnd 2).toString} front={u.front} back={u.back} starts={u.startsWith "hé"} ends={u.endsWith "😀"} replace={u.replace "ö" "oe"} contains={u.contains '中'}"
  IO.println s!"case: {u.toUpper} {"ÀB-cd".toLower} {"hello".capitalize} {'é'.toUpper} {'z'.toUpper} {'Q'.toLower} {'é'.isAlpha} {'7'.isDigit} {' '.isWhitespace} {"  pad me \t".trimAscii.toString}|"
  IO.println s!"bytes: {u.toUTF8.toList} roundtrip={showOpt (String.fromUTF8? u.toUTF8)} invalid={showOpt (String.fromUTF8? (ByteArray.mk #[0xff, 0x41]))} encode={String.utf8EncodeChar '😀'}"
  IO.println s!"chars: {Char.ofNat 0x41} {(Char.ofNat 0xD800).toNat} {(Char.ofNat 0x110000).toNat} {(Char.ofNat 0x1F600).toNat} {('a'.toNat + 1)} {String.singleton 'x' |>.pushn '!' 3} {"a\"b\n\tc".quote} {'\n'.quote}"
  IO.println s!"toNat?: {showOpt "".toNat?} {showOpt "007".toNat?} {showOpt "1_000".toNat?} {showOpt "12a".toNat?} {showOpt "18446744073709551616".toNat?} {showOpt " 5".toNat?} {showOpt "٣".toNat?} toInt?: {showOpt "-0".toInt?} {showOpt "+5".toInt?} {showOpt "-12".toInt?} {showOpt "--1".toInt?} {showOpt "-99999999999999999999".toInt?}"
  IO.println s!"splitOn: {repr ("a,b,,c".splitOn ",")} {repr ("a--b".splitOn "--")} {repr ("abc".splitOn "")} {repr ("".splitOn ",")} {repr ("aaa".splitOn "aa")} {repr ("x é y".splitOn " ")} {repr ("中a中b".splitOn "中")} {repr ("no-sep".splitOn "|")} {repr ("ab".splitOn "abc")}"
  IO.println s!"nat/int: {(0 : Nat)} {(2^64 : Nat)} {(-(2^63) : Int)} {(-7 : Int)} {(12345678901234567890123 : Nat)} {toString (-(10^30) : Int)}"
  let fs : List Float := [0.1 + 0.2, 1e100, 1.0 / 0.0, -1.0 / 0.0, 0.0 / 0.0, -0.0, 1e-7, 2.5, 123456789.125, 1e21, Float.sqrt 2.0, Float.ofScientific 12345 true 2, (2^70 : Nat).toFloat, -1.5e-3]
  IO.println s!"float: {fs}"
  let fs2 : List Float := [Float.floor 2.5, Float.ceil 2.5, Float.round 2.5, Float.round (-2.5), Float.exp 1.0, Float.log 10.0, Float.sin 1.0, Float.pow 2.0 0.5]
  IO.println s!"float ops: {fs2} {(3.99 : Float).toUInt64} {(-3.99 : Float).toUInt64} {(1e30 : Float).toUInt64} {decide ((2.5 : Float) < 3.0)} {(0.0 / 0.0 : Float) == (0.0 / 0.0 : Float)}"
  IO.println s!"compare: {decide ("abc" < "abd")} {decide ("ab" < "abc")} {decide ("é" < "z")} {"abc" == "ab" ++ "c"} {repr (compare "b" "abc")} {"interp {braces}"} {s!"{1}{2}{"x"}"}"
  pure 0
