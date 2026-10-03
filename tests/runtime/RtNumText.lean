/-! Runtime test: numbers and characters as text. CStr: `String.toNat?`,
`toInt?`, `isNat`, `isInt`, `toNat!` on 35 inputs ("", "_", "1_000", "+5",
"-0", "--5", 2^64, -2^63-1, fullwidth and Arabic digits, 1000 digits; the
`toNat!`/`toInt!` panics), `Nat.toDigits` in bases 0..100, sub/superscripts,
`repr`/`reprArg`/`reprPrec` of negative `Int`s inside `some`/lists,
`digitChar`. CChar: `Char.ofNat` of 39 code points (surrogates, 0x10FFFF,
0x110000, 2^32+65, 2^64+65, 2^100) through `toNat`, `repr`, `quote`,
`utf8Size`, the classifiers, `toUpper`/`toLower`, strings; escapes, `hash`.
From the round-6 adversarial reviewers, area numbers (adv6/numbers), checks
CStr and CChar. -/

namespace CStr
-- from adv6/numbers/CStr.lean
-- Number <-> string: toNat?, toInt?, toDigits, repr, sub/superscripts.
@[noinline] def bs (s : String) : String := s
@[noinline] def bn (n : Nat) : Nat := n
@[noinline] def bi (n : Int) : Int := n

def inputs : List String :=
  ["", "0", "00", "007", "1_000", "_1", "1_", "1__0", "+5", "-0", "-", "+", "-5", "--5", "+-5", " 5", "5 ", "5a", "a5",
   "18446744073709551615", "18446744073709551616", "9223372036854775807", "9223372036854775808", "-9223372036854775808",
   "-9223372036854775809", "123456789012345678901234567890123456789012345678901234567890", "٣", "１２", "0x10", "1e5", "1.0",
   "99999999999999999999", "-18446744073709551616", "4294967296", "-2147483649"]

def main : IO Unit := do
  for s in inputs do
    let s := bs s
    IO.println s!"{repr s}: toNat? {s.toNat?} toInt? {s.toInt?} isNat {s.isNat} isInt {s.isInt} toNat! {if s.isNat then toString s.toNat! else "-"}"
  let huge := String.ofList (List.replicate 1000 '9')
  IO.println s!"huge {(huge.toNat?.map (· + 1)).map (fun n => (toString n).length)} {(("-" ++ huge).toInt?.map (· - 1)).map (fun n => (toString n).length)}"
  for b in [2, 8, 10, 16, 36, 37, 64, 100, 0] do
    IO.println s!"toDigits {b}: {Nat.toDigits b (bn 0)} {Nat.toDigits b (bn 255)} {String.ofList (Nat.toDigits b (bn (2^64 + 1)))}"
  for n in [0, 1, 9, 10, 127, 128, 255, 256, 2^63, 2^64, 10^30] do
    let n := bn n
    IO.println s!"n {n}: repr {repr n} toString {toString n} sub {n.toSubscriptString} sup {n.toSuperscriptString} toDigits {String.ofList (Nat.toDigits 10 n)} hex {String.ofList (Nat.toDigits 16 n)} len {(toString n).length}"
  for i in [0, -1, -127, -128, -129, 127, 128, -(2^63), -(2^64), 2^63, -(10^30)] do
    let i := bi i
    IO.println s!"i {i}: repr {repr i} reprArg {reprArg i} reprPrec {reprPrec i 0} {reprPrec i 1024} opt {repr (some i)} list {repr [i]} toString {toString i}"
  IO.println s!"digitChar {(List.range 40).map Nat.digitChar |> String.ofList}"
  -- panics
  IO.println s!"bang {(bs "abc").toNat!} {(bs "-x").toInt!}"
  IO.println s!"fmt {(bn 5).toDigits 2 |> String.ofList} {(bn 42).toSuperDigits} {(bn 42).toSubDigits}"
end CStr

namespace CChar
-- from adv6/numbers/CChar.lean
-- Char: invalid code points, classification, conversions, escapes.
@[noinline] def bn (n : Nat) : Nat := n
@[noinline] def b32 (n : UInt32) : UInt32 := n

def main : IO Unit := do
  for n in [0, 9, 10, 13, 31, 32, 39, 34, 92, 65, 90, 97, 122, 127, 128, 159, 160, 255, 256, 0x3bb, 0x7ff, 0x800, 0xd7ff, 0xd800, 0xdbff, 0xdc00, 0xdfff, 0xe000, 0xfffd, 0xfffe, 0xffff, 0x10000, 0x10ffff, 0x110000, 0x7fffffff, 2^32, 2^32 + 65, 2^64 + 65, 2^100] do
    let c := Char.ofNat (bn n)
    IO.println s!"{n}: toNat {c.toNat} val {c.val} repr {repr c} quote {c.quote} utf8Size {c.utf8Size} alpha {c.isAlpha} digit {c.isDigit} alnum {c.isAlphanum} upper {c.isUpper} lower {c.isLower} ws {c.isWhitespace} toUpper {c.toUpper.toNat} toLower {c.toLower.toNat} str {(toString c).length} {(toString c).utf8ByteSize} {(String.singleton c).toList.map Char.toNat} u8 {c.toUInt8} isValid {decide (Nat.isValidChar n)}"
  for u in [0, 65, 0xd800, 0x10ffff, 0x110000, 0xffffffff] do
    let u := b32 u
    IO.println s!"ofUInt32 {u}: {(if h : u.isValidChar then Char.mk u h else 'X').toNat} {decide u.isValidChar}"
  let s := String.ofList ((List.range 20).map (fun i => Char.ofNat (bn (i * 0x1111))))
  IO.println s!"s {s.length} {s.utf8ByteSize} {s.toList.map Char.toNat} {repr s}"
  IO.println s!"escapes {repr "\x00\x01\t\n\r\"\\\x7f\u0080é€😀"} {"a\u0000b".length} {repr '\x7f'} {repr ' '} {repr '😀'}"
  IO.println s!"cmp {decide ('a' < 'b')} {decide ('😀' < 'é')} {'a' == 'a'} {repr (compare 'z' 'A')} {('a'.toNat + 1)}"
  IO.println s!"digits {['0', '9', 'a', 'z', 'A', 'Z', '٣'].map (·.isDigit)} {"0123456789".toList.map (fun c => c.toNat - '0'.toNat)}"
  let chars : Array Char := #['a', Char.ofNat 0xd800, '😀', Char.ofNat (bn 0x10ffff)]
  IO.println s!"arr {chars.map Char.toNat} {chars.map Char.isAlpha} {String.ofList chars.toList |>.length}"
  IO.println s!"ofNat edges {(Char.ofNat (bn 0xd800)) == (Char.ofNat 0)} {Char.ofNat (bn 0x10ffff) == Char.ofNat 0x10ffff}"
  IO.println s!"toUpper unicode {'é'.toUpper} {'ß'.toUpper} {'É'.toLower}"
  IO.println s!"hash {hash 'a'} {hash '😀'}"
end CChar

def main : IO Unit := do
  IO.println "=== CStr"
  CStr.main
  IO.println "=== CChar"
  CChar.main
