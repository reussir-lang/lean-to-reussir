/-! Runtime test: the `String.Internal.*` externs (implemented natively by
exported Lean definitions; the prelude has its own versions), called
directly on ASCII, multi-byte and whitespace-heavy strings. -/

def strs : List String :=
  ["", "a", "hello world", "  \t padded \n ", "héllo wörld", "日本語 テキスト", "x\ny\r\nz", " nbsp ", "   ", "abc😀def"]

def main (args : List String) : IO Unit := do
  let k := args.length
  for s in strs do
    IO.println s!"{repr s}"
    for n in [0, 1, 2, 5, 100 + k] do
      IO.println s!"  drop {n} {repr (String.Internal.drop s n)} dropRight {repr (String.Internal.dropRight s n)} pushn {repr (String.Internal.pushn s 'é' n)}"
    IO.println s!"  trim {repr (String.Internal.trim s)} capitalize {repr (String.Internal.capitalize s)} isEmpty {String.Internal.isEmpty s} front {repr (String.Internal.front s)}"
    IO.println s!"  posOf o {String.Internal.posOf s 'o'} posOf ö {String.Internal.posOf s 'ö'} contains l {String.Internal.contains s 'l'} any digit {String.Internal.any s Char.isDigit}"
    for p in [0, 1, 2, 3, 7, 100] do
      IO.println s!"  offsetOfPos {p} {String.Internal.offsetOfPos s ⟨p⟩} nextWhile {(String.Internal.nextWhile s Char.isAlpha ⟨p⟩).byteIdx}"
    for t in strs do
      IO.println s!"  isPrefixOf {repr t} {String.Internal.isPrefixOf t s}"
    IO.println s!"  foldl {String.Internal.foldl (fun acc c => acc.push (c.toUpper)) ">" s}"
