/-! Runtime test: the character count of substrings (`String.Pos.Raw.extract`,
`String.extract`, `splitOn`): every byte range of ASCII strings (whose
ranges have as many characters as bytes) and of strings with 2-, 3- and
4-byte characters, short and long, the source still used after the
extraction or not. The strings come from the command line
(RtStringExtractCount.args), so nothing is folded at compile time. -/

def main (args : List String) : IO Unit := do
  for t in args do
    let n := t.utf8ByteSize
    let mut lens : List Nat := []
    for b in [0:n + 1] do
      for e in [b:n + 2] do
        lens := (String.Pos.Raw.extract t ⟨b⟩ ⟨e⟩).length :: lens
    IO.println s!"{repr t} length {t.length} bytes {n}: raw extract lengths {lens.reverse}"
    let mut ps : List t.Pos := [t.startPos]
    let mut p := t.startPos
    while h : p ≠ t.endPos do
      p := p.next h
      ps := ps ++ [p]
    let mut vlens : List Nat := []
    for b in ps do
      for e in ps do
        vlens := (t.extract b e).length :: vlens
    IO.println s!"  extract lengths {vlens.reverse}"
    IO.println s!"  splitOn: {(t.splitOn "-").map String.length} {(t.splitOn "€").map String.length} {((t ++ t).splitOn "a").map String.length}"
