/-! Runtime test: `String.Pos.Raw.extract` (`lean_string_utf8_extract`) at
positions >= 2^63, which are big `Nat`s, with the inputs from the
command line (RtStringExtractBig.args: the string, then start/end pairs),
so nothing is folded at compile time. Since Lean 4.34 a big position counts
as SIZE_MAX: a big start gives "", a big end extracts to the end. Lean 4.33
returned the string itself (without a reference: a use after free). The
first two pairs are the lean-runtime oracle's LR1-01 rows
(`"a€😀é"` at ⟨2^64⟩ ⟨0⟩ and ⟨1⟩ ⟨2^63⟩: native 4.34 gives "" and "€😀é").
`String.extract` (`lean_string_utf8_extract_fast`, valid positions) is
checked at every valid position pair of the same string. -/

def main (args : List String) : IO Unit := do
  let s := args.headD ""
  let rec pairs : List String → List (Nat × Nat)
    | b :: e :: rest => (b.toNat!, e.toNat!) :: pairs rest
    | _ => []
  for (b, e) in pairs (args.drop 1) do
    IO.println s!"Pos.Raw.extract {repr s} ⟨{b}⟩ ⟨{e}⟩ = {repr (String.Pos.Raw.extract s ⟨b⟩ ⟨e⟩)}"
  -- every pair of valid positions, through `String.extract`
  let mut ps : List s.Pos := []
  let mut p := s.startPos
  ps := [p]
  while h : p ≠ s.endPos do
    p := p.next h
    ps := ps ++ [p]
  for b in ps do
    for e in ps do
      IO.println s!"extract {b.offset.byteIdx} {e.offset.byteIdx} = {repr (s.extract b e)}"
