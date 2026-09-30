/-! Runtime test: externs whose signatures mention Lean-defined types, which
lean2rr implements with generated glue around runtime primitives:
`String.compare` (Ordering), `String.toList` (List Char), `String.get?`
(Option Char), `Float.frExp` (Float × Int), `String.intercalate`. -/

def main (args : List String) : IO Unit := do
  let k := args.length
  let ws := ["b", "a", "ab", "", "é", "abc", "b"]
  IO.println s!"compare {ws.map fun w => repr (compare w "ab")} sorted {ws.mergeSort (fun a b => compare a b != .gt)}"
  IO.println s!"toList {"héllo日".toList} {"".toList} {("x".pushn 'y' k).toList}"
  IO.println s!"get? {repr ("héllo".get? ⟨1⟩)} {repr ("héllo".get? ⟨2⟩)} {repr ("héllo".get? ⟨20⟩)}"
  IO.println s!"frExp {(12.5 : Float).frExp} {(0.0 : Float).frExp} {(1.0/0.0 : Float).frExp} {(-3e-310 : Float).frExp} {(6.0 : Float32).frExp}"
  IO.println s!"intercalate {", ".intercalate ["a", "b", "c"]} {"".intercalate []} {"-".intercalate ["x"]}"
