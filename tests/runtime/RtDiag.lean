/-! Runtime test: `dbgTraceIfShared` reports shared heap objects only
(nullary constructors are scalars) on stderr. -/

def main (args : List String) : IO Unit := do
  let xs := (List.range (args.length + 3)).toArray
  let ys := xs
  let n := (dbgTraceIfShared "shared array" xs).size + ys.size
  IO.println s!"n {n}"
  let o : Option Nat := if args.length > 5 then some 1 else none
  IO.println s!"none {(dbgTraceIfShared "opt none" o).isSome}"
  let l : List Nat := if args.length > 5 then [1] else []
  IO.println s!"nil {(dbgTraceIfShared "list nil" l).length}"
  let s := String.ofList (List.replicate (args.length + 3) 'z')
  IO.println s!"unique {(dbgTraceIfShared "unique string" (s.push 'q')).length}"
