/-! Runtime test: case `A866` of the shared dependent-type corpus (programs
built by another translator's team and checked against native Lean). It
checks: An `initialize` whose Ref holds a capturing closure. -/
structure Hook where
  name : String
  run : Nat → Nat

instance : Inhabited Hook := ⟨⟨"", id⟩⟩

initialize fnB : IO.Ref (String → String) ← do
  let e ← IO.getEnv "T_MODE"
  IO.mkRef (if e.isSome then (fun s => s ++ "!" ++ e.getD "") else (fun s => "<" ++ s ++ ">" ++ e.getD "-"))
initialize fnA : IO.Ref (Nat → Nat) ← IO.mkRef (fun x => x * 2 + 1)
initialize hook : IO.Ref Hook ← do
  let k := (← IO.getEnv "T_MODE").map String.length |>.getD 0
  IO.mkRef ⟨"h", fun x => x + k⟩
initialize fns : IO.Ref (List (Nat → Nat)) ← do
  let k := (← IO.getEnv "T_MODE").map String.length |>.getD 7
  IO.mkRef [(· + k), (· * k), fun x => x]

def main (args : List String) : IO Unit := do
  let n := args.length
  let s := String.join args
  let g ← fnB.get
  let g2 ← fnB.get
  let f ← fnA.get
  let h ← hook.get
  let fs ← fns.get
  IO.println s!"{g s} {g2 "x"} {f n} {h.name} {h.run n} {fs.map (· n)}"
  fnB.set (fun t => t ++ "?")
  IO.println s!"{(← fnB.get) s}"
