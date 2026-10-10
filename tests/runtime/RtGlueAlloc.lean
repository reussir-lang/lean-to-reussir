/-! Runtime test (hunt HSTR2-01): the glue of `String.toList`,
`String.Pos.Raw.get?` and `Float.frExp`/`Float32.frExp` allocates what
native Lean allocates. lean2rr passed curried constructor closures to
generic prelude helpers: `toList` made about 3 allocations per character
(natively 1, the cons cell), `get?` made 1 at every call (natively 0), and
`frExp` built its pair through a closure.
- `list N`: 20 times `toList` of an N-character string (every 5th
  character `é`, two bytes; a different last character each time).
- `getq N`: 20 passes of `get?` at every byte of that string (the second
  byte of each `é` gives `none`).
- `frexp N`: `Float.frExp` and `Float32.frExp` of N values.
- no mode: the three at N = 100, and their results on a few edge cases.
tests/runtime/alloc-check.sh compares the allocations at two sizes
(RtGlueAlloc.alloc). -/
def strOf (n : Nat) : String :=
  String.ofList ((List.range n).map fun i => if i % 5 == 0 then 'é' else 'a')

def runList (n : Nat) : IO Unit := do
  let s := strOf n
  let mut total := 0
  for k in [0:20] do
    let l := (s.push (Char.ofNat (98 + k))).toList
    total := total + l.length + (l.getLast?.map Char.toNat).getD 0
  IO.println s!"list {n}: {total}"

def runGetq (n : Nat) : IO Unit := do
  let s := strOf n
  let mut total := 0
  let mut nones := 0
  for _ in [0:20] do
    for i in [0:s.utf8ByteSize] do
      match (String.Pos.Raw.mk i).get? s with
      | some c => total := total + c.toNat % 3
      | none => nones := nones + 1
  IO.println s!"getq {n}: {total} {nones}"

def runFrexp (n : Nat) : IO Unit := do
  let mut acc : Float := 0
  let mut accE : Int := 0
  let mut acc32 : Float32 := 0
  let mut accE32 : Int := 0
  for i in [0:n] do
    let x := (i.toFloat + 0.5) * 1.7
    let (m, e) := x.frExp
    acc := acc + m
    accE := accE + e
    let (m32, e32) := (x.toFloat32 / 3).frExp
    acc32 := acc32 + m32
    accE32 := accE32 + e32
  IO.println s!"frexp {n}: {acc} {accE} {acc32} {accE32}"

def main (args : List String) : IO Unit := do
  let n := (args[1]? >>= String.toNat?).getD 100
  match args.head? with
  | some "list" => runList n
  | some "getq" => runGetq n
  | some "frexp" => runFrexp n
  | _ =>
    runList n; runGetq n; runFrexp n
    for s in ["", "a", "é", "héllo €𝔸!", "\x00z"] do
      let p := (List.range (s.utf8ByteSize + 2)).map fun i => (String.Pos.Raw.mk i).get? s
      IO.println s!"{repr s}: {s.toList} {s.toList.length} {p}"
    let fs : List Float := [0.0, -0.0, 1.0, -0.75, 12.5, 1.0 / 0.0, -1.0 / 0.0, 0.0 / 0.0, 5e-324, 1.7976931348623157e308]
    IO.println s!"{fs.map Float.frExp}"
    IO.println s!"{fs.map fun x => x.toFloat32.frExp}"
