/-! Runtime test (typed references, clean step B2, in a program that
creates tasks): typed references (a `Nat` counter, an array of records, a
string) updated by `modify` from several tasks and from `main`, read with
`get`, replaced with `swap` and `set`. In a program with tasks each
operation has its point (a polling point before a read, a publication
before a write, and the wait while another context's `modify` has taken
the reference: `refPoint`, generic over the reference's record type). The
results do not depend on the order in which the tasks run. -/

structure Pt where
  n : Nat
  s : String
  deriving Inhabited

def main : IO Unit := do
  let cnt ← IO.mkRef (0 : Nat)
  let log ← IO.mkRef (#[] : Array Pt)
  let txt ← IO.mkRef ""
  let tasks ← (List.range 6).mapM fun k => IO.asTask do
    for i in [0:200] do
      cnt.modify (· + 1)
      if i % 50 == 0 then
        log.modify (·.push { n := k, s := toString i })
        txt.modify (·.push 'x')
    return k
  for i in [0:100] do
    cnt.modify (· + 2)
    if i % 25 == 0 then discard <| cnt.get
  for t in tasks do
    match ← IO.wait t with
    | .ok _ => pure ()
    | .error e => IO.println s!"task error {e}"
  let entries ← log.get
  let sorted := (entries.map fun p => p.n * 1000 + p.s.toNat!).qsort (· < ·)
  IO.println s!"count {← cnt.get} entries {entries.size} {sorted} text {(← txt.get).length}"
  let old ← cnt.swap 5
  cnt.set (old + (← cnt.get))
  IO.println s!"after {← cnt.get} {← cnt.ptrEq cnt}"
