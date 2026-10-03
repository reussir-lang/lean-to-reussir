/-! Runtime test: a stack overflow in a task that runs on one of more than
4096 contexts alive at once (dedicated tasks that sleep, so all are alive)
prints `Stack overflow detected. Aborting.` and aborts (exit 134), as in
a native worker thread: the first task or the last one overflows
(`RtStackOverflowContexts.pipe`). -/

def deep : Nat → Nat
  | 0 => 7
  | n+1 => let r := deep n; (r * 3 + n) % 1000003

def main (args : List String) : IO Unit := do
  let n := (args.headD "4100").toNat!
  let which := (args.getD 1 "last")
  let ts ← (List.range n).mapM fun i => IO.asTask (prio := .dedicated) do
    IO.sleep 300
    let pick := if which == "last" then i == n - 1 else i == 1
    if pick then return deep 1000000000 else return i
  let mut s := 0
  for t in ts do
    match ← IO.wait t with
    | .ok v => s := s + v
    | .error e => IO.println s!"err {e}"
  IO.println s!"done {s}"
