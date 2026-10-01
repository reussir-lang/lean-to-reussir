/-! Runtime test: polling and `IO.waitAny` for tasks that cannot finish
without others: a pending dependent of a task blocked on a promise `main`
resolves later (it is waiting, and `waitAny` takes another task); a task
polled with sleeps while a ticker task sleeps periodically; a running task
asked about with sleeps between questions while another task prints later;
two running tasks asked about in a busy loop. -/
def pr (s : String) : IO Unit := do IO.println s; (← IO.getStdout).flush

def eStr {α} [ToString α] : Except IO.Error α → String
  | .ok v => s!"ok {v}"
  | .error e => s!"error {e}"

def main : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let a ← IO.asTask (do return (← IO.wait p.result!) + 1)
  IO.sleep 10
  let d ← IO.mapTask (fun r => return (match r with | .ok v => v * 2 | .error _ => 0)) a
  let f1 ← IO.hasFinished d
  IO.sleep 1
  let f2 ← IO.hasFinished d
  IO.sleep 1
  let f3 ← IO.hasFinished d
  pr s!"dependent polled: {f1} {f2} {f3}"
  let o ← IO.asTask (do IO.sleep 20; return (7 : Nat))
  let r ← IO.waitAny [d, o]
  pr s!"waitAny: {eStr r}"
  p.resolve 1
  pr s!"d = {eStr (← IO.wait d)}"
  -- a ticker sleeps periodically meanwhile
  let stop ← IO.mkRef false
  let ticker ← IO.asTask (do while !(← stop.get) do IO.sleep 2)
  let q ← IO.Promise.new (α := Nat)
  let t ← IO.asTask (do return (← IO.wait q.result!) + 1)
  let mut n := 0
  while !(← IO.hasFinished t) && n < 5 do
    IO.sleep 10
    n := n + 1
  pr s!"after polling: finished={← IO.hasFinished t} n={n}"
  q.resolve 1
  stop.set true
  pr s!"t = {eStr (← IO.wait t)}"
  let _ ← IO.wait ticker
  -- questions at 5-7 ms about a task that sleeps 80 ms
  let t ← IO.asTask (do IO.sleep 80; return (1 : Nat))
  let u ← IO.asTask (do IO.sleep 40; pr "U at 40")
  IO.sleep 5
  let a ← IO.hasFinished t
  IO.sleep 1
  let b ← IO.hasFinished t
  IO.sleep 1
  let c ← IO.hasFinished t
  pr s!"main at 7: {a} {b} {c}"
  let _ ← IO.wait t
  let _ ← IO.wait u
  -- two running tasks in a busy loop
  let t1 ← IO.asTask (do IO.sleep 20; return (1 : Nat))
  let t2 ← IO.asTask (do IO.sleep 30; return (2 : Nat))
  IO.sleep 5
  let mut k := 0
  repeat
    let a ← IO.hasFinished t1
    let b ← IO.hasFinished t2
    if a && b then break
    k := k + 1
  pr s!"both finished after polling: {decide (k > 0)}"
