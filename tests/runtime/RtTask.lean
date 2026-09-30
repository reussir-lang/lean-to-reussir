/-! Runtime test: IO tasks (`IO.asTask`, `mapTask`, `bindTask`, `waitAny`,
`getTaskState`/`hasFinished`, `cancel`/`checkCanceled`, `mapTasks`) are
deferred until needed (a task body that races with `main` sleeps first, so
the native output is deterministic): `main` goes on before the task runs,
a task can wait for `main`, polling `hasFinished` terminates, `sync :=
true` on a finished task runs at once, and a task never waited for runs
before the process exits, with `IO.checkCanceled` true. Pure tasks inside
and around them. -/

@[noinline] def hn (x : Nat) : Nat := x

def val (r : Except IO.Error Nat) : String :=
  match r with
  | .ok v => toString v
  | .error e => s!"error {e}"

def main (args : List String) : IO Unit := do
  let n := args.length
  -- A task runs after main's next actions (it sleeps first natively).
  let t1 ← IO.asTask (do IO.sleep 100; IO.println "t1 body"; return hn (n + 1))
  IO.println "main after spawn"
  IO.println s!"t1 = {val (← IO.wait t1)}"
  IO.println s!"t1 again = {val (← IO.wait t1)}"
  -- A task waiting for main.
  let flag ← IO.mkRef false
  let t2 ← IO.asTask (do
    while !(← flag.get) do IO.sleep 1
    IO.println "t2 saw flag"
    return 2)
  IO.sleep 20
  IO.println "main sets flag"
  flag.set true
  IO.println s!"t2 = {val (← IO.wait t2)}"
  -- hasFinished before and after.
  let t3 ← IO.asTask (do IO.sleep 100; return 3)
  IO.println s!"t3 finished early {← IO.hasFinished t3}"
  IO.println s!"t3 = {val (← IO.wait t3)}"
  IO.println s!"t3 finished after wait {← IO.hasFinished t3} {← IO.getTaskState t3}"
  -- Polling until finished terminates.
  let t4 ← IO.asTask (do IO.sleep 30; IO.println "t4 body"; return 4)
  while !(← IO.hasFinished t4) do
    IO.sleep 5
  IO.println "t4 polled to completion"
  -- Exceptions stay in the task.
  let t5 ← IO.asTask (do IO.sleep 10; throw (IO.userError "t5 failed") : IO Nat)
  IO.println s!"t5 = {val (← IO.wait t5)}"
  -- mapTask/bindTask with sync on a finished task run at once.
  let t6 ← IO.mapTask (sync := true) (fun r => do IO.println "t6 body (sync)"; return r.toOption.getD 0 + 60) t1
  IO.println "after t6 creation"
  IO.println s!"t6 = {val (← IO.wait t6)}"
  let t7 ← IO.bindTask (sync := true) t1 (fun r => do
    IO.println "t7 body (sync)"
    IO.asTask (do IO.sleep 10; IO.println "t7 inner"; return r.toOption.getD 0 + 70))
  IO.println "after t7 creation"
  IO.println s!"t7 = {val (← IO.wait t7)}"
  -- Not sync: deferred (the body sleeps first natively).
  let t8 ← IO.mapTask (fun r => do IO.sleep 50; IO.println "t8 body"; return r.toOption.getD 0 + 80) t1
  IO.println "after t8 creation"
  IO.println s!"t8 = {val (← IO.wait t8)}"
  -- A chain: mapTask over a pending task.
  let t9 ← IO.asTask (do IO.sleep 20; IO.println "t9 body"; return 9)
  let t10 ← IO.mapTask (fun r => do IO.println "t10 body"; return r.toOption.getD 0 * 10) t9
  IO.println s!"t10 = {val (← IO.wait t10)}"
  -- Cancellation.
  let t11 ← IO.asTask (do IO.sleep 50; return (if ← IO.checkCanceled then 1 else 0))
  IO.cancel t11
  IO.println s!"t11 canceled = {val (← IO.wait t11)}"
  let t12 ← IO.asTask (do return (if ← IO.checkCanceled then 1 else 0))
  IO.println s!"t12 canceled = {val (← IO.wait t12)}"
  IO.println s!"main canceled = {← IO.checkCanceled}"
  -- waitAny: a finished task wins.
  let slow ← IO.asTask (do IO.sleep 200; return 100)
  let r ← IO.waitAny [slow, Task.pure (.ok 5)]
  IO.println s!"waitAny = {val r}"
  -- Pure tasks inside IO tasks, IO.wait on pure tasks.
  let p := Task.spawn fun _ => hn 21
  let q := p.map (· * 2)
  let b := p.bind fun x => Task.spawn fun _ => x + 1
  IO.println s!"pure {p.get} {q.get} {b.get} {← IO.wait q} {← IO.getTaskState b}"
  let t13 ← IO.asTask (do IO.sleep 10; return (Task.spawn fun _ => hn 13).get)
  IO.println s!"t13 = {val (← IO.wait t13)}"
  -- BaseIO-level tasks (no Except).
  let bt ← BaseIO.asTask (do IO.sleep 10; return hn 77)
  IO.println s!"bt = {← IO.wait bt}"
  let bm ← BaseIO.mapTask (fun x => return x + 1) bt
  IO.println s!"bm = {← IO.wait bm}"
  -- IO.mapTasks.
  let ms ← IO.mapTasks (fun xs => do IO.println "mapTasks body"; return xs.foldl (· + ·) 0) [q, p]
  IO.println s!"mapTasks = {val (← IO.wait ms)}"
  -- Never awaited: runs before the process exits, sees the shutdown.
  let _ ← IO.asTask (do IO.sleep 100; IO.println s!"late task canceled {← IO.checkCanceled}")
  IO.println "main done"
