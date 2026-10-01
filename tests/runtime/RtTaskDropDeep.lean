/-! Runtime test (with one native worker thread, `NAME.pipe`): pure tasks
the program drops before they start are deleted, however long the chain
or wide the tree of dropped dependents that hold them (natively, dropping
the last reference to a dependent releases its source, and so on). A pure
task that a kept task holds still runs. -/
def work (tag : String) (n : Nat) : Nat := dbgTrace s!"{tag} runs" fun _ => n + 1

def main (args : List String) : IO Unit := do
  let n := args.length
  let blocker ← IO.asTask (do IO.sleep 100; IO.println "blocker"; return 1)
  IO.sleep 20
  -- a chain of 200 maps over a spawned task, all dropped
  let mut c : Task Nat := Task.spawn fun _ => work "chain source" n
  for i in [0:200] do
    c := c.map fun x => work s!"chain {i}" x
  let r ← IO.mkRef c
  r.set (Task.pure 0)
  -- a tree: 3 levels of 4 maps each, dropped
  let root : Task Nat := blocker.map fun x => work "tree root" (x.toOption.getD 0)
  let level1 := (List.range 4).map fun i => root.map fun x => work s!"tree {i}" x
  let level2 := level1.flatMap fun t => (List.range 4).map fun j => t.map fun x => work s!"leaf {j}" x
  let r2 ← IO.mkRef (some level2)
  r2.set none
  -- a chain of 100 maps whose end is kept: it runs
  let mut k : Task Nat := Task.spawn fun _ => n + 1
  for _ in [0:100] do
    k := k.map (· + 1)
  let _ ← IO.wait blocker
  IO.println s!"kept chain: {k.get}"
