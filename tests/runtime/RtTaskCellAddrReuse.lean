/-! Runtime test: a task cell freed while its entry in the task glue lives
on, and new task cells made right then (the glue finds a task's entry
through a map from its cell's address, `leanrt::task::Tasks::by_cell`;
runtime bug hunt, 2026-10-21). Each IO task below is dropped at once (the
glue holds its cell), and its value holds the last reference to an
unresolved promise. When the task ends, its cell is freed inside the job
(the entry stays until the job returns), its value is freed, the promise is
resolved with `none` at the end of that free, and the promise's `sync`
dependent spawns new tasks then, whose cells may take the freed cell's
address: they must not find the old entry. The second half does the same
with pure tasks whose value holds the promise. The unit test
`task::tests::a_reused_address_finds_its_own_entry` checks the map alone. -/
def main (args : List String) : IO Unit := do
  let n := args.length
  let mut deps : Array (Task (List (Task Nat))) := #[]
  for r in [0:20] do
    let p ← IO.Promise.new (α := Nat)
    let dep := p.result?.map (sync := true) fun o =>
      (List.range 6).map fun i => Task.spawn fun _ => r * 100 + i * 10 + o.getD (7 + n)
    deps := deps.push dep
    let _ ← IO.asTask (do IO.sleep 1; pure p)
  let mut total := 0
  for d in deps do
    let ts := d.get
    for t in ts do
      total := total + t.get
  IO.println s!"total {total}"
  -- The same, with pure tasks whose value holds the promise, waited for.
  let mut deps2 : Array (Task (List (Task Nat))) := #[]
  let mut holders : Array (Task Nat) := #[]
  for r in [0:20] do
    let p ← IO.Promise.new (α := Nat)
    let dep := p.result?.map (sync := true) fun o =>
      (List.range 4).map fun i => Task.spawn fun _ => r + i + o.getD 3
    deps2 := deps2.push dep
    let carrier := Task.spawn fun _ => [p]
    holders := holders.push (carrier.map fun l => l.length)
  let mut t2 := 0
  for h in holders do t2 := t2 + h.get
  for d in deps2 do
    for t in d.get do
      t2 := t2 + t.get
  IO.println s!"total2 {t2}"
