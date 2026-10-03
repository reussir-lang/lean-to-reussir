/-! Runtime test: `Promise.result!` of a promise dropped unresolved, in a
task: natively that task's thread prints the panic and blocks forever; the
rest of the program goes on (`main` prints and exits). -/

@[noinline] def orphan : BaseIO (Task Nat) := do
  let p : IO.Promise Nat ← IO.Promise.new
  return p.result!

def main : IO Unit := do
  let _t ← IO.asTask (prio := .dedicated) do
    let r ← orphan
    return r.get
  IO.sleep 100
  IO.println "main still runs"
  (← IO.getStdout).flush
  IO.Process.exit 0
