/-! Runtime test: `getHardwareConcurrency` and the number of task-manager
workers are `std::thread::hardware_concurrency()`, the number of online
processors, which the CPU affinity mask does not limit
(`RtHardwareConcurrency.pipe` runs the program under `taskset -c 0`). With
more than one worker, four tasks that sleep 300 ms all start before the
first one ends. -/

def main : IO Unit := do
  IO.println s!"hardware concurrency {System.Platform.Internal.getHardwareConcurrency ()}"
  let log ← IO.mkRef (#[] : Array String)
  let ts ← (List.range 4).mapM fun _ => IO.asTask do
    log.modify (·.push "start")
    IO.sleep 300
    log.modify (·.push "end")
  for t in ts do discard <| IO.wait t
  IO.println s!"{← log.get}"
