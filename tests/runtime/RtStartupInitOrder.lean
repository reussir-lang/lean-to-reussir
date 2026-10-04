prelude
import StartupInitOrderDep
import Init.Data.Random

/-! Runtime test: Lean's library initializers run at their module's place in
the import walk, as natively (EmitC `emitInitFn`: a module's imports first,
in import order, each module once), not before the program's. This
`prelude` program imports its companion `StartupInitOrderDep`
(`RtStartupInitOrder.deps`) before `Init.Data.Random`, so the companion's
initializer, which takes every descriptor, runs before `IO.stdGenRef`, which
then cannot open `/dev/urandom`: the program stops with an uncaught
exception (exit 1). `RtStartupInitOrder.pipe` runs it under `ulimit -n 64`.
lean2rr ran the library's initializers first (review RSG-01). -/

def main : IO Unit := IO.println "main ran"
