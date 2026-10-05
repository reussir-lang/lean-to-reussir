# Tasks and the scheduler

Native Lean runs tasks on a thread pool. lean2rr runs everything on one
thread with the shared crate lean-runtime's task scheduler
(`lean_runtime::sched`, its features `sched` and `stack-overflow`):
Lean's task manager on one thread, with contexts that block and resume,
which picks one of the schedules native Lean can produce (lean-runtime's
`docs/sched.md`). Every rule of when a task runs, of its dependents, waits,
polling, cancellation, promises, `Std.Sync`, the event loop and the exit is
lean-runtime's; lean2rr keeps the glue: its task objects (cells of a
generated state), the generated code's primitives mapped onto
lean-runtime's API, and the duties lean-runtime lists for a translator's
glue. Plan [§5.14](../../translation-plan.md#514-thunks-and-tasks) has the
rules; [`runtime/README.md`](../../../runtime/README.md) ("Thunks and
tasks", "The scheduler") the primitives.

- [cells.md](cells.md): thunks, tasks and promises as runtime cells of a
  generated state, and how a cell names its task in lean-runtime.
- [deferral.md](deferral.md): the generated code's task primitives on
  lean-runtime's scheduler: creation, dependents, runs, waits, polling,
  `IO.waitAny`, dropped tasks, the final run.
- [dependents.md](dependents.md): `sync` dependents, bind tasks, and the
  promises dropped inside a free.
- [scheduler.md](scheduler.md): the glue lean-runtime asks for (the
  suspend step, the per-context streams, polling points, references in a
  program that creates tasks, the no-suspend scope), the scheduler's start
  at the first task, the event loop with its timers and signals, the
  stack-overflow report, `Std.Sync`.

What a single thread cannot reproduce is listed in plan
[§10](../../translation-plan.md#10-known-divergences-and-unsupported-features)
("Tasks").
