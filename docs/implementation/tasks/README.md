# Tasks and the scheduler

Native Lean runs tasks on a thread pool; lean2rr's runtime runs everything
on one thread and picks one of the schedules native Lean can produce: a
task runs when it is needed, when the running code blocks, at an effect
point once a worker would have started it, when the program polls for it,
or when `main` returns. Plan [§5.14](../../translation-plan.md#514-thunks-and-tasks) has
the rules; [`runtime/README.md`](../../../runtime/README.md) ("Thunks and
tasks", "The scheduler") the primitives.

- [cells.md](cells.md): thunks, tasks and promises as runtime cells of a
  generated state type.
- [deferral.md](deferral.md): when a task runs, dropped pure tasks,
  priorities, the final run, cancellation at shutdown.
- [dependents.md](dependents.md): `sync` dependents, bind tasks, and the
  walks of dependents of promises dropped inside a free.
- [scheduler.md](scheduler.md): contexts, the order of the scheduler,
  effect points, polling, the event loop, the stack guard, per-task
  streams.

What a single thread cannot reproduce is listed in plan
[§10](../../translation-plan.md#10-known-divergences-and-unsupported-features)
("Tasks").
