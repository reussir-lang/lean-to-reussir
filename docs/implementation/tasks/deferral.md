# When a task runs

Paths: `lean2rr/LeanToReussir/` for lean2rr's files, `runtime/` for the
runtime. Plan [§5.14](../../translation-plan.md#514-thunks-and-tasks)
("Tasks").

### Tasks are deferred once `main` has started

- **What:** Every task created after `main` has started, IO or pure, is
  deferred: its cell is `pending` and `leanrt::task` queues it, holding a
  reference while it is pending. It runs at the first of: `IO.wait` or
  `Task.get` of it (on the stack of whoever needs it), the running code
  blocking with a worker free, an effect point with a worker free for a
  while, a program polling for it, or `main` returning. During module
  initialization, and with `LEAN_NUM_THREADS=0`, tasks run at once.
- **Why:** A task may wait for `main` (`while !(← flag.get) do IO.sleep 1`):
  run at creation, it spun forever; its output came before `main`'s next
  line; pure tasks the program drops were computed (03bbbfd; a pure task
  forcing a pending IO task too early hung programs, 787b48c; every task
  deferred, adv4 TK4-01, 5ec3ab9). Natively there is no task manager during
  initialization (`lean_task_spawn_core` runs the computation at once).
- **Where:** `Lower/LazyGlue.lean`: `taskNewFn`, `newTask`, `taskKind`;
  `runtime/leanrt/src/task.rs`: `register`, `deferring`, `start`;
  `runtime/prelude.rr`: `l2r_task_register`, `l2r_task_deferring`.
- **Remove only if:** the runtime gets real threads.

### Dropped pure tasks are deleted, not run

- **What:** The runtime's own reference does not count: when the runtime
  is about to start a pure task (`Task.spawn`, `map`, `bind`) and holds the
  only reference, or the only other references come from pure dependents
  that are dropped themselves (to any depth), the task is handed to the
  generated code to be dropped instead. The search through the tree of
  dependents is iterative and remembers tasks that keep a tree alive
  (pins).
- **Why:** Lean keeps an IO task alive until it has run (`keep_alive`) but
  deletes a pure one the program drops before a worker started it (adv4
  TK4-01, 5ec3ab9; to any depth, 97acbd0). Without pins a long chain was
  searched once per task, quadratically (7edc0f5).
- **Where:** `runtime/leanrt/src/task.rs`: `dropped`, `droppable_now`,
  `droppable_in`, `deletable`, `set_pin`, `pinned`, `dropped_by_now`,
  `deleting`; `Lower/Promises.lean`: `taskDispatchFns`.
- **Remove only if:** never.

### Priorities are taken modulo 2^32, as an `unsigned`

- **What:** A priority is `lean_usize_of_nat(prio)` modulo 2^32. 2^32-1
  (`LEAN_SYNC_PRIO`) runs at once on the enqueuing thread (a dependent as
  soon as its source finishes); 0 to 8 are the task manager's queues; above
  8 is a dedicated thread, which starts first here.
- **Why:** Lean passes `lean_unbox(prio)` as an `unsigned` (adv4 TK4-03,
  5ec3ab9).
- **Where:** `Lower/LazyGlue.lean`: `prioOf`; `runtime/leanrt/src/task.rs`:
  `priority`, `register`, `run_here`.
- **Remove only if:** never.

### The final run follows Lean's task manager, timed like a native worker

- **What:** When `main` returns, queued tasks run in the order Lean's task
  manager starts them: one queue per priority, the first task of the
  highest non-empty queue. An idle worker picks its task once it is awake,
  about 90 µs after the enqueue that woke it (a new thread) or 20 µs (an
  idle one), so tasks queued back to back compete by priority while one
  queued earlier has already started; when a worker's task finishes it
  picks the next at once.
- **Why:** Measured natively with `LEAN_NUM_THREADS=1`; replaces "the
  first task registered" (adv3 P3-4, 946a9d0; adv4 TK4-04, 5ec3ab9).
- **Where:** `runtime/leanrt/src/task.rs`: `LATENCY_COLD`, `LATENCY_WARM`,
  `pick`, `next_tag`, `shutdown`; `Lower/Promises.lean`:
  `taskDispatchFns` (`l2r_run_pending_tasks`).
- **Remove only if:** the runtime gets real threads.

### A needed task runs its chain of sources from the deepest end

- **What:** A task needed while the tasks it waits for are pending runs
  that chain from its deepest end, one task after the other
  (`l2r_task_force_sources`). A pending task that waits for one running on
  another context waits until that one has finished, then looks again.
- **Why:** A 4·10^6-long `mapTask` chain forced by `main` recursed (adv3,
  946a9d0). Running the dependent at once would have it wait inside its own
  computation, with the wrong state, cancellation and `sync` thread
  (7edc0f5).
- **Where:** `runtime/leanrt/src/task.rs`: `source_next`,
  `source_elsewhere`; `Lower/Promises.lean`: `taskDispatchFns`.
- **Remove only if:** never.

### Polling a pending task reports it waiting until time has passed

- **What:** `IO.getTaskState`/`IO.hasFinished` report a pending task
  `waiting` until the program asks again after a sleep since the first
  answer, or keeps asking (1000 times); then it runs and is reported
  `finished`. A task that cannot finish without others (it waits for an
  unresolved promise or for a task on another context) does not run: the
  others go on once per question (`sched::poll_yield`).
- **Why:** Two quick checks before `main` released a task ran it
  (787b48c). Blocking until the polled task finished hung when another
  context slept periodically (6f14a9e). A deferred task reported `waiting`
  at the first question even after a sleep is kept and documented (adv2
  K2, f9e06af).
- **Where:** `runtime/leanrt/src/task.rs`: `query`, `status`;
  `runtime/leanrt/src/sched.rs`: `poll_yield`; `Lower/LazyGlue.lean`:
  `taskStateFn`.
- **Remove only if:** the runtime gets real threads.

### `IO.waitAny` runs the first pending task, or waits for progress

- **What:** `IO.waitAny` returns the value of the first finished task of
  its list; if none has finished, the first pending one that can run (not
  waiting for an unresolved promise or for a task on another context) runs
  (it finished first); if none can, the caller waits until some task
  finishes and looks again.
- **Why:** Waiting forever at once hung programs that finish natively
  (5ec3ab9, f87ea08).
- **Where:** `Lower/LazyGlue.lean`: `taskWaitAnyFn`;
  `runtime/leanrt/src/task.rs`: `wait_status`, `wait_progress`.
- **Remove only if:** never.

### `IO.checkCanceled` at shutdown

- **What:** After `main` returns, a task that was queued then sees Lean's
  shutdown flag only once time has passed in it (a sleep) or from its
  second check on (so does a task it creates or releases before time
  passes); any other task of the final run sees it at once.
- **Why:** A native worker could have started such a task before the flag
  was set; a fire-and-forget task that checks first still does its work
  (787b48c; adv4 TK4-07, 5ec3ab9).
- **Where:** `runtime/leanrt/src/task.rs`: `check_canceled`,
  `early_now` (the `EARLY` flag), `shutdown`.
- **Remove only if:** the runtime gets real threads.

### Cancellation reaches dependents; `getTID` inside a task

- **What:** `IO.cancel` sets the flag of an unfinished task; when a
  canceled task finishes, the tasks created while it was unfinished that
  depend on it are canceled too. `IO.getTID` inside a task is `main`'s
  thread id plus the running task's worker number (a `sync` dependent's is
  its source's).
- **Why:** As Lean's `handle_finished` (787b48c); a worker thread's id
  differs from `main`'s (adv3 P3-5, 946a9d0).
- **Where:** `runtime/leanrt/src/task.rs`: `cancel`, `tid_offset`.
- **Remove only if:** never.

### The number of workers is read as Lean reads it

- **What:** `LEAN_NUM_THREADS` is read as glibc's `atoi` (`strtol`
  saturating at a `long`, then the low 32 bits) taken as an `unsigned`; 0
  or not a number is no task manager. Unset, it is the number of online
  processors, not limited by the CPU affinity mask or a cgroup quota.
- **Why:** As native Lean (`lean_init_task_manager_using`) and
  `std::thread::hardware_concurrency` (7edc0f5, 6f14a9e; round 6,
  1362da1).
- **Where:** `runtime/leanrt/src/sched.rs`: `pool_limit`,
  `hardware_concurrency`; `runtime/leanrt/src/task.rs`: `start`.
- **Remove only if:** never.
