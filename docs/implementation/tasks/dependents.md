# Dependents: who runs when a task finishes

Paths: `lean2rr/LeanToReussir/` for lean2rr's files, `runtime/` for the
runtime. Plan [§5.14](../../translation-plan.md#514-thunks-and-tasks)
("Dependents", "Promises", and the end of "Blocking").

### `sync` dependents run on the finishing thread, before any waiter

- **What:** A task that waits for another (`mapTask`, `bindTask`,
  `Task.map`, `Task.bind`) is off the queue until that task finishes.
  Then, whoever finished it, its dependents are walked newest first: one
  created with `sync := true` (or at priority 2^32-1) runs there and then,
  with that thread's current streams, before anything waiting for the
  finished task resumes; the others are enqueued at their priority. A
  `sync` dependent's own dependents are walked by the same loop, so a long
  chain does not recurse. `sync := true` on a finished task applies `f` at
  once in the calling thread.
- **Why:** As Lean's `handle_finished` and `lean_task_map_core` (adv3
  P3-2, 946a9d0; adv4 TK4-05, 5ec3ab9).
- **Where:** `runtime/leanrt/src/task.rs`: `end`, `walk_next`, `depend`;
  `Lower/LazyGlue.lean`: `taskDepend`; `Lower/LazyForce.lean`:
  `lazyGetFn` (`l2r_task_walk_if`); `Lower/Promises.lean`:
  `taskDispatchFns` (`l2r_task_walk`).
- **Remove only if:** never.

### A bind task waits for the task it continues as

- **What:** A bind task (`IO.bindTask`, `Task.bind`) that has run `f`
  finishes at once if the task `f` returned has finished; otherwise it
  waits for it, keeping its priority and `sync` flag, reported `waiting`,
  and finishes as that one. Dependents of a cycle are left behind.
- **Why:** As Lean's `task_bind_fn1`; native workers stop when the queue is
  empty (f9e06af; adv4 TK4-06, 5ec3ab9).
- **Where:** `Lower/LazyForce.lean`: `taskBindStepFn`;
  `Lower/LazyGlue.lean`: `taskStepFn`; `runtime/leanrt/src/task.rs`:
  `bind_wait`.
- **Remove only if:** never.

### No context is ever suspended inside a free

- **What:** A free's pending work is the thread's (`reussir_rt::drop`,
  patch 0014), so a context switch inside a free is an internal panic
  (`switch_to`); nothing that may block runs there. A promise whose last reference goes inside a free (held by an
  array, list, map, structure or `Option` being freed) is resolved with
  `none` in its turn, but its dependents, which run Lean code that may
  block, are kept for later.
- **Why:** The other contexts would push their frees onto the suspended
  one's (2d21a0a: one free stack shared with Reussir's glue).
- **Where:** `runtime/leanrt/src/sched.rs`: `switch_to`;
  `runtime/leanrt/src/task.rs`: `resolve`, `Promise` (`Drop`).
- **Remove only if:** never.

### Dependents of a promise dropped inside a free run when the free is over

- **What:** The kept walks run as soon as the free is over: when a free
  one of the runtime's containers started ends (`drop::run`), and, for a
  free Reussir's record glue started, through `__reussir_drop_drained`, a
  hook every outermost drain that released something calls when it ends
  (local Reussir patch 0040, applied to `l2r-local` since 2026-10-03;
  `task::resolve` stores `task::drained` there). The symbol is linked
  weakly: without the patch, those walks run at the context's next effect
  point, block, `Std.Sync` wait or question about a task. The `Std.Sync`
  waiting primitives and `once::claim` run pending walks before looking at
  their object, and a wait that registers in `sched::block` returns at
  once when walks ran (its caller looks again).
- **Why:** Natively the dependents run at once, on the dropping thread:
  code in between saw the old state, and their output escaped
  `IO.FS.withIsolatedStreams` (round 7 RV7C-01). A walk run after a
  `Std.Sync` caller had put the context in the object's waiter list woke
  the running context (a no-op) and it waited forever (RV7C-02; d5169c4;
  tests `RtPromiseFreeSync`, `RtSyncLostWake`). A reference's `set` frees
  the old value inside a free the runtime starts, so its walks run when
  that free ends, with or without 0040 (round 8 RV8T-01, 8af8f1a; test
  `RtPromiseFreeGlue`, see
  [../ownership.md](../ownership.md#reference-sets-store-the-new-value-before-releasing-the-old-one)).
- **Where:** `runtime/leanrt/src/task.rs`: `resolve`, `run_later_walks`,
  `hook_drained`; `runtime/leanrt/src/drop.rs`: `run`;
  `runtime/leanrt/src/sync.rs`: `settle`; `runtime/leanrt/src/once.rs`:
  `claim`; `runtime/leanrt/src/sched.rs`: `block`, `effect`;
  `Lower/Promises.lean`: `taskDispatchFns` (`l2r_task_walk_c`).
- **Remove only if:** never; the fallback (next effect point) stays as
  long as Reussir builds without patch 0040 are supported. Remaining
  difference: the
  dependents see the rest of the container released too (plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Promises released inside a free").
