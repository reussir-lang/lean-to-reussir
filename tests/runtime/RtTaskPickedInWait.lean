import Std.Async
import Std.Net.Addr
/-! Runtime test (lean-runtime fixes-8, 83f7127): `main` waits for a pure
task that the lone emulated worker starts during `main`'s own wait, while
the event loop watches a descriptor.

`main` opens a listening TCP socket (nobody connects: the event loop
watches its descriptor, which never becomes ready), spawns a pure task
while the worker is idle, computes for about a millisecond with no effect
point (`IO.lazyPure`; the number it prints depends only on the code), and
then waits for the task (`Task.get`). By then the worker's wake-up latency
(90 µs) has passed, so the worker that the wait lets catch up first
(lean-runtime's `settle_worker` in `may_run_awaited`) takes the task. A
worker only marks a pure task started (`pick`), and the mark wakes the
task's waiters, before `main` has blocked on it. Before fixes-8 `main`
then blocked on the started task, and no wake-up came: the hub starts a
started pure task by itself only as its last resort, which a watched
descriptor prevents, so it waited in `epoll_wait` forever (`RtTcp` hung
about one run in 20 that way). Since fixes-8 the wait checks the mark
again and runs the task on `main`'s stack.

The socket is used after the wait (the last line): a value is freed right
after its last use, so a socket last used at `listen` would be closed
before the wait. Then nothing would be watched, the last resort would run
the task, and the old hang would not show. -/
open Std.Async
open Std.Net

def spin (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:n] do
    acc := (acc * 31 + i) % 1000003
  return acc

def main (args : List String) : IO Unit := do
  let s ← TCP.Socket.Server.mk
  s.bind (SocketAddressV4.mk (.ofParts 127 0 0 1) 0)
  s.listen 1
  -- `args.length` (0) keeps the compiler from computing these at compile time
  let t ← IO.lazyPure fun _ => Task.spawn fun _ => 6 * 7 + args.length
  let n ← IO.lazyPure fun _ => spin (300000 + args.length)
  let v ← IO.lazyPure fun _ => t.get
  IO.println s!"spin {n}, task {v}"
  -- `s` is still open here (its last use), so the loop watched it all along
  IO.println s!"still listening: {decide ((← s.getSockName).port > 0)}"
