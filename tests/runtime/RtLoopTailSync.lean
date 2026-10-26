import Std.Sync.Mutex
import Std.Sync.RecursiveMutex
import Std.Sync.SharedMutex
/-! Runtime test (leanrt hunt after D8, H3): `for` loops whose body takes and
releases `Std` locks and notifies a condition variable stay loops. The
prelude's `l2r_sync_op` and `l2r_condvar_wait_h` passed the addresses of
locals to leanrt functions that are not inlined; inlined into the loop's
function, the escaping stack slots kept the loop's self tail call a real
call, and long loops overflowed the stack where native Lean runs in 8 MB.
The textures now call by-value wrappers (`sync::owned`). Every operation of
`l2r_sync_op` is used in a loop; `Condvar.wait` is in a loop but does not run
(its predicate holds). Runs 2*10^5 steps on a 1 MiB stack (`.pipe`). -/
open Std

def main (args : List String) : IO Unit := do
  let n := (args.headD "10").toNat!
  let m ← Mutex.new (0 : Nat)
  for k in [0:n] do
    m.atomically (modify fun s => (s + k) % 1000003)
  IO.println s!"Mutex: {← m.atomically get}"
  let bm ← BaseMutex.new
  let c ← Condvar.new
  let mut tries := 0
  for k in [0:n] do
    if ← bm.tryLock then
      tries := tries + 1
      c.notifyOne
      c.waitUntil bm (pure (k < n))
      bm.unlock
    bm.lock
    c.notifyAll
    bm.unlock
  IO.println s!"BaseMutex and Condvar: {tries}"
  let r ← RecursiveMutex.new (0 : Nat)
  for k in [0:n] do
    r.atomically (modify fun s => (s + 2 * k) % 1000003)
  IO.println s!"RecursiveMutex: {← r.atomically get}"
  let br ← BaseRecursiveMutex.new
  let mut rtries := 0
  for _ in [0:n] do
    if ← br.tryLock then
      rtries := rtries + 1
      br.unlock
  IO.println s!"BaseRecursiveMutex: {rtries}"
  let s ← SharedMutex.new (0 : Nat)
  let mut reads := 0
  for k in [0:n] do
    s.atomically (modify fun v => (v + 3 * k) % 1000003)
    reads := (reads + (← s.atomicallyRead (do return (← read) % 10))) % 1000003
  IO.println s!"SharedMutex: {← s.atomicallyRead read} {reads}"
  let bs ← BaseSharedMutex.new
  let mut stries := 0
  for _ in [0:n] do
    if ← bs.tryWrite then
      stries := stries + 1
      bs.unlockWrite
    if ← bs.tryRead then
      stries := stries + 1
      bs.unlockRead
  IO.println s!"BaseSharedMutex: {stries}"
