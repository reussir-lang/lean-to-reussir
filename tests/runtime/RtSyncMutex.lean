import Std.Sync
/-! Runtime test: `Std.Sync`'s locks across tasks (each on a thread of its
own natively, `Task.Priority.dedicated`). `Mutex.atomically` from several
tasks; `tryLock`/`tryAtomically` while another task holds the lock and
sleeps (the task that waits for it goes on once it is released); a
`RecursiveMutex` taken twice by one thread; a `SharedMutex` read by two
tasks at once, then written. Every print comes from one task at a time, in
an order the locks and flags fix. -/
open Std

def countIt (m : Mutex Nat) (n : Nat) : IO Unit := do
  for _ in [0:n] do
    m.atomically (modify (· + 1))

def holdIt (m : Mutex Nat) (flag : IO.Ref Nat) : IO Unit := do
  m.atomically do
    flag.set 1
    modify (· + 1)
    while (← flag.get) == 1 do
      IO.sleep 1
    IO.println "holder: releases"

def tryIt (m : Mutex Nat) (flag : IO.Ref Nat) : IO Unit := do
  while (← flag.get) == 0 do
    IO.sleep 1
  let r ← m.tryAtomically (modify (· + 1))
  IO.println s!"try while held: {r.isSome}"
  flag.set 2
  m.atomically (modify (· + 10))
  IO.println "waiter: got the lock"
  let r ← m.tryAtomically (modify (· + 100))
  IO.println s!"try when free: {r.isSome}"

def main : IO Unit := do
  -- counting
  let m ← Mutex.new 0
  let ts ← (List.range 4).mapM fun _ => IO.asTask (prio := .dedicated) (countIt m 500)
  for t in ts do IO.ofExcept (← IO.wait t)
  IO.println s!"count {← m.atomically get}"
  -- tryAtomically while another task holds it
  let m2 ← Mutex.new 0
  let flag ← IO.mkRef 0
  let t1 ← IO.asTask (prio := .dedicated) (holdIt m2 flag)
  let t2 ← IO.asTask (prio := .dedicated) (tryIt m2 flag)
  IO.ofExcept (← IO.wait t1)
  IO.ofExcept (← IO.wait t2)
  IO.println s!"m2 {← m2.atomically get}"
  -- BaseMutex.tryLock on a mutex the same thread holds
  let b ← BaseMutex.new
  IO.println s!"tryLock {← b.tryLock} {← b.tryLock}"
  b.unlock
  IO.println s!"after unlock {← b.tryLock}"
  b.unlock
  -- RecursiveMutex
  let r ← RecursiveMutex.new (1 : Nat)
  r.atomically do
    r.atomically (modify (· * 5))
    modify (· + 2)
  IO.println s!"recursive {← r.atomically get}"
  let br ← BaseRecursiveMutex.new
  IO.println s!"rec tryLock {← br.tryLock} {← br.tryLock}"
  br.unlock; br.unlock
  -- SharedMutex: two readers at once, then a writer
  let s ← SharedMutex.new (10 : Nat)
  let inside ← IO.mkRef (0 : Nat)
  let reader : IO Nat := s.atomicallyRead do
    inside.modify (· + 1)
    while (← inside.get) < 2 do IO.sleep 1
    return (← read)
  let r1 ← IO.asTask (prio := .dedicated) reader
  let r2 ← IO.asTask (prio := .dedicated) reader
  IO.println s!"readers {← IO.ofExcept (← IO.wait r1)} {← IO.ofExcept (← IO.wait r2)} with 2 inside"
  s.atomically (modify (· * 3))
  IO.println s!"after write {← s.atomicallyRead (do return (← read))}"
  let bs ← BaseSharedMutex.new
  bs.read
  IO.println s!"tryWrite while read {← bs.tryWrite} tryRead {← bs.tryRead}"
  bs.unlockRead; bs.unlockRead
  IO.println s!"tryWrite when free {← bs.tryWrite} tryRead {← bs.tryRead}"
  bs.unlockWrite
