import Std.Sync
/-! Runtime test: `Std.Channel` and `Std.CloseableChannel` between tasks
(threads of their own natively), unbounded, bounded and unbuffered: a
producer that blocks while the buffer is full (or until a receiver takes
the value) goes on once the consumer receives; `close` wakes a blocked
receiver; `trySend`/`tryRecv`; the asynchronous API (`send`/`recv` as
tasks, `forAsync`). Values are printed by one consumer, in order. -/
open Std

def produce (ch : CloseableChannel.Sync Nat) (n : Nat) : IO Unit := do
  for i in [0:n] do
    ch.send i
  ch.close

def consume (ch : CloseableChannel.Sync Nat) : IO (Array Nat) := do
  let mut acc := #[]
  for v in ch do
    acc := acc.push v
  return acc

def run (cap : Option Nat) : IO Unit := do
  let ch ← CloseableChannel.new (α := Nat) cap
  let p ← IO.asTask (prio := .dedicated) (produce ch.sync 20)
  let c ← IO.asTask (prio := .dedicated) (consume ch.sync)
  let vs ← IO.ofExcept (← IO.wait c)
  IO.ofExcept (← IO.wait p)
  IO.println s!"capacity {cap}: {vs.size} values, in order {vs == (Array.range 20)}"

def main : IO Unit := do
  for cap in [none, some 0, some 1, some 4] do
    run cap
  -- the consumer is main, the producer blocks on a full buffer
  let ch ← Channel.new (α := String) (some 1)
  let t ← IO.asTask (prio := .dedicated) do
    for w in ["a", "b", "c", "d"] do
      ch.sync.send w
  for _ in [0:4] do
    IO.println s!"received {← ch.sync.recv}"
  IO.ofExcept (← IO.wait t)
  -- trySend / tryRecv
  let ch2 ← CloseableChannel.new (α := Nat) (some 2)
  IO.println s!"trySend {← ch2.trySend 1} {← ch2.trySend 2} {← ch2.trySend 3}"
  IO.println s!"tryRecv {← ch2.tryRecv} {← ch2.tryRecv} {← ch2.tryRecv}"
  -- close wakes a blocked receiver
  let ch3 ← CloseableChannel.new (α := Nat)
  let r ← IO.asTask (prio := .dedicated) ch3.sync.recv
  IO.sleep 20
  discard <| EIO.toBaseIO ch3.close
  IO.println s!"after close: {← IO.ofExcept (← IO.wait r)}"
  IO.println s!"send on closed: {(← EIO.toBaseIO (ch3.sync.send 1)) matches .error .closed}"
  -- the asynchronous API
  let ch4 ← CloseableChannel.new (α := Nat) (some 0)
  let rt ← ch4.recv
  let st ← ch4.send 42
  IO.println s!"async recv {← IO.wait rt}, send ok {(← IO.wait st) matches .ok ()}"
  let out ← IO.mkRef #[]
  let done ← ch4.forAsync fun x => out.modify (·.push x)
  for i in [0:3] do
    discard <| IO.wait (← ch4.send (i * 10))
  discard <| EIO.toBaseIO ch4.close
  IO.wait done
  IO.println s!"forAsync {← out.get}"
